import Uniq.IR

namespace IR.CG
  structure CGNode where
    name    : Const
    func    : Function
    callees : Array Const
    callers : Array Const
    deriving Inhabited

  partial def computeCallees (body : FnBody) : List Const :=
    match body with
    | .ret .. => []
    | .«let» _ expr rest =>
      let callees := match expr with
        | .app c _ => [c]
        | _ => [] -- papp is not considered, but that's okay because we only use this
                  -- for escape analysis where papp doesn't play a role
      callees ++ computeCallees rest
    | .case _ cases => cases.data.map computeCallees |>.join
    | .case' _ cases => cases.data.map (fun ⟨_, _, body⟩ => computeCallees body) |>.join

  def computeCallGraph (p : Program) : Lean.RBMap Const CGNode compare := Id.run do
    let mut r := Lean.mkRBMap _ _ _
    for ⟨c, func⟩ in p do
      r := r.insert c ⟨c, func, (computeCallees func.body).toArray, #[]⟩
    for ⟨c, cgNode⟩ in r.toList do
      for callee in cgNode.callees do
        let calleeCGNode := r.find! callee
        r := r.erase callee -- deduplicate the reference to `calleeCGNode` so that pushing the new caller is efficient
        r := r.insert callee { calleeCGNode with callers := calleeCGNode.callers.push c }
    return r
end IR.CG

structure IR.SCC where
  component : Array IR.CG.CGNode
  callees   : Array Const
  callers   : Array Const
  deriving Inhabited

namespace IR.SCC
  open IR.CG

  partial def computeSCCs (cg : Lean.RBMap Const CGNode compare) : Lean.RBMap Const SCC compare :=
    let rec visit (cgNode : CGNode) : StateM (Lean.RBTree Const compare × List CGNode) Unit := do
      let (visited, postorder) ← get
      if visited.contains cgNode.name then
        return
      let visited := visited.insert cgNode.name
      set (visited, postorder)
      for callee in cgNode.callees do
        visit (cg.find! callee)
      set (visited, cgNode :: postorder)
    let visitAll : StateM (Lean.RBTree Const compare × List CGNode) Unit := do
      for ⟨_, cgNode⟩ in cg do
        visit cgNode
    let ⟨_, ⟨_, postorder⟩⟩ := StateT.run visitAll ⟨Lean.mkRBTree _ _, []⟩
    let rec assign (cgNode root : CGNode) : StateM (Lean.RBTree Const compare × Lean.RBMap Const SCC compare) Unit := do
      let (assigned, sccs) ← get
      if assigned.contains cgNode.name then
        return
      let assigned := assigned.insert cgNode.name
      let scc := sccs.findD root.name ⟨#[], #[], #[]⟩ -- we'll fill callers and callees in later
      let sccs := sccs.erase root.name -- deduplicate ref
      let component := scc.component.push cgNode
      let sccs := sccs.insert root.name ⟨component, #[], #[]⟩
      set (assigned, sccs)
      for caller in cgNode.callers do
        assign (cg.find! caller) root
    let assignAll : StateM (Lean.RBTree Const compare × Lean.RBMap Const SCC compare) Unit := do
      for cgNode in postorder do
        assign cgNode cgNode
    let ⟨_, ⟨_, sccs⟩⟩ := StateT.run assignAll ⟨Lean.mkRBTree _ _, Lean.mkRBMap _ _ _⟩
    let inverseIndex : Lean.RBMap Const Const compare := Id.run do
      let mut inverseIndex := Lean.mkRBMap _ _ _
      for ⟨root, scc⟩ in sccs do
        for cgNode in scc.component do
          inverseIndex := inverseIndex.insert cgNode.name root
      return inverseIndex
    let sccs : Lean.RBMap Const SCC compare := Id.run do
      let mut sccs := sccs
      for ⟨root, scc⟩ in sccs.toList do
        let mut calleeIndex : Lean.RBTree Const compare := Lean.mkRBTree _ _
        let mut callerIndex : Lean.RBTree Const compare := Lean.mkRBTree _ _
        for cgNode in scc.component do
          for callee in cgNode.callees do
            let calleeRoot := inverseIndex.find! callee
            if calleeRoot != root then
              calleeIndex := calleeIndex.insert calleeRoot
          for caller in cgNode.callers do
            let callerRoot := inverseIndex.find! caller
            if callerRoot != root then
              callerIndex := callerIndex.insert callerRoot
        sccs := sccs.insert root { scc with callees := calleeIndex.toArray, callers := callerIndex.toArray }
      return sccs
    sccs

  def computeRoots (sccs : Lean.RBMap Const SCC compare) : Array Const :=
    sccs.toList.filter (·.2.callers.isEmpty) |>.map (·.1) |>.toArray

  partial def sccsInReverseTopologicalSort (sccs : Lean.RBMap Const SCC compare) : Array (Const × SCC) :=
    let rec loop (node : Const) : StateM (Lean.RBTree Const compare × List (Const × SCC)) Unit := do
      let (done, acc) ← get
      if done.contains node then
        return
      for callee in (sccs.find! node).callees do
        loop callee
      let done := done.insert node
      let acc := (node, sccs.find! node) :: acc
      set (done, acc)
      return
    let loopRoots : StateM (Lean.RBTree Const compare × List (Const × SCC)) Unit := do
      for root in computeRoots sccs do
        loop root
    let ⟨_, ⟨_, sorted⟩⟩ := StateT.run loopRoots ⟨Lean.mkRBTree _ _, []⟩
    sorted.toArray.reverse
end IR.SCC