import Uniq.SCC

namespace IR.EscapeAnalysis
  structure Escapee where
    var   : Var
    field : List (Ctor × Proj)
    deriving BEq

  def Escapee.prepend (y : Escapee) (ctor : Ctor) (proj : Proj) : Escapee :=
    { y with field := (ctor, proj) :: y.field }

  def Escapee.subsumes (y y' : Escapee) : Bool :=
    y == y' && y.field.isPrefixOf y'.field

  def convertParamEscapeesToArgEscapees (paramEscapees : Array Escapee) (params args : Array Var) : Array Escapee :=
    paramEscapees.filterMap fun y => do
      let i ← params.findIdx? (· == y.var)
      return { y with var := args[i]! }

  def filterSubsumed (escapees : Array Escapee) : Array Escapee :=
    escapees.filter fun y => escapees.all fun y' => y == y' || ! y'.subsumes y

  def filterDead (escapees : Array Escapee) (alive : Array Var) : Array Escapee :=
    let alive := Lean.rbtreeOf alive.data compare
    escapees.filter (alive.contains ·.var)

  structure State where
    program     : Program
    funEscapees : Lean.RBMap Const (Array Escapee) compare

  def State.getEscapees (s : State) (c : Const) : Array Escapee :=
    s.funEscapees.find? c |>.getD #[]

  def State.appEscapees (s : State) (c : Const) (args : Array Var) : Array Escapee :=
    convertParamEscapeesToArgEscapees (s.getEscapees c) (s.program.find! c).params args

  partial def State.fnBodyEscapees (s : State) : FnBody → Array Escapee
    | FnBody.ret x => #[⟨x, []⟩]
    | FnBody.case _ cases => cases.concatMap s.fnBodyEscapees
    | FnBody.case' x cases => cases.concatMap fun ⟨ctor, args, F⟩ =>
      let FEscapees := s.fnBodyEscapees F
      let fieldEscapees : Array Escapee := FEscapees.filterMap fun y => do
        let proj : Nat ← args.indexOf? y.var
        return ⟨x, (ctor, proj) :: y.field⟩
      FEscapees ++ fieldEscapees
    | FnBody.«let» x expr F =>
      let FEscapees := s.fnBodyEscapees F
      FEscapees ++ if ! FEscapees.any (·.var == x) then
        #[]
      else
        match expr with
        | Expr.app c args =>
          s.appEscapees c args
        | Expr.papp _ args =>
          args.map fun arg => ⟨arg, []⟩
        | Expr.vapp y z =>
          #[⟨y, []⟩, ⟨z, []⟩]
        | Expr.ctor _ _ _ args =>
          if FEscapees.contains ⟨x, []⟩ then
            args.map fun arg => ⟨arg, []⟩
          else
            FEscapees.filter (·.var == x) |>.map fun y =>
              let field := y.field.head!
              let rest := y.field.drop 1
              let argIdxCorrespondingToField : Nat := field.2
              ⟨args[argIdxCorrespondingToField]!, rest⟩
        | Expr.proj ctor proj y =>
          FEscapees.filter (·.var == x) |>.map fun escapee =>
            ⟨y, (ctor, proj) :: escapee.field⟩

  partial def run (p : Program) (sccs : Lean.RBMap Const SCC compare) : Lean.RBMap Const (Array Escapee) compare := Id.run do
    let mut state : State := ⟨p, Lean.mkRBMap _ _ _⟩
    for (_, scc) in SCC.sccsInReverseTopologicalSort sccs do
      let mut stateChanged := true
      while stateChanged do
        stateChanged := false
        let mut queue : List Const := scc.component.map (·.name) |>.data
        while !queue.isEmpty do
          let current := queue.head!
          queue := queue.tail!
          let result := filterSubsumed <| filterDead (state.fnBodyEscapees (p.find! current).body) (p.find! current).params
          let lastState? := state.funEscapees.find? current
          if lastState?.isNone || lastState?.get! != result then
            state := { state with funEscapees := state.funEscapees.insert current result }
            stateChanged := true
    return state.funEscapees
end IR.EscapeAnalysis