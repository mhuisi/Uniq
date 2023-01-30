import Uniq.SCC

namespace IR.EscapeAnalysis
  inductive Tag where
    | const (c : Const)
    | case  (idx : Nat)
    | app
    | param (idx : Nat)
  deriving BEq, Inhabited, Ord

  def compareLists [Ord α] (xs ys : List α) : Ordering :=
    match xs, ys with
    | [], [] => .eq
    | [], _  => .lt
    | _, []  => .gt
    | (x :: xs), (y :: ys) =>
      match Ord.compare x y with
      | .lt => .lt
      | .gt => .gt
      | .eq => compareLists xs ys

  instance : Ord (List Tag) where
    compare := compareLists

  instance : ToString Tag where
    toString tag := match tag with
      | .const c => s!"const {c}"
      | .case idx => s!"case {idx}"
      | .app => s!"app"
      | .param idx => s!"param {idx}"

  structure Escapee where
    var         : Var
    field       : List (Ctor × Proj)
    tag?        : Option (List Tag)
    deriving BEq, Inhabited

  def longestCommonPrefix [BEq α] (xs ys : List α) : List α :=
    xs.zip ys |>.filter (fun (x, y) => x == y) |>.map (·.1)

  def Escapee.collapse (x y : Escapee) : Escapee :=
    assert! x.var == y.var
    { x with field := longestCommonPrefix x.field y.field }

  structure State where
    program     : Program
    funEscapees : Lean.RBMap Const (Array Escapee) compare

  def mkNonDerivedEscapee (var : Var) (field : List (Ctor × Proj)) : Escapee :=
    ⟨var, field, none⟩

  def mkDerivedEscapee (previous : Escapee) (var : Var) (field : List (Ctor × Proj)) : Escapee :=
    ⟨var, field, previous.tag?⟩

  instance : ToString Escapee where
    toString e := s!"{e.var}_{e.field}"

  def Escapee.subsumes (y y' : Escapee) : Bool :=
    y == y' && y.field.isPrefixOf y'.field

  def convertParamEscapeesToArgEscapees (tag : List Tag) (paramEscapees : Array Escapee) (args : Array Var) : Array Escapee :=
    paramEscapees.map fun y =>
      let argIdx : Nat := y.var -- param vars are [0, |arity|)
      { y with var := args[argIdx]!, tag? := some (.param argIdx :: tag) }

  def filterSubsumed (escapees : Array Escapee) : Array Escapee :=
    escapees.filter fun y => escapees.all fun y' => y == y' || ! y'.subsumes y

  def groupEscapeesByTag (escapees : Array Escapee) : Lean.RBMap (List Tag) (List Escapee) compare := Id.run do
    let mut r := Lean.mkRBMap _ _ _
    for escapee in escapees do
      if let some tag := escapee.tag? then
        let acc := r.find? tag |>.getD []
        r := r.insert tag (escapee :: acc)
    return r

  def collapseSameTags (escapees : Array Escapee) : Array Escapee := Id.run do
    let escapeesByTag := groupEscapeesByTag escapees
    let mut r := escapees.filter (·.tag?.isNone)
    for ⟨_, escapees⟩ in escapeesByTag do
      match escapees with
      | [x] => r := r.push x
      | [x, y] => r := r.push (x.collapse y)
      | _ => panic! "error: more than two escapees with the same tag"
    return r

  def filterDead (escapees : Array Escapee) (arity : Nat) : Array Escapee :=
    escapees.filter fun escapee =>
      let var : Nat := escapee.var
      var < arity

  def State.appEscapees (s : State) (c : Const) (args : Array Var) (tag : List Tag) : Array Escapee :=
    match s.funEscapees.find? c, s.program.find? c with
    | some escapees, _ =>
      convertParamEscapeesToArgEscapees tag escapees args
    | none, none => -- extern function without escapee decl; all args are assumed to escape
      args.map (mkNonDerivedEscapee · [])
    | none, some _ => -- non-extern function that we haven't looked at yet; use the bottom element
      #[]

  partial def State.fnBodyEscapees (s : State) (tag : List Tag) (body : FnBody) : Array Escapee :=
    match body with
    | FnBody.ret x => #[mkNonDerivedEscapee x []]
    | FnBody.case _ cases => Id.run do
      let mut r := #[]
      for i in [0:cases.size] do
        let escapees := s.fnBodyEscapees (.case i :: tag) cases[i]!
        r := r ++ escapees
      return r
    | FnBody.case' x cases => Id.run do
      let mut r := #[]
      for i in [0:cases.size] do
        let ⟨ctor, args, F⟩ := cases[i]!
        let FEscapees := s.fnBodyEscapees (.case i :: tag) F
        let fieldEscapees : Array Escapee := FEscapees.filterMap fun y => do
          let proj ← args.indexOf? y.var
          mkDerivedEscapee y x ((ctor, proj.val) :: y.field)
        r := r ++ FEscapees ++ fieldEscapees
      return r
    | FnBody.«let» x expr F =>
      let tag :=
        if expr matches .app .. then
          .app :: tag
        else
          tag
      let FEscapees := s.fnBodyEscapees tag F
      let exprEscapees :=
        if ! FEscapees.any (·.var == x) then
          #[]
        else
          match expr with
          | Expr.app c args =>
            s.appEscapees c args tag
          | Expr.papp _ args =>
            args.map fun arg => mkNonDerivedEscapee arg []
          | Expr.vapp y z =>
            #[mkNonDerivedEscapee y [], mkNonDerivedEscapee z []]
          | Expr.ctor _ _ _ args =>
            if FEscapees.any fun e => e.var == x && e.field == [] then
              args.map fun arg => mkNonDerivedEscapee arg []
            else
              FEscapees.filter (·.var == x) |>.map fun y =>
                let field := y.field.head!
                let rest := y.field.drop 1
                let argIdxCorrespondingToField : Nat := field.2
                mkDerivedEscapee y args[argIdxCorrespondingToField]! rest
          | Expr.proj ctor proj y =>
            FEscapees.filter (·.var == x) |>.map fun escapee =>
              mkDerivedEscapee escapee y ((ctor, proj) :: escapee.field)
      FEscapees ++ exprEscapees

  abbrev ExternEscapeeMap := Lean.RBMap Const (Array Escapee) compare

  partial def run (p : Program) (externEscapees : ExternEscapeeMap) (sccs : Lean.RBMap Const SCC compare) : Lean.RBMap Const (Array Escapee) compare := Id.run do
    let mut s := State.mk p externEscapees
    for (_, scc) in SCC.sccsInReverseTopologicalSort sccs do
      let mut stateChanged := true
      while stateChanged do
        stateChanged := false
        let mut queue : List Const := scc.component.map (·.name) |>.data
        while !queue.isEmpty do
          let current := queue.head!
          queue := queue.tail!
          let ⟨arity, body⟩ := p.find! current
          let escapees := s.fnBodyEscapees [.const current] body
          let result := filterSubsumed <| collapseSameTags <| filterDead escapees arity
          let lastState? := s.funEscapees.find? current
          if lastState?.isNone || lastState?.get! != result then
            s := { s with funEscapees := s.funEscapees.insert current result }
            stateChanged := true
    return s.funEscapees

  section List_get
    set_option trace.Compiler.result true in
    def List.get? (xs : List α) (i : Nat) : Option α :=
      match xs with
      | [] => none
      | x :: xs =>
        match i == 0 with
        | true  => Option.some x
        | false => xs.get? i.pred

    /-
    def IR.EscapeAnalysis.List.get?._redArg xs i : Option lcErased :=
      cases xs : Option lcErased
      | List.nil =>
        let _x.1 := none _;
        return _x.1
      | List.cons head.2 tail.3 =>
        let _x.4 := 0;
        let _x.5 := Nat.beq i _x.4;
        cases _x.5 : Option lcErased
        | Bool.false =>
          let _x.6 := Nat.pred i;
          let _x.7 := List.get?._redArg tail.3 _x.6;
          return _x.7
        | Bool.true =>
          let _x.8 := some _ head.2;
          return _x.8
    -/

    def getList : Const := 0
    def mkZero : Const := 1
    def natEq : Const := 2
    def predNat : Const := 3

    def iList : ADTName := 0
    def iNil : Ctor := 0
    def iCons : Ctor := 1
    def iOption : ADTName := 1
    def iNone : Ctor := 0
    def iSome : Ctor := 1

    def xsvar : Var := 0
    def ivar : Var := 1
    def nonevar : Var := 2
    def head : Var := 3
    def tail : Var := 4
    def zero : Var := 5
    def eqr : Var := 6
    def predr : Var := 7
    def recr : Var := 8
    def somevar : Var := 9

    def iget? : FnBody :=
      icase' xsvar: #[
        (iNil, #[],
          ilet nonevar ≔ ictor iOption⟦#[.erased .shared]⟧iNone @@ #[];
          iret nonevar),
        (iCons, #[head, tail],
          ilet zero ≔ iapp mkZero @@ #[];
          ilet eqr ≔ iapp natEq @@ #[ivar, zero];
          icase eqr: #[
            ilet predr ≔ iapp predNat @@ #[ivar];
            ilet recr ≔ iapp getList @@ #[tail, predr];
            iret recr,
            ----
            ilet somevar ≔ ictor iOption⟦#[.erased .shared]⟧iSome @@ #[head];
            iret somevar
          ])
      ]

    def program : Program := Lean.RBMap.ofList [(getList, ⟨2, iget?⟩)]

    -- {0: #[0_[(1, 0)], 0_[(1, 1)]];}
    #eval IO.println <| run program (Lean.mkRBMap _ _ _) (IR.SCC.computeSCCs <| IR.CG.computeCallGraph <| program)

  end List_get
end IR.EscapeAnalysis