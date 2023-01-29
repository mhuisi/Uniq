import Uniq.SCC

namespace IR.EscapeAnalysis
  structure Escapee where
    var   : Var
    field : List (Ctor × Proj)
    deriving BEq

  instance : ToString Escapee where
    toString e := s!"{e.var}_{e.field}"

  def Escapee.prepend (y : Escapee) (ctor : Ctor) (proj : Proj) : Escapee :=
    { y with field := (ctor, proj) :: y.field }

  def Escapee.subsumes (y y' : Escapee) : Bool :=
    y == y' && y.field.isPrefixOf y'.field

  def convertParamEscapeesToArgEscapees (paramEscapees : Array Escapee) (args : Array Var) : Array Escapee :=
    paramEscapees.map fun y =>
      let argIdx : Nat := y.var -- param vars are [0, |arity|)
      { y with var := args[argIdx]! }

  def filterSubsumed (escapees : Array Escapee) : Array Escapee :=
    escapees.filter fun y => escapees.all fun y' => y == y' || ! y'.subsumes y

  def filterDead (escapees : Array Escapee) (arity : Nat) : Array Escapee :=
    escapees.filter fun escapee => 
      let var : Nat := escapee.var
      var < arity

  structure State where
    program        : Program
    funEscapees    : Lean.RBMap Const (Array Escapee) compare

  def State.getEscapees (s : State) (c : Const) : Array Escapee :=
    s.funEscapees.find? c |>.getD #[]

  def State.appEscapees (s : State) (c : Const) (args : Array Var) : Array Escapee :=
    match s.funEscapees.find? c, s.program.find? c with
    | some escapees, _ =>
      convertParamEscapeesToArgEscapees escapees args
    | none, none => -- extern function without escapee decl; all args are assumed to escape
      args.map (⟨·, []⟩)
    | none, some _ => -- non-extern function that we haven't looked at yet; use the bottom element
      #[]

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

  abbrev ExternEscapeeMap := Lean.RBMap Const (Array Escapee) compare

  partial def run (p : Program) (externEscapees : ExternEscapeeMap) (sccs : Lean.RBMap Const SCC compare) : Lean.RBMap Const (Array Escapee) compare := Id.run do
    let mut state : State := ⟨p, externEscapees⟩
    for (_, scc) in SCC.sccsInReverseTopologicalSort sccs do
      let mut stateChanged := true
      let mut i := 0
      while stateChanged && i < 4 do
        stateChanged := false
        let mut queue : List Const := scc.component.map (·.name) |>.data
        while !queue.isEmpty do
          let current := queue.head!
          queue := queue.tail!
          let ⟨arity, body⟩ := p.find! current
          let result := filterSubsumed <| filterDead (state.fnBodyEscapees body) arity
          dbg_trace result
          let lastState? := state.funEscapees.find? current
          if lastState?.isNone || lastState?.get! != result then
            state := { state with funEscapees := state.funEscapees.insert current result }
            stateChanged := true
        i := i + 1
    return state.funEscapees

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

  #eval IO.println <| run program (Lean.mkRBMap _ _ _) (IR.SCC.computeSCCs <| IR.CG.computeCallGraph <| program)

  end List_get
end IR.EscapeAnalysis