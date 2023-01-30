import Uniq.Borrowing

-- TODOs:
-- remove sorries in functions
-- account for extern functions

namespace Checker
  structure StaticContext where
    program        : IR.Program
    funTypes       : IR.FunTypeMap
    adtDecls       : Types.ADTDeclMap
    borrowedParams : Borrowing.BorrowedParamMap

  def StaticContext.funType! (Γ : StaticContext) (c : Const) : Array Types.AttrType × Types.AttrType :=
    Γ.funTypes.find! c

  structure Context where
    static       : StaticContext
    zeroedFields : Lean.RBMap Var (Lean.RBTree (Ctor × Proj) compare) compare
    types        : Lean.RBMap Var Types.AttrType compare

  def Context.funType! (Γ : Context) (c : Const) : Array Types.AttrType × Types.AttrType :=
    Γ.static.funType! c

  def Context.nonzero (Γ : Context) (var : Var) : Bool := Id.run do
    let some zeroedFields := Γ.zeroedFields.find? var
      | return true
    return zeroedFields.size == 0

  def attrApplicableTo (a b : Types.AttrType) : Bool :=
    a.isUnique || a.isShared && b.isShared

  def erasedApplicableToModOuterAttr : Types.AttrType → Bool
    | .erased _ | .selfVar .. | .typeVar .. | .func .. => true
    | .adt _ _ args => args.all fun arg => arg.makeShared == arg

  partial def typeApplicableTo (a b : Types.AttrType) : Bool := Id.run do
    if !attrApplicableTo a b then
      return false
    match a, b with
    | .erased _, b => erasedApplicableToModOuterAttr b
    | _, .erased _ => true
    | .selfVar _ varA, .selfVar _ varB =>
      varA == varB
    | .typeVar varA, .typeVar varB =>
      varA == varB
    | .adt _ nameA argsA, .adt _ nameB argsB =>
      nameA == nameB
        && argsA.size == argsB.size
        && (argsA.zip argsB).all fun ⟨argA, argB⟩ => typeApplicableTo argA argB
    | .func paramsA retA, .func paramsB retB =>
      typeApplicableTo retA retB
        && paramsA.size == paramsB.size
        && (paramsA.zip paramsB).all fun ⟨paramA, paramB⟩ => typeApplicableTo paramA paramB
    | _, _ => false

  def Context.canApply (Γ : Context) (var : Var) (type : Types.AttrType) : Bool := Id.run do
    let some foundType := Γ.types.find? var
      | return false
    return typeApplicableTo foundType type

  def Context.canApplyAll (Γ : Context) (vars : Array Var) (types : Array Types.AttrType) : Bool :=
    vars.zip types |>.all fun ⟨var, type⟩ => Γ.canApply var type

  def Context.eraseIfUnique! (Γ : Context) (var : Var) : Context :=
    let foundType := Γ.types.find! var
    if foundType.isUnique then
      {Γ with types := Γ.types.erase var}
    else
      Γ

  def Context.eraseAllUnique! (Γ : Context) (vars : Array Var) : Context := Id.run do
    let mut Γ := Γ
    for var in vars do
      Γ := Γ.eraseIfUnique! var
    return Γ

  def Context.adjoin (Γ : Context) (var : Var) (type : Types.AttrType) : Context :=
    { Γ with types := Γ.types.insert var type }

  def Context.adjoinAll (Γ : Context) (vars : Array Var) (types : Array Types.AttrType) : Context := Id.run do
    let mut Γ := Γ
    for ⟨var, type⟩ in vars.zip types do
      Γ := Γ.adjoin var type
    return Γ

  def Context.consumeWhenAppliedTo (Γ : Context) (var : Var) (type : Types.AttrType) : Context :=
    Γ.adjoin var type |>.eraseIfUnique! var

  def Context.consumeAllWhenAppliedTo (Γ : Context) (vars : Array Var) (types : Array Types.AttrType) : Context :=
    Γ.adjoinAll vars types |>.eraseAllUnique! vars

  def Context.isZeroed (Γ : Context) (var : Var) (ctor : Ctor) (proj : Proj) : Bool :=
    Γ.zeroedFields.find? var |>.map (·.contains (ctor, proj)) |>.getD false

  def Context.zero (Γ : Context) (adtAttr fieldAttr : Types.Attr) (var : Var) (ctor : Ctor) (proj : Proj) : Context := Id.run do
    let mut zeroedFields := Γ.zeroedFields
    if adtAttr matches .unique && fieldAttr matches .unique then
      let zeroedFieldsOfVar := Γ.zeroedFields.find? var
        |>.getD (Lean.mkRBTree _ _)
        |>.insert (ctor, proj)
      zeroedFields := zeroedFields.insert var zeroedFieldsOfVar
    return { Γ with zeroedFields := zeroedFields }

  def substitutedCtors (static : StaticContext) (adtName : ADTName) (argTypes : Array Types.AttrType) : Array (Array Types.AttrType) :=
    static.adtDecls.find! adtName |>.subst adtName argTypes |>.ctors

  def determinePappReturnType (paramTypes : Array Types.AttrType) (retType : Types.AttrType) : Types.AttrType :=
    if paramTypes.size == 0 then
      retType
    else
      .func paramTypes retType

  def Context.isBorrowedIn (Γ : Context) (c : Const) (i : Nat) : Bool :=
    Γ.static.borrowedParams.find? c |>.map (·.contains i) |>.getD false

  def Context.consumeAllNonBorrowedWhenAppliedTo (Γ : Context) (vars : Array Var) (c : Const) (types : Array Types.AttrType) : Context := Id.run do
    let mut nonBorrowedVars := #[]
    let mut nonBorrowedTypes := #[]
    for i in [0:vars.size] do
      if !Γ.isBorrowedIn c i then
        nonBorrowedVars := nonBorrowedVars.push vars[i]!
        nonBorrowedTypes := nonBorrowedTypes.push types[i]!
    Γ.adjoinAll nonBorrowedVars nonBorrowedTypes |>.eraseAllUnique! nonBorrowedVars

  partial def check (Γ : Context) (body : IR.FnBody) (retType : Types.AttrType) : Bool := Id.run do
    match body with
    | IR.FnBody.ret var =>
      if !Γ.nonzero var then
        return false
      return Γ.canApply var retType
    | IR.FnBody.«let» var expr rest =>
      match expr with
      | IR.Expr.app c args =>
        if !args.all Γ.nonzero then
          return false
        let ⟨paramTypes, funRetType⟩ := Γ.funType! c
        if !Γ.canApplyAll args paramTypes then
          return false
        let Γ' := Γ.consumeAllNonBorrowedWhenAppliedTo args c paramTypes
        let Γ' := Γ'.adjoin var funRetType
        return check Γ' rest retType
      | IR.Expr.papp c args =>
        if !args.all Γ.nonzero then
          return false
        let ⟨paramTypes, funRetType⟩ := Γ.funType! c
        let paramTypes := paramTypes.map (·.makeShared)
        let funRetType := funRetType.makeShared
        let ⟨passedParamTypes, restParamTypes⟩ :=
          (paramTypes.data.take args.size |>.toArray, paramTypes.data.drop args.size |>.toArray)
        if !Γ.canApplyAll args passedParamTypes then
          return false
        let Γ' := Γ.consumeAllWhenAppliedTo args passedParamTypes
        let varType := determinePappReturnType restParamTypes funRetType
        let Γ' := Γ'.adjoin var varType
        return check Γ' rest retType
      | IR.Expr.vapp x y =>
        if !Γ.nonzero y then
          return false
        let .func paramTypes funRetType := Γ.types.find! x
          | return false
        let paramType := paramTypes[0]!
        let restParamTypes := paramTypes.eraseIdx 0
        if !Γ.canApply y paramType then
          return false
        let Γ' := Γ.consumeWhenAppliedTo y paramType
        let varType := determinePappReturnType restParamTypes funRetType
        let Γ' := Γ'.adjoin var varType
        return check Γ' rest retType
      | IR.Expr.ctor adtName typeArgs ctorIdx args =>
        if !args.all Γ.nonzero then
          return false
        let ctor := substitutedCtors Γ.static adtName typeArgs |>.get! ctorIdx
        if !Γ.canApplyAll args ctor then
          return false
        let Γ' := Γ.consumeAllWhenAppliedTo args ctor
        let Γ' := Γ'.adjoin var (.adt .unique adtName typeArgs)
        return check Γ' rest retType
      | IR.Expr.proj i j x =>
        if Γ.isZeroed x i j then
          return false
        let .adt attr adtName typeArgs := Γ.types.find! x
          | return false
        let field := substitutedCtors Γ.static adtName typeArgs |>.get! i |>.get! j
        let Γ' := Γ.zero attr field.attr x i j
        let Γ' := Γ'.adjoin var field
        return check Γ' rest retType
    | IR.FnBody.case var cases =>
      if !Γ.nonzero var then
        return false
      return cases.all (check Γ · retType)
    | IR.FnBody.case' var cases =>
      if !Γ.nonzero var then
        return false
      let some (Types.AttrType.adt _ name params) := Γ.types.find? var
        | return false
      let ctors := substitutedCtors Γ.static name params
      let Γ' := Γ.eraseIfUnique! var
      return cases.zip ctors |>.all fun ⟨case, ctor⟩ =>
        let ⟨_, vars, F⟩ := case
        let Γ' := Γ'.adjoinAll vars ctor
        check Γ' F retType

  def checkProgram
    (program            : IR.Program) -- missing all extern consts
    (funTypes           : IR.FunTypeMap) -- complete
    (adtDecls           : Types.ADTDeclMap) -- missing all extern types
    (externUniqueFields : Types.ExternUniqueFieldsMap) -- missing some extern types
    (externEscapees     : IR.EscapeAnalysis.ExternEscapeeMap) -- missing some extern consts
    : Bool := Id.run do
    for ⟨c, function⟩ in program do
      let ⟨paramTypes, retType⟩ := funTypes.find! c
      let initialTypes := Lean.RBMap.ofList ((List.range function.arity).zip paramTypes.data)
      let cg := IR.CG.computeCallGraph program
      let sccs := IR.SCC.computeSCCs cg
      let escapees := IR.EscapeAnalysis.run program externEscapees sccs
      let borrowedParams := Borrowing.computeBorrowedParams adtDecls externUniqueFields funTypes escapees
      let typechecks := check ⟨⟨program, funTypes, adtDecls, borrowedParams⟩, {}, initialTypes⟩ function.body retType
      if !typechecks then
        return false
    return true
end Checker

section List_get
    set_option trace.Compiler.result true in
    def List_get? (xs : List α) (i : Nat) : Option α :=
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
    def iNat : ADTName := 2
    def iBool : ADTName := 3

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

    def iget? : IR.FnBody :=
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

    def program : IR.Program := Lean.RBMap.ofList [(getList, ⟨2, iget?⟩)]
    def funTypes : IR.FunTypeMap := Lean.RBMap.ofList [
      (getList, #[.adt .unique iList #[.erased .unique], .adt .shared iNat #[]], .erased .unique),
      (mkZero, #[], .adt .unique iNat #[]),
      (natEq, #[.adt .shared iNat #[], .adt .shared iNat #[]], .adt .shared iBool #[]),
      (predNat, #[.adt .shared iNat #[]], .adt .shared iNat #[])
    ]
    def adtDecls : Types.ADTDeclMap := Lean.RBMap.ofList [
      (iList, .mk 0 #[1] #[#[], #[.typeVar 1, .selfVar .shared 0]]),
      (iOption, .mk 0 #[1] #[#[], #[.typeVar 1]])
    ]
    def externUniqueFields : Types.ExternUniqueFieldsMap := Lean.RBMap.empty
    def externEscapees : IR.EscapeAnalysis.ExternEscapeeMap := Lean.RBMap.empty
end List_get