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

  def Context.adjoin (Γ : Context) (var : Var) (type : Types.AttrType) : Context :=
    { Γ with types := Γ.types.insert var type }

  def Context.consumeIfUnique! (Γ : Context) (var : Var) : Context :=
    let foundType := Γ.types.find! var
    if foundType.isUnique then
      {Γ with types := Γ.types.erase var}
    else
      Γ

  def Context.applyTo? (Γ : Context) (vars : Array Var) (types : Array Types.AttrType)
    (isBorrowed : Nat → Bool := fun _ => false) : Option Context := do
    let mut Γ := Γ
    for i in [:vars.size] do
      let var := vars[i]!
      let type := types[i]!
      guard <| Γ.canApply var type
      if ! isBorrowed i then
        Γ := Γ.adjoin var type
        Γ := Γ.consumeIfUnique! var
    return Γ

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

  partial def check (Γ : Context) (body : IR.FnBody) (retType : Types.AttrType) : Bool := Id.run do
    dbg_trace Γ.types
    dbg_trace "{body.printHead}"
    dbg_trace ""
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
        let some Γ' := Γ.applyTo? args paramTypes (isBorrowed := Γ.isBorrowedIn c)
          | return false
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
        let some Γ' := Γ.applyTo? args passedParamTypes
          | return false
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
        let some Γ' := Γ.applyTo? #[y] #[paramType]
          | return false
        let varType := determinePappReturnType restParamTypes funRetType
        let Γ' := Γ'.adjoin var varType
        return check Γ' rest retType

      | IR.Expr.ctor adtName explicitParamTypes ctorIdx args =>
        if !args.all Γ.nonzero then
          return false
        let adtDecl := Γ.static.adtDecls.find! adtName
        let ctor := adtDecl.ctors.get! ctorIdx
        let mut inferredParamTypes := Lean.RBMap.empty
        for ⟨arg, field⟩ in args.zip ctor do
          let some foundType := Γ.types.find? arg
            | return false
          let some unifiedVars := foundType.unifyWith field
            | return false -- not unifiable => not applicable
          let some merged := Types.mergeUnifiedVars inferredParamTypes unifiedVars
            | return false -- conflicting variable assignments
          inferredParamTypes := merged
        let some argTypes := adtDecl.computeCtorParamTypes explicitParamTypes inferredParamTypes
          | return false -- one param type was neither provided nor could be inferred
        let ctor := adtDecl.subst adtName argTypes |>.ctors.get! ctorIdx
        let some Γ' := Γ.applyTo? args ctor
          | return false
        let Γ' := Γ'.adjoin var (.adt .unique adtName argTypes)
        return check Γ' rest retType

      | IR.Expr.proj i j x =>
        if Γ.isZeroed x i j then
          return false
        let .adt attr adtName typeArgs := Γ.types.find! x
          | return false
        let mut field := substitutedCtors Γ.static adtName typeArgs |>.get! i |>.get! j
        if attr matches .shared then
          field := field.makeShared
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
      let some (Types.AttrType.adt attr name params) := Γ.types.find? var
        | return false
      let ctors := substitutedCtors Γ.static name params
      let Γ' := Γ.consumeIfUnique! var
      return cases.zip ctors |>.all fun ⟨case, ctor⟩ =>
        let ⟨_, vars, F⟩ := case
        let ctor := ctor.map fun field =>
          if attr matches .shared then
            field.makeShared
          else
            field
        let Γ' := vars.zip ctor |>.foldr (init := Γ') fun ⟨var, field⟩ Γ' => Γ'.adjoin var field
        check Γ' F retType

  instance [ToString α] : ToString (Lean.RBTree α cmp) where
    toString tree := toString tree.toArray

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

namespace List_get
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
        ilet nonevar ≔ ictor iOption⟦#[some <| .erased .shared]⟧iNone @@ #[];
        iret nonevar),
      (iCons, #[head, tail],
        ilet zero ≔ iapp mkZero @@ #[];
        ilet eqr ≔ iapp natEq @@ #[ivar, zero];
        icase eqr: #[
          ilet predr ≔ iapp predNat @@ #[ivar];
          ilet recr ≔ iapp getList @@ #[tail, predr];
          iret recr,
          ----
          ilet somevar ≔ ictor iOption⟦#[none]⟧iSome @@ #[head];
          iret somevar
        ])
    ]

  def program : IR.Program := Lean.RBMap.ofList [(getList, ⟨2, iget?⟩)]
  def funTypes : IR.FunTypeMap := Lean.RBMap.ofList [
    (getList, #[.adt .unique iList #[.erased .unique], .adt .shared iNat #[]], .adt .unique iOption #[.erased .unique]),
    (mkZero, #[], .adt .unique iNat #[]),
    (natEq, #[.adt .shared iNat #[], .adt .shared iNat #[]], .adt .shared iBool #[]),
    (predNat, #[.adt .shared iNat #[]], .adt .shared iNat #[])
  ]
  def adtDecls : Types.ADTDeclMap := Lean.RBMap.ofList [
    (iList, .mk 0 #[1] #[#[], #[.typeVar 1, .selfVar .unique 0]]),
    (iOption, .mk 0 #[1] #[#[], #[.typeVar 1]])
  ]
  def externUniqueFields : Types.ExternUniqueFieldsMap := Lean.RBMap.empty
  def externEscapees : IR.EscapeAnalysis.ExternEscapeeMap := Lean.RBMap.ofList [
    (natEq, #[])
  ]

  #eval Checker.checkProgram program funTypes adtDecls externUniqueFields externEscapees
end List_get

namespace DupApp
  def program : IR.Program := Lean.RBMap.ofList [(0, ⟨1, ilet 1 ≔ iapp 1 @@ #[0, 0]; iret 1⟩)]
  def funTypes : IR.FunTypeMap := Lean.RBMap.ofList [
    (0, #[.erased .unique], .erased .unique),
    (1, #[.erased .shared, .erased .shared], .erased .unique)
  ]
  #eval Checker.checkProgram program funTypes Lean.RBMap.empty Lean.RBMap.empty Lean.RBMap.empty
end DupApp