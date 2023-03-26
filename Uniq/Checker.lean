import Uniq.EscapeAnalysis

-- be warned: there are lots of tiny inefficiencies in this entire code that could easily be fixed by
-- memoizing the right data. in a serious implementation, this should be fixed.
-- generally, this code was written in a hurry and needs a major make-over.
namespace Checker
  variable (funTypes : IR.FunTypeMap) (adtDecls : Types.ADTDeclMap) (retType : Types.AttrType) in
  partial def inferUsages (body : IR.FnBody) : Lean.RBTree Var compare := Id.run do
    match body with
    | IR.FnBody.ret var =>
      if retType.isUnique then
        return Lean.RBTree.fromArray #[var] compare
      else
        return Lean.RBTree.empty
    
    | IR.FnBody.«let» var expr rest =>
      match expr with
      | IR.Expr.app c args =>
        let mut restUsage := inferUsages rest
        let ⟨paramTypes, _⟩ := funTypes.find! c
        for ⟨arg, paramType⟩ in args.zip paramTypes do
          if paramType.isUnique then
            restUsage := restUsage.insert arg
        return restUsage
      
      | IR.Expr.papp .. =>
        return inferUsages rest -- all args are shared

      | IR.Expr.vapp .. =>
        return inferUsages rest -- all args are shared

      | IR.Expr.ctor adtName _ ctorIdx args =>
        let mut restUsage := inferUsages rest
        if restUsage.contains var then
          let adtDecl := adtDecls.find! adtName
          let ctor := adtDecl.ctors.get! ctorIdx
          for ⟨arg, paramType⟩ in args.zip ctor do
            -- typeVar: we don't know whether this usage will be unique or not
            if paramType matches .typeVar _ || paramType.isUnique then
              restUsage := restUsage.insert arg
        return restUsage

      | IR.Expr.proj _ _ x =>
        let mut restUsage := inferUsages rest
        if restUsage.contains x then
          restUsage := restUsage.insert var
        return restUsage

    | IR.FnBody.case _ cases =>
      let mut usages := Lean.RBTree.empty
      for case in cases do
        usages := usages.union (inferUsages case)
      return usages
    
    | IR.FnBody.case' var cases =>
      let mut usages := Lean.RBTree.empty
      for case in cases do
        let ⟨_, vars, F⟩ := case
        let usagesF := inferUsages F
        if vars.any usagesF.contains then
          usages := usages.insert var
        usages := usages.union usagesF
      return usages

  abbrev EscapeeMap := Lean.RBMap Const (Array (Array IR.EscapeAnalysis.Escapee)) compare

  def groupFunEscapeesByParam
    (arity       : Nat)
    (funEscapees : Array IR.EscapeAnalysis.Escapee)
    : Array (Array IR.EscapeAnalysis.Escapee) := Id.run do
    let mut r := mkArray arity #[]
    for escapee in funEscapees do
      r := r.modify escapee.var (·.push escapee)
    return r

  structure StaticContext where
    program            : IR.Program
    funTypes           : IR.FunTypeMap
    adtDecls           : Types.ADTDeclMap
    escapees           : EscapeeMap
    externUniqueFields : Types.ExternUniqueFieldsMap
    usages             : Lean.RBTree Var compare

  def StaticContext.funType! (Γ : StaticContext) (c : Const) : Array Types.AttrType × Types.AttrType :=
    Γ.funTypes.find! c

  def StaticContext.isBorrowedIn
    (Γ       : StaticContext)
    (c       : Const)
    (i       : Nat)
    (argType : Types.AttrType) : Bool := Id.run do
    let ⟨paramTypes, _⟩ := Γ.funTypes.find! c
    let some funEscapees := Γ.escapees.find? c
      | return false
    dbg_trace "found escapees"
    let noUniqueFieldsEscape : ADTName → Array Types.AttrType → Bool := fun name args =>
       funEscapees[i]!.all fun escapee =>
            -- we use args' because we want the actual type args in the provided argument to check
            -- uniqueness. a shared type arg is allowed to escape, a unique one is not.
            !Types.isUniqueField Γ.adtDecls Γ.externUniqueFields (.adt .unique name args) escapee.field
    match argType, paramTypes[i]! with
    | .adt .unique name typeArgs, .adt .shared ..
    | .adt .unique name typeArgs, .erased .shared =>
      return noUniqueFieldsEscape name typeArgs
    | .erased .unique, .adt .shared name' typeArgs' =>
      return noUniqueFieldsEscape name' <| typeArgs'.map (·.strengthen)
    | .erased .unique, .erased .shared =>
      return funEscapees[i]!.isEmpty
    | _, _ => false


  structure Context where
    static       : StaticContext
    zeroedFields : Lean.RBMap Var (Lean.RBTree (Ctor × Proj) compare) compare
    types        : Lean.RBMap Var Types.AttrType compare

  def Context.funType! (Γ : Context) (c : Const) : Array Types.AttrType × Types.AttrType :=
    Γ.static.funType! c

  def Context.isUniqueUsage (Γ : Context) (var : Var) : Bool :=
    Γ.static.usages.contains var

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
    (isBorrowed : Nat → Types.AttrType → Bool := fun _ _ => false) : Option Context := do
    let mut Γ := Γ
    for i in [:vars.size] do
      let var := vars[i]!
      let type := types[i]!
      guard <| Γ.canApply var type
      let argType := Γ.types.find! var
      if ! isBorrowed i argType then
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

  def Context.isBorrowedIn (Γ : Context) (c : Const) (i : Nat) (argType : Types.AttrType) : Bool :=
    Γ.static.isBorrowedIn c i argType

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
        let mut ctor := adtDecl.subst adtName argTypes |>.ctors.get! ctorIdx
        let mut adtType : Types.AttrType := .adt .unique adtName argTypes
        if !Γ.isUniqueUsage var then
          ctor := ctor.map (·.makeShared)
          adtType := adtType.makeShared
        let some Γ' := Γ.applyTo? args ctor
          | return false
        let Γ' := Γ'.adjoin var adtType
        return check Γ' rest retType

      | IR.Expr.proj i j x =>
        if Γ.isZeroed x i j then
          return false
        let .adt attr adtName typeArgs := Γ.types.find! x
          | return false
        let mut field := substitutedCtors Γ.static adtName typeArgs |>.get! i |>.get! j
        let mut Γ' := Γ
        if attr matches .shared then
          field := field.makeShared
          Γ' := Γ'.zero attr field.attr x i j
        Γ' := Γ'.adjoin var field
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
    let cg := IR.CG.computeCallGraph program
    let sccs := IR.SCC.computeSCCs cg
    let escapees := IR.EscapeAnalysis.run program externEscapees sccs
    let mut escapeeMap := Lean.RBMap.empty
    for ⟨c, funEscapees⟩ in escapees do
      let arity := (funTypes.find! c).1.size
      escapeeMap := escapeeMap.insert c (groupFunEscapeesByParam arity funEscapees)
    for ⟨c, function⟩ in program do
      let ⟨paramTypes, retType⟩ := funTypes.find! c
      let initialTypes := Lean.RBMap.ofList ((List.range function.arity).zip paramTypes.data)
      let usages := inferUsages funTypes adtDecls retType function.body
      let typechecks := check ⟨⟨program, funTypes, adtDecls, escapeeMap, externUniqueFields, usages⟩, {}, initialTypes⟩ function.body retType
      if !typechecks then
        return false
    return true
end Checker

namespace Test.List_map
  def List.map (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: map f xs

  /-
  def Test.List_map.List.map._redArg f x.1 : List lcErased :=
    cases x.1 : List lcErased
    | List.nil =>
      return x.1
    | List.cons head.2 tail.3 =>
      let _x.4 := f head.2;
      let _x.5 := Test.List_map.List.map._redArg f tail.3;
      let _x.6 := List.cons _ _x.4 _x.5;
      return _x.6 
  -/

  def map : Const := 0

  def iList : ADTName := 0
  def iNil : Ctor := 0
  def iCons : Ctor := 1

  def fvar : Var := 0
  def xsvar : Var := 1
  def nl : Var := 2
  def hd : Var := 3
  def tl : Var := 4
  def hd' : Var := 5
  def tl' : Var := 6
  def res : Var := 7

  def imap : IR.FnBody :=
    icase' xsvar: #[
      (iNil, #[],
        ilet nl ≔ ictor iList⟦#[some <| .erased .shared]⟧iNil @@ #[];
        iret nl),
      (iCons, #[hd, tl],
        ilet hd' ≔ ivapp fvar @@ hd;
        ilet tl' ≔ iapp map @@ #[fvar, tl];
        ilet res ≔ ictor iList⟦#[some <| .erased .shared]⟧iCons @@ #[hd', tl'];
        iret res)
    ]

  def program : IR.Program := Lean.RBMap.ofList [(map, ⟨2, imap⟩)]
  def funTypes : IR.FunTypeMap := Lean.RBMap.ofList [
    (map, #[.func #[(.erased .shared)] (.erased .shared), .adt .shared iList #[.erased .shared]], .adt .unique iList #[.erased .shared])
  ]
  def adtDecls : Types.ADTDeclMap := Lean.RBMap.ofList [
    (iList, .mk 0 #[1] #[#[], #[.typeVar 1, .selfVar .unique 0]])
  ]
  def externUniqueFields : Types.ExternUniqueFieldsMap := Lean.RBMap.empty
  def externEscapees : IR.EscapeAnalysis.ExternEscapeeMap := Lean.RBMap.empty

  #eval Checker.checkProgram program funTypes adtDecls externUniqueFields externEscapees
  #eval IO.println <| IR.EscapeAnalysis.run program externEscapees (IR.SCC.computeSCCs <| IR.CG.computeCallGraph <| program)
end Test.List_map

namespace Test.Array_transposeSquare
  def Array.swap [Inhabited α] (xs : Array α) (i : Nat) (x : α) : Array α × α :=
    let x' := xs[i]!
    let xs := xs.set! i x
    (xs, x')

partial def Array.transposeSquare [Inhabited α] (xs : Array (Array α)) (i j : Nat) : Array (Array α) :=
  let n := Array.size xs
  if i >= n then
    xs
  else if j >= n then
    Array.transposeSquare xs (i + 1) (i + 2)
  else
    let (xs, xs_i) := Array.swap xs i #[]
    let (xs, xs_j) := Array.swap xs j #[]
    let x := Array.get! xs_i j
    let x' := Array.get! xs_j i
    let xs_i := Array.set! xs_i j x'
    let xs_j := Array.set! xs_j i x
    let xs := Array.set! xs i xs_i
    let xs := Array.set! xs j xs_j
    Array.transposeSquare xs i (j + 1)
      
  def transpose : Const := 0
  def mkOne : Const := 1
  def mkTwo : Const := 2
  def size : Const := 3
  def geq : Const := 4
  def add : Const := 5
  def mkEmpty : Const := 6
  def swap : Const := 7
  def get : Const := 8
  def set : Const := 9
  def set' : Const := 10

  def Array : ADTName := 0
  def Nat : ADTName := 1
  def Bool : ADTName := 2
  def Prod : ADTName := 3
  def mkTuple : Ctor := 0

  def xs0 : Var := 0
  def i : Var := 1
  def j : Var := 2 
  def one : Var := 3
  def two : Var := 4
  def n : Var := 5
  def b1 : Var := 6
  def b2 : Var := 7
  def iadd1 : Var := 8
  def iadd2 : Var := 9
  def r1 : Var := 10
  def empty1 : Var := 11
  def empty2 : Var := 12
  def p1 : Var := 13
  def xs1 : Var := 14
  def xs_i0 : Var := 15
  def p2 : Var := 16
  def xs2 : Var := 17
  def xs_j0 : Var := 18
  def x : Var := 19
  def x' : Var := 20
  def xs_i1 : Var := 21
  def xs_j1 : Var := 22
  def xs3 : Var := 23
  def xs4 : Var := 24
  def jadd1 : Var := 25
  def r2 : Var := 26

  def itranspose : IR.FnBody :=
    ilet one ≔ iapp mkOne @@ #[];
    ilet two ≔ iapp mkTwo @@ #[];
    ilet n ≔ iapp size @@ #[xs0];
    ilet b1 ≔ iapp geq @@ #[i, n];
    icase b1: #[
      ( iret xs0),
      ( ilet b2 ≔ iapp geq @@ #[j, n];
        icase b2: #[
          ( ilet iadd1 ≔ iapp add @@ #[i, one];
            ilet iadd2 ≔ iapp add @@ #[i, two];
            ilet r1 ≔ iapp transpose @@ #[xs0, iadd1, iadd2];
            iret r1),
          ( ilet empty1 ≔ iapp mkEmpty @@ #[];
            ilet empty2 ≔ iapp mkEmpty @@ #[];
            ilet p1 ≔ iapp swap @@ #[xs0, i, empty1];
            ilet xs1 ≔ iproj mkTuple#0 @@ p1;
            ilet xs_i0 ≔ iproj mkTuple#1 @@ p1;
            ilet p2 ≔ iapp swap @@ #[xs1, j, empty2];
            ilet xs2 ≔ iproj mkTuple#0 @@ p2;
            ilet xs_j0 ≔ iproj mkTuple#1 @@ p2;
            ilet x ≔ iapp get @@ #[xs_i0, j];
            ilet x' ≔ iapp get @@ #[xs_j0, i];
            ilet xs_i1 ≔ iapp set @@ #[xs_i0, j, x'];
            ilet xs_j1 ≔ iapp set @@ #[xs_j0, i, x];
            ilet xs3 ≔ iapp set' @@ #[xs2, i, xs_i1];
            ilet xs4 ≔ iapp set' @@ #[xs3, j, xs_j1];
            ilet jadd1 ≔ iapp add @@ #[j, one];
            ilet r2 ≔ iapp transpose @@ #[xs4, i, jadd1];
            iret r2)
        ])
    ]

  def program : IR.Program := Lean.RBMap.ofList [(transpose, ⟨3, itranspose⟩)]
  def funTypes : IR.FunTypeMap := Lean.RBMap.ofList [
    (transpose, #[
          .adt .unique Array #[.adt .unique Array #[.erased .shared]],
          .adt .shared Nat #[],
          .adt .shared Nat #[]
        ],
      .adt .unique Array #[.adt .unique Array #[.erased .shared]]
    ),
    (mkOne, #[], .adt .shared Nat #[]),
    (mkTwo, #[], .adt .shared Nat #[]),
    (size, #[.adt .shared Array #[.erased .shared]], .adt .shared Nat #[]),
    (geq, #[.adt .shared Nat #[], .adt .shared Nat #[]], .adt .shared Bool #[]),
    (add, #[.adt .shared Nat #[], .adt .shared Nat #[]], .adt .shared Nat #[]),
    (mkEmpty, #[], .adt .unique Array #[.erased .unique]),
    (swap, #[
          .adt .unique Array #[.adt .unique Array #[.erased .shared]], 
          .adt .shared Nat #[], 
          .adt .unique Array #[.erased .shared]
        ], 
      .adt .unique Prod #[.adt .unique Array #[.adt .unique Array #[.erased .shared]], .adt .unique Array #[.erased .shared]]),
    (get, #[
          .adt .shared Array #[.erased .shared],
          .adt .shared Nat #[]
        ],
      .erased .shared),
    (set, #[
          .adt .unique Array #[.erased .shared],
          .adt .shared Nat #[],
          .erased .shared
        ],
      .adt .unique Array #[.erased .shared]),
    (set', #[
          .adt .unique Array #[.erased .unique],
          .adt .shared Nat #[],
          .erased .unique
        ],
      .adt .unique Array #[.erased .unique])
  ]
  def adtDecls : Types.ADTDeclMap := Lean.RBMap.ofList [
    (Bool, .mk 0 #[] #[#[], #[]]),
    (Prod, .mk 0 #[0, 1] #[#[.typeVar 0, .typeVar 1]])
  ]
  def externUniqueFields : Types.ExternUniqueFieldsMap := Lean.RBMap.ofList [
    (Array, Types.externUniqueFieldsTreeOfArray #[
      ([(0, 0)], some 0)
    ])
  ]
  def externEscapees : IR.EscapeAnalysis.ExternEscapeeMap := Lean.RBMap.ofList [
    (size, #[]),
    (get, #[⟨0, [(0, 0)], none⟩])
  ]

  /-
  {
  1: ! 1 #[];
  2: ! 1 #[];
  3: ! 1 #[];
  4: ! 1 #[];
  5: ! 1 #[];
  6: ! 2 #[];
  7: ! 2 #[];
  13: * 3 #[* 0 #[*■], *■];
  15: ! 0 #[!■];
  16: * 3 #[* 0 #[*■], *■];
  17: * 0 #[*■];
  18: *■;
  19: !■;
  }
  20 ≔ app 8 #[18, 1]; ...
  -/

  #eval Checker.checkProgram program funTypes adtDecls externUniqueFields externEscapees
  #eval IO.println <| IR.EscapeAnalysis.run program externEscapees (IR.SCC.computeSCCs <| IR.CG.computeCallGraph <| program)

end Test.Array_transposeSquare

namespace Test.List_get
  def List_get? (xs : List α) (i : Nat) : Option α :=
    match xs with
    | [] => none
    | x :: xs =>
      match i == 0 with
      | true  => Option.some x
      | false => xs.get? i.pred

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
    (getList, #[.adt .shared iList #[.erased .shared], .adt .shared iNat #[]], .adt .unique iOption #[.erased .shared]),
    (mkZero, #[], .adt .shared iNat #[]),
    (natEq, #[.adt .shared iNat #[], .adt .shared iNat #[]], .adt .shared iBool #[]),
    (predNat, #[.adt .shared iNat #[]], .adt .shared iNat #[])
  ]
  def adtDecls : Types.ADTDeclMap := Lean.RBMap.ofList [
    (iList, .mk 0 #[1] #[#[], #[.typeVar 1, .selfVar .unique 0]]),
    (iOption, .mk 0 #[1] #[#[], #[.typeVar 1]])
  ]
  def externUniqueFields : Types.ExternUniqueFieldsMap := Lean.RBMap.empty
  def externEscapees : IR.EscapeAnalysis.ExternEscapeeMap := Lean.RBMap.empty

  #eval Checker.checkProgram program funTypes adtDecls externUniqueFields externEscapees
  def escapees : Checker.EscapeeMap := Id.run do
    let e := IR.EscapeAnalysis.run program externEscapees (IR.SCC.computeSCCs <| IR.CG.computeCallGraph <| program)
    let mut escapeeMap := Lean.RBMap.empty
    for ⟨c, funEscapees⟩ in e do
      let arity := (funTypes.find! c).1.size
      escapeeMap := escapeeMap.insert c (Checker.groupFunEscapeesByParam arity funEscapees)
    return escapeeMap
  #eval escapees
  def usages := Checker.inferUsages funTypes adtDecls (funTypes.find! getList).2 (program.find! getList).2
  def ctx : Checker.StaticContext := ⟨program, funTypes, adtDecls, escapees, externUniqueFields, usages⟩
  #eval ctx.isBorrowedIn getList 0 (.adt .unique iList #[.erased .shared])
end Test.List_get