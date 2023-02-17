import Lean.Data.RBMap
import Lean.Data.PrefixTree
import Uniq.Indices

namespace Types
  inductive Attr where
    | shared
    | unique
  deriving BEq, Inhabited

  instance : ToString Attr where
    toString attr := match attr with
      | .shared => "!"
      | .unique => "*"

  mutual
    inductive ADT where
      | mk (selfVar : Var) (typeVars : Array Var) (ctors : Array (Array AttrType))
    deriving BEq, Inhabited

    inductive AttrType where
      | selfVar (attr : Attr) (var : Var)
      | typeVar (var : Var)
      | erased  (attr : Attr)
      | adt     (attr : Attr) (name : ADTName) (args : Array AttrType)
      | func    (params : Array AttrType) (ret : AttrType)
    deriving BEq, Inhabited
  end

  def ADT.selfVar : ADT → Var
    | .mk selfVar _ _ => selfVar

  def ADT.typeVars : ADT → Array Var
    |.mk _ typeVars _ => typeVars

  def ADT.ctors : ADT → Array (Array AttrType)
    |.mk _ _ ctors => ctors

  partial def printAttrType : AttrType → String
    | .selfVar attr var => toString attr ++ toString var
    | .typeVar var => toString var
    | .erased attr => s!"{attr}■"
    | .adt attr name args => s!"{attr} {name} {args.map (printAttrType ·)}"
    | .func params ret => s!"!({params.map (printAttrType ·)} → {printAttrType ret})"

  instance : ToString AttrType where
    toString type := printAttrType type

  abbrev ADTDeclMap := Lean.RBMap ADTName ADT compare

  open AttrType

  partial def containsInvalidFunctionAnnotation : AttrType → Bool
    | typeVar .. | selfVar .. => true
    | erased ..               => false
    | adt _ _ args =>
      args.any containsInvalidFunctionAnnotation
    | func params ret =>
      params.any containsInvalidFunctionAnnotation || containsInvalidFunctionAnnotation ret

  partial def propagateAux : AttrType → Bool → AttrType
    | selfVar _ var,        true   => selfVar .shared var
    | selfVar attr var,     false  => selfVar attr var
    | typeVar var,          _      => typeVar var
    | erased _,             true   => erased .shared
    | erased attr,          false  => erased attr
    | adt _ name args,      true   => adt .shared name (args.map (propagateAux · true))
    | adt .shared name args, false => adt .shared name (args.map (propagateAux · true))
    | adt .unique name args, false => adt .unique name (args.map (propagateAux · false))
    | func params ret,      _      => func (params.map (propagateAux · true)) (propagateAux ret true)

  def AttrType.propagate := (propagateAux · false)

  def AttrType.isFullyPropagated (type : AttrType) : Bool :=
    propagate type == type

  partial def AttrType.substRawAux (type : AttrType) (substVar : Var) (substituted : AttrType) :=
    match type with
    | selfVar attr var =>
      if var == substVar then
        match substituted with
        | selfVar _ var   => selfVar attr var
        | typeVar _       => panic! "cannot substitute in typeVar raw"
        | erased _        => erased attr
        | adt _ name args => adt attr name args
        | func _ _        => panic! "cannot substitute in func raw"
      else
        selfVar attr var
    | typeVar var        => typeVar var
    | erased attr        => erased attr
    | adt attr name args => adt attr name (args.map (substRawAux · substVar substituted))
    | func params ret    => func (params.map (substRawAux · substVar substituted)) (substRawAux ret substVar substituted)

  def AttrType.substRaw (type : AttrType) (substVar : Var) (substituted : AttrType) :=
    type.substRawAux substVar substituted |>.propagate

  partial def AttrType.substAux (type : AttrType) (substVar : Var) (substituted : AttrType) :=
    match type with
    | selfVar attr var   => selfVar attr var
    | typeVar var        => if var == substVar then substituted else typeVar var
    | erased attr        => erased attr
    | adt attr name args => adt attr name (args.map (substAux · substVar substituted))
    | func params ret    => func (params.map (substAux · substVar substituted)) (substAux ret substVar substituted)

  def AttrType.subst (type : AttrType) (substVar : Var) (substituted : AttrType) :=
    type.substAux substVar substituted |>.propagate

  def ADT.subst (adt : ADT) (name : ADTName) (paramTypes : Array AttrType) : ADT :=
    assert! paramTypes.size == adt.typeVars.size
    let ctors := adt.ctors.map fun ctor => ctor.map fun field => Id.run do
      let mut field := field
      for p in adt.typeVars.zip paramTypes do
        field := field.subst p.1 p.2
      -- "unique" is ignored, substRaw uses the attr designated in the field
      field := field.substRaw adt.selfVar (.adt .unique name paramTypes)
      return field
    ADT.mk adt.selfVar adt.typeVars ctors

  partial def AttrType.strengthen : AttrType → AttrType
    | .selfVar _ var   => .selfVar .unique var
    | .typeVar var     => .typeVar var
    | .erased _        => .erased .unique
    | .adt _ name args => .adt .unique name (args.map strengthen)
    | .func params ret => func params ret

  def ADT.computeCtorParamTypes (adt : ADT) (explicitParamTypes : Array (Option AttrType)) (inferredParamTypes : Lean.RBMap Var AttrType compare) : Option (Array AttrType) := do
    let mut paramTypesAsArray := #[]
    for p in adt.typeVars.zip explicitParamTypes do
      let typeVar := p.1
      let explicitParamType? := p.2
      -- Inferred types are always better than explicit types
      if let some inferredParamType := inferredParamTypes.find? typeVar then
        paramTypesAsArray := paramTypesAsArray.push inferredParamType
      else
        -- The type of this typeVar couldn't be inferred,
        -- so it doesn't appear in any of the constructor args.
        -- Because of this, we can set all the attributes in the
        -- user-provided param type to "unique". I'm sure the user
        -- won't mind that we make their types stronger than they specified.
        paramTypesAsArray := paramTypesAsArray.push (← explicitParamType?).strengthen
    return paramTypesAsArray

  def AttrType.makeShared
    | erased _          => erased .shared
    | adt _ name params => propagate (adt .shared name params)
    | func params ret   => func params ret
    | selfVar _ var     => selfVar .shared var
    | typeVar var       => typeVar var

  def AttrType.attr : AttrType → Attr
    | selfVar attr _ => attr
    | typeVar _      => panic! "typeVar has no attr"
    | erased attr    => attr
    | adt attr ..    => attr
    | func ..        => .shared

  def AttrType.isTypeVar : AttrType → Bool := (· matches .typeVar _)
  def AttrType.isShared  : AttrType → Bool := (·.attr == .shared)
  def AttrType.isUnique  : AttrType → Bool := (·.attr == .unique)

  def AttrType.attrApplicableTo (a b : Types.AttrType) : Bool :=
    a.isTypeVar || b.isTypeVar || a.isUnique || a.isShared && b.isShared

  def mergeUnifiedVars (a b : Lean.RBMap Var AttrType compare) : Option (Lean.RBMap Var AttrType compare) := do
    let mut r := a
    for ⟨var, type⟩ in b do
      guard <| !r.contains var || r.find! var == type
      r := r.insert var type
    return r

  partial def AttrType.unifyWith (a b : Types.AttrType) : Option (Lean.RBMap Var AttrType compare) :=  do
    if !attrApplicableTo a b then
      .none
    match a, b with
    | a, .typeVar varB =>
      return Lean.RBMap.ofList [(varB, a)]
    | _, .selfVar .. =>
      -- This is not strictly correct (a may not necessarily be applicable to the selfVar)
      -- but it is correct in the context where this function is used -
      -- when determining the typeVars for a ctor call, in which case
      -- we will be fine if we just check the applicability of the fully substituted
      -- types again afterwards.
      return Lean.RBMap.empty
    | .erased _, b => erasedApplicableToModOuterAttr b
    | _, .erased _ => return Lean.RBMap.empty
    | .adt _ nameA argsA, .adt _ nameB argsB =>
      guard <| nameA == nameB && argsA.size == argsB.size
      let mut r := Lean.RBMap.empty
      for ⟨argA, argB⟩ in argsA.zip argsB do
        r ← mergeUnifiedVars r (← unifyWith argA argB)
      return r
    | .func paramsA retA, .func paramsB retB =>
      guard <| paramsA.size == paramsB.size
      let mut r ← unifyWith retA retB
      for ⟨paramA, paramB⟩ in paramsA.zip paramsB do
        r ← mergeUnifiedVars r (← unifyWith paramA paramB)
      return r
    | _, _ => .none
  where
    erasedApplicableToModOuterAttr : Types.AttrType → Option (Lean.RBMap Var AttrType compare)
      | .erased _ | .selfVar .. | .typeVar .. | .func .. => some Lean.RBMap.empty
      | .adt _ _ args => do
        guard <| args.all fun arg => arg.makeShared == arg
        return Lean.RBMap.empty

  instance : Ord (Ctor × Proj) := lexOrd

  -- implicit assumptions:
  -- - the tree is not simply a leaf
  -- - only leafs contain typeVars
  abbrev ExternUniqueFieldsTree := Lean.PrefixTree (Ctor × Proj) (Option Var) compare

  inductive ExternUniqueFieldResult
    | unique
    | maybeUnique (restPath : List (Ctor × Proj)) (typeVar : Var)
    | shared

  def ExternUniqueFieldsTree.isUniqueField (tree : ExternUniqueFieldsTree) (path : List (Ctor × Proj)) : ExternUniqueFieldResult  :=
    loop tree.val path
  where
    loop : Lean.PrefixTreeNode (Ctor × Proj) (Option Var) → List (Ctor × Proj) → ExternUniqueFieldResult
      | .Node (.some (.some var)) .leaf, [] => .maybeUnique [] var
      | .Node .., [] => .unique
      | .Node (.some (.some var)) .leaf, rest => .maybeUnique rest var
      | .Node _ .leaf, _ => .unique
      | .Node _ children, field :: rest =>
        children.find compare field |>.map (loop · rest) |>.getD .shared

  abbrev ExternUniqueFieldsMap := Lean.RBMap ADTName ExternUniqueFieldsTree compare

  partial def isUniqueField (adtDecls : ADTDeclMap) (externUniqueFields : ExternUniqueFieldsMap) : AttrType → List (Ctor × Proj) → Bool
    | erased .unique, _ | selfVar .unique _, _ => true
    | adt .unique name args, field =>
      match field, adtDecls.find? name with
      | [], _ => true
      | ⟨i, j⟩ :: rest, some adtDecl =>
        let adtDecl := adtDecl.subst name args
        let i : Nat := i
        let j : Nat := j
        isUniqueField adtDecls externUniqueFields adtDecl.ctors[i]![j]! rest
      | ⟨i, j⟩ :: rest, none => Id.run do
        let some externUniqueFieldsTree := externUniqueFields.find? name
          | return true
        match externUniqueFieldsTree.isUniqueField (⟨i, j⟩ :: rest) with
        | .unique => true
        | .shared => false
        | .maybeUnique restPath var =>
          let arg : Nat := var
          let argType := args[arg - 1]! -- we assume that the typeVars are numbered by [1, |arity|]
          isUniqueField adtDecls externUniqueFields argType restPath
    | _, _ => false
end Types