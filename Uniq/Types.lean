import Lean.Data.RBMap
import Lean.Data.PrefixTree
import Uniq.Indices

namespace Types
  inductive Attr where
    | shared
    | unique
  deriving BEq, Inhabited

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
    | selfVar _ var,        true  => selfVar .shared var
    | selfVar attr var,     false => selfVar attr var
    | typeVar var,          _     => typeVar var
    | erased _,             true  => erased .shared
    | erased attr,          false => erased attr
    | adt _ name args,      true  => adt .shared name (args.map (propagateAux · true))
    | adt .shared name args, false => adt .shared name (args.map (propagateAux · true))
    | adt .unique name args, false => adt .unique name (args.map (propagateAux · false))
    | func params ret,      _     => func (params.map (propagateAux · true)) (propagateAux ret true)

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

  def AttrType.isShared : AttrType → Bool := (·.attr == .shared)
  def AttrType.isUnique : AttrType → Bool := (·.attr == .unique)

  inductive FieldTag where
    | all
    | only

  structure UniqueField where
    path : List (Ctor × Proj)
    tag  : FieldTag

  instance : Ord (Ctor × Proj) := lexOrd

  abbrev ExternUniqueFieldsTree := Lean.PrefixTree (Ctor × Proj) Unit compare

  def ExternUniqueFieldsTree.isUniqueField (tree : ExternUniqueFieldsTree) (path : List (Ctor × Proj)) : Bool :=
    loop tree.val path
  where
    loop : Lean.PrefixTreeNode (Ctor × Proj) Unit → List (Ctor × Proj) → Bool
      | _, [] | .Node _ .leaf, _ => true
      | .Node _ children, field :: rest =>
        children.find compare field |>.map (loop · rest) |>.getD false

  abbrev ExternUniqueFieldsMap := Lean.RBMap ADTName ExternUniqueFieldsTree compare

  mutual
    def isUniqueFieldInADT (adtDecls : ADTDeclMap) (externUniqueFields : ExternUniqueFieldsMap) (adtName : ADTName) : List (Ctor × Proj) → Bool
      | [] => true
      | ⟨i, j⟩ :: rest =>
        match adtDecls.find? adtName with
        | some (.mk _ _ ctors) =>
          let i : Nat := i
          let j : Nat := j
          isUniqueField adtDecls externUniqueFields (ctors[i]![j]!) rest
        | none => Id.run do
          let some externUniqueFields := externUniqueFields.find? adtName
            | return true
          externUniqueFields.isUniqueField (⟨i, j⟩ :: rest)


    def isUniqueField (adtDecls : ADTDeclMap) (externUniqueFields : ExternUniqueFieldsMap) : AttrType → List (Ctor × Proj) → Bool
      | erased .unique, _ | selfVar .unique _, _ => true
      -- This is not strictly correct, but it is correct in the scope where the function is used.
      -- `isUniqueField` is only used on ADT parameters that are elligible for borrowing,
      -- i.e. shared, which makes every type parameter shared, too. Hence, type variables in the
      -- context of this function can never be unique.
      | typeVar _, _ => false
      | adt .unique name _, field =>
        isUniqueFieldInADT adtDecls externUniqueFields name field
      | _, _ => false
  end
end Types