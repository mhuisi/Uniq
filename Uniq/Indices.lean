def Const   := Nat deriving BEq, Inhabited, Ord, Repr, ToString
def Var     := Nat deriving BEq, Inhabited, Ord, Repr, ToString
def Ctor    := Nat deriving BEq, Inhabited, Ord, Repr, ToString
def Proj    := Nat deriving BEq, Inhabited, Ord, Repr, ToString
def ADTName := Nat deriving BEq, Inhabited, Ord, Repr, ToString

instance : OfNat Const n where
  ofNat := n

instance : OfNat Var n where
  ofNat := n

instance : OfNat Ctor n where
  ofNat := n

instance : OfNat Proj n where
  ofNat := n

instance : OfNat ADTName n where
  ofNat := n