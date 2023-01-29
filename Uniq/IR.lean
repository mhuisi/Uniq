import Lean.Data.RBTree
import Uniq.Types

namespace IR
  inductive Expr where
    | app (c : Const) (args : Array Var)
    | papp (c : Const) (args : Array Var)
    | vapp (x y : Var)
    | ctor (adtName : ADTName) (typeParams : Array Types.AttrType) (ctor : Ctor) (params : Array Var)
    | proj (ctor : Ctor) (proj : Proj) (var : Var)
  deriving Inhabited

  inductive FnBody where
    | ret   (var : Var)
    | «let» (var : Var) (expr : Expr) (rest : FnBody)
    | case  (var : Var) (cases : Array FnBody)
    | case' (var : Var) (cases : Array (Ctor × Array Var × FnBody))
  deriving Inhabited

  structure Function where
    params : Array Var
    body   : FnBody
  deriving Inhabited

  abbrev Program    := Lean.RBMap Const Function compare
  abbrev FunTypeMap := Lean.RBMap Const (Array Types.AttrType × Types.AttrType) compare
end IR