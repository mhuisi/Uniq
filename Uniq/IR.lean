import Lean.Data.RBTree
import Uniq.Types

namespace IR
  inductive Expr where
    | app (c : Const) (args : Array Var)
    | papp (c : Const) (args : Array Var)
    | vapp (x y : Var)
    | ctor (adtName : ADTName) (typeParams : Array (Option Types.AttrType)) (ctor : Ctor) (params : Array Var)
    | proj (adtName : ADTName) (ctor : Ctor) (proj : Proj) (var : Var)
  deriving Inhabited

  def printExpr : Expr → String
    | .app c args => s!"app {c} {args}"
    | .papp c args => s!"papp {c} {args}"
    | .vapp x y => s!"vapp {x} {y}"
    | .ctor adtName typeParams ctor params => s!"ctor {adtName} {typeParams} {ctor} {params}"
    | .proj adtName ctor proj var => s!"proj {adtName} {ctor} {proj} {var}"

  instance : ToString Expr where
    toString := printExpr

  inductive FnBody where
    | ret   (var : Var)
    | «let» (var : Var) (expr : Expr) (rest : FnBody)
    | case  (var : Var) (cases : Array FnBody)
    | case' (adtName : ADTName) (var : Var) (cases : Array (Ctor × Array Var × FnBody))
  deriving Inhabited

  partial def printFnBody : FnBody → String
    | .ret var => s!"ret {var}"
    | .«let» var expr rest => s!"{var} ≔ {expr}; {printFnBody rest}"
    | .case var cases => s!"\ncase {var}:\n{cases.map printFnBody |>.data |> String.intercalate ";\n"}"
    | .case' adtName var cases => s!"\n{adtName}.case' {var}:\n{cases.map (fun (ctor, fields, case) => s!"{ctor} {fields} => {printFnBody case}") |>.data |> String.intercalate ";\n"}"

  def FnBody.printHead : FnBody → String
    | .ret var => s!"ret {var}"
    | .«let» var expr _ => s!"{var} ≔ {expr}; ..."
    | .case var _ => s!"case {var}: ..."
    | .case' adtName var _ => s!"{adtName}.case' {var}: ..."

  instance : ToString FnBody where
    toString := printFnBody

  notation "iret " t1 => FnBody.ret t1
  notation "icase " t1 ": " t2 => FnBody.case t1 t2
  notation t0 "․icase' " t1 ": " t2 => FnBody.case' t0 t1 t2
  notation "ilet " t1 " ≔ " t2 "; " rest => FnBody.«let» t1 t2 rest

  structure Function where
    arity : Nat
    body  : FnBody
  deriving Inhabited

  abbrev Program    := Lean.RBMap Const Function compare
  abbrev FunTypeMap := Lean.RBMap Const (Array Types.AttrType × Types.AttrType) compare
end IR