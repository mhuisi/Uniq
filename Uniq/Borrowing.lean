import Uniq.EscapeAnalysis
  
namespace Borrowing
  def groupFunEscapeesByParam 
    (arity       : Nat) 
    (funEscapees : Array IR.EscapeAnalysis.Escapee) 
    : Array (Array IR.EscapeAnalysis.Escapee) := Id.run do
    let mut r := mkArray arity #[]
    for escapee in funEscapees do
      r := r.modify escapee.var (·.push escapee)
    return r

  abbrev BorrowedParamMap := Lean.RBMap Const (Lean.RBTree Nat compare) compare

  def computeBorrowedParams 
    (adtDecls           : Types.ADTDeclMap) 
    (externUniqueFields : Types.ExternUniqueFieldsMap) 
    (funTypes           : IR.FunTypeMap) 
    (escapees           : Lean.RBMap Const (Array IR.EscapeAnalysis.Escapee) compare) 
    : BorrowedParamMap := Id.run do
    let mut borrowedParams := Lean.mkRBMap _ _ _
    for ⟨c, paramTypes, _⟩ in funTypes do
      let some funEscapees := escapees.find? c
        | continue
      let funEscapees := groupFunEscapeesByParam paramTypes.size funEscapees
      let mut borrowed := Lean.mkRBTree _ _
      for i in [0:paramTypes.size] do
        let paramEscapes := funEscapees[i]!.contains ⟨i, []⟩ -- params are vars [0, |arity|)
        let paramTypeShared := paramTypes[i]!.isShared
        let noFieldsEscape :=
          if let .adt _ name _ := paramTypes[i]! then
            funEscapees[i]!.all fun escapee =>
              !Types.isUniqueFieldInADT adtDecls externUniqueFields name escapee.field
          else
            true
        if !paramEscapes && paramTypeShared && noFieldsEscape then
          borrowed := borrowed.insert i
      borrowedParams := borrowedParams.insert c borrowed
    return borrowedParams
end Borrowing