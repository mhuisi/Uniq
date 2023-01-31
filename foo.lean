-- annotationen über mdata
-- an pap vs fapp kommt man über getArity
-- an extern informationen über inferType
-- τs so stark wie möglichkeit
-- Name → type durch getConstInfo
-- _rarg -> funktion verbindung durch call rekonstruieren

List α ≡ ⊤ ⊕ (α ⊗ List α)
map : ∀ p ≤ ⋆. p(List α) → !(α → β) → p(List β) := λ xs f.
  case xs of
    nil => nil
    cons =>
      let x := proj₀ xs
      let fx := f x
      let tail := proj₁ xs
      let tail' := map xs f
      let xs' := ctor_cons fx tail'
      ret xs'

get : List α → Int → α := λ xs i.
  case xs of
    nil => error
    cons =>
      let b := i == 0
      case b of
      false =>
        let xs' := proj₁ xs
        let prev := i - 1
        let r := get xs' prev
        ret r
      true =>
        let r := proj₀ xs
        ret r

nil   : *(UList α)
cons  : *(UList α) → !α → *(UList α)
!cons : !(UList α) → !α → !(UList α)
head  : *(UList α) → !α
!head : !(UList α) → !α
tail  : *(UList α) → *(UList α)
!tail : !(UList α) → !(UList α)
match : *(UList α) → (() → β) → (!α → *(UList α) → β) → β
!match: !(UList α) → (() → β) → (!α → !(UList α) → β) → β
get   : *(UList α) → !Int → *(UList α)
!get  : !(UList α) → !Int → !(UList α)
lend  : UList α → Int → (UList α → β ⊗ UList α) → β ⊗ UList α
map   : *(UList α) → !(α → β) → *(UList α)
!map  : !(UList α) → !(α → β) → !(UList α)

------------------------------------------------------------------------------------------------------------

IR:

Variablen w, x, y, z
Const c
Ausdrücke e: c [y] | pap c [y] | y z | (A [τ]).ctorᵢ [y] | projᵢⱼ y
FnBody F: ret x | let x = e; F | case x of [F] | case' x of [ctorᵢ [y] ⇒ F]
Fn f: λ [y]. F
Programm δ : Const → Fn

------------------------------------------------------------------------------------------------------------

Typen:

-- TODO:
-- (inference, LCNF abgleichen)
-- Beispiele rechnen
-- Implementieren!

Modalitäten m: !, *

ADTs a: μ x_κ_adt. [[τ_field(x_κ_adt, y_τ)] → *x_κ_adt]
  mit FV_τ(a) = y_τ

ADT-Konstanten A

ADT-Deklarationen γ : A ⇀ a
  mit ∀ A ∈ dom(γ). is_fully_propagated(γ(A))

Attributierte Typen τ: m x_κ | x_τ | m ◾ | m A [τ_arg] | ! [τ_param] → τ_ret
  mit |FV_τ(γ(A))| = |[τ_arg]|

Funktionstypen δ_τ : c ⇀ ([τ] → τ)
  mit ∀ Const c mit δ_τ(c) = [τ_param] → τ_ret.
    ⋀ [is_fully_propagated(τ_param)] ∧ is_fully_propagated(τ_ret) ∧
    ⋀ [¬ contains_invalid_function_annotation(τ_param)] ∧ ¬ contains_invalid_function_annotation(τ_ret)

contains_invalid_function_annotation(x_τ | m x_κ) = true
contains_invalid_function_annotation(m ◾)         = false
contains_invalid_function_annotation(m A [τ_arg]) =
  ⋁ [contains_invalid_function_annotation(τ_arg)]
contains_invalid_function_annotation(! [τ_param] → τ_ret) =
  ⋁ [contains_invalid_function_annotation(τ_param)] ∨ contains_invalid_function_annotation(τ_ret)

propagate(m x_κ, true)                       = ! x_κ
propagate(m x_κ, false)                      = m x_κ
propagate(x_τ, _)                            = x_τ
propagate(m ◾, true)                         = ! ◾
propagate(m ◾, false)                        = m ◾
propagate(m A [τ_arg], true)                 = ! A [propagate(τ_arg, true)]
propagate(! A [τ_arg], false)                = ! A [propagate(τ_arg, true)]
propagate(* A [τ_arg], false)                = * A [propagate(τ_arg, false)]
propagate(! [τ_param] → τ_ret, _)            = ! [propagate(τ_param, true)] → propagate(τ_ret, true)
propagate(τ)                                 = propagate(τ, false)
propagate(μ x_κ_adt. [[τ_field] → *x_κ_adt]) = μ x_κ_adt. [[propagate(τ_field)] → *x_κ_adt]
is_fully_propagated(x)                       = (propagate(x, false) = x)

τ_field(·, ·) := propagate(τ_field[x_κ_adt ↦ ·, y_τ ↦ ·])

!(m ◾)                 = ! ◾
!(m A [τ_arg])         = propagate(! A [τ_arg])
!(! [τ_param] → τ_ret) = ! [τ_param] → τ_ret

m(m x_κ)               = m
m(m ◾)                 = m
m(m A [τ_arg])         = m
m(! [τ_param] → τ_ret) = !

Escapees y: x | yᵢⱼ

var_of_escapee(x) = x
var_of_escapee(yᵢⱼ) = var_of_escapee(y)
projs_of_escapee(x) = []
projs_of_escapee(yᵢⱼ) = projs_of_escapee(y) ++ [(i, j)]
y_[] = y
y_(i, j)::projs = yᵢⱼ_projs
convert_escapee(y, y') = var_of_escapee(y')_projs_of_escapee(y)
subsumes(y, y') = ∃ suffix. |suffix| > 1 ∧ projs_of_escapee(y) = projs_of_escapee(y') ++ suffix

params_to_args(M, [param], [arg]) =
  { convert_escapee(y, [arg]ᵢ) : y ∈ M ∧ ∃ i. [param]ᵢ = var_of_escapee(y) }

app_escapees(c, [y]) = params_to_args(escapees(F), [y'], [y])
  where δ(c) = λ [y']. F

erase_subsumed(M) = M\{y ∈ M : ∃ y' ∈ M. subsumes(y', y)}
M ⊔ N = erase_subsumed(M ∪ N)

escapees(ret x) = {x}
escapees(case x of [F]) = ⋃ [escapees(F)]
escapees(case' x of [ctorᵢ [y] ⇒ F]) =
  ⋃ [escapees(F) ∪ {xᵢⱼ : [y]ⱼ ∈ escapees(F)} ∪ {xᵢⱼₖₗ : [y]ⱼₖₗ ∈ escapees(F)}]
escapees(let x = c [y]; F) =
  escapees(F) ∪ {
    app_escapees(c, [y]) if x ∈ escapees(F) ∨ ∃ i j. xᵢⱼ ∈ escapees(F)
    ∅                    otherwise
  }
escapees(let x = pap c [y]; F) =
  escapees(F) ∪ {
    ⋃ [y]                if x ∈ escapees(F)
    app_escapees(c, [y]) if ∃ i j. xᵢⱼ ∈ escapees(F)
    ∅                    otherwise
  }
escapees(let x = y z; F) =
  escapees(F) ∪ {
    {y, z} if x ∈ escapees(F) ∨ ∃ i j. xᵢⱼ ∈ escapees(F)
    ∅      otherwise
  }
escapees(let x = (A [τ]).ctorᵢ [y]; F) =
  escapees(F) ∪ {
    ⋃ [y]                      if x ∈ escapees(F)
    {[y]ⱼ : xᵢⱼ ∈ escapees(F)} otherwise
  }
escapees(let x = projᵢⱼ y; F) =
  escapees(F) ∪ {
    yᵢⱼ                       if x ∈ escapees(F)
    {yᵢⱼₖₗ : xₖₗ ∈ escapees(F)} otherwise
  }

Escapende Variablen & Felder escapes_in : Var × Const ⇀ 𝔹
  mit ∀ c ∈ dom(δ). escapes_in(⬝, c) = ⬝ ∈ escapees(F) mit δ(c) = λ [y]. F

Beinhaltete eindeutige Felder ε : A ⇀ 2^([ℕ × ℕ] × (* | ∅))
  mit ∀ A ∈ dom(γ). ε(A) = unique_fields_in(γ(A))

unique_fields_in(μ x_κ_adt. [c])          = ⋃ {unique_fields_in(i, j, [τ_field]ⱼ) : j ∧ [c]ᵢ = [τ_field] → *x_κ_adt}
unique_fields_in(i, j, * ◾ | * x_κ)       = {[((i, j)], *)}
unique_fields_in(i, j, x_τ)               = {([(i, j)], ∅)}
unique_fields_in(i, j, * A [τ_arg])       = {([(i, j)], ∅)} ∪ {(i, j)::field : field ∈ ε(A)}
unique_fields_in(i, j, _)                 = ∅
unique_fields_in(! A [τ_arg])             = ε(A)
unique_fields_in(_)                       = ∅

is_borrowed_in(c, i) =
    ∧ ¬escapes_in([y]ᵢ, c)
    ∧ [τ_param]ᵢ ∈ dom(unique_fields_in) -- every ADT in [τ_param]ᵢ defined in ε -- TODO: Clean this up
    ∧ m([τ_param]ᵢ) = !
    ∧ ∀ (field, tag) ∈ unique_fields_in([τ_param]ᵢ).
      (tag = ∅ ⇒ ¬escapes_in([y]ᵢ_field, c)) ∧
      (tag = * ⇒ ∀ suffix. ¬escapes_in([y]ᵢ_field++suffix, c)))
  mit δ_τ(c) = [τ_param] → τ_ret

applicable_to_mod_borrowing(!◾, !◾) = true
applicable_to_mod_borrowing(! [τ_param] → τ_ret, ! [τ_param] → τ_ret) = true
applicable_to_mod_borrowing(m A [τ_arg], m' A [τ_arg']) =
  m = * ∧ m' = ! ∧ ∀ i. applicable_to_mod_borrowing([τ_arg]ᵢ, [τ_arg']ᵢ)

applicable_to_mod_borrowing([τ₁'], [τ_param], τ_ret) =
  ∀ i.
    (is_borrowed_in(c, i)  ⇒ applicable_to_mod_borrowing([τ₁']ᵢ, [τ_param]ᵢ)) ∧
    (¬is_borrowed_in(c, i) ⇒ [τ₁']ᵢ = [τ_param]ᵢ)

is_downcasted(m ◾, ! ◾)                                 = true
is_downcasted(! [τ_param] → τ_ret, ! [τ_param] → τ_ret) = true
is_downcasted(m A [τ_arg], !(m A [τ_arg]))              = true
is_downcasted(m A [τ_arg], m A [τ_arg'])                = ∃ i. [τ_arg'] = [τ_arg][i ↦ ![τ_arg]ᵢ]

------------------------------------------------------------------------------------------------------------

Typsystem:

Prädikate:
  ⊢ δ_τ
  ⊢ c : [τ_param] → τ_ret
  ⊢ λ [y]. F : [τ_param] → τ_ret
  Z; Γ ⊢ F : τ_ret mit Z : Variable × ℕ × ℕ → 𝔹 und Γ ⊆ Variable × Attributierter Typ

zero(Z, x, i, j, ! A [τ_arg]) = Z
zero(Z, x, i, j, * A [τ_arg]) = {
  Z[(x, i, j) ↦ true] falls m([τ_field]ⱼ(A [τ_arg], [τ_arg])) = *
  Z                    sonst
}
  mit
    γ(A) = μ x_κ_adt. [c]
    [c]ᵢ = [τ_field] → *x_κ_adt

nonzero(Z, x) = ∀ i j. ¬Z(x, i, j)

Program
  ∀ c ∈ dom(δ_τ). ⊢ c : δ_τ(c)
⊢ δ_τ

Const
  ⊢ δ(c) : [τ_param] → τ_ret
⊢ c : [τ_param] → τ_ret

Fn
  const false; [y : τ_param] ⊢ F : τ_ret
⊢ λ [y]. F : [τ_param] → τ_ret

Forget
  Z; Γ ⊢ F : τ_ret'
Z; Γ, x : τ ⊢ F : τ_ret'

Duplicate
  Z; Γ, x : !τ, x : !τ ⊢ F : τ_ret'
Z; Γ, x : !τ ⊢ F : τ_ret'

Downcast
  nonzero(Z, x)
  is_downcasted(* A [τ_arg], τ)
  Z; Γ, x : τ ⊢ F : τ_ret'
Z; Γ, x : * A [τ_arg] ⊢ F : τ_ret'

◾-Downcast-Left
  Z; Γ, x : m(τ) ◾ ⊢ F : τ_ret'
Z; Γ, x : τ ⊢ F : τ_ret'

◾-Upcast-Left
  Z; Γ, x : τ ⊢ F : τ_ret'
Z; Γ, x : m(τ) ◾ ⊢ F : τ_ret'

◾-Downcast-Right
  Z; Γ ⊢ F : τ_ret'
Z; Γ ⊢ F : m(τ_ret') ◾

◾-Upcast-Right
  Z; Γ ⊢ F : m(τ_ret') ◾
Z; Γ ⊢ F : τ_ret'

Ret
  nonzero(Z, x)
Z; x : τ_ret' ⊢ ret x : τ_ret'

Let-ConstApp
  [nonzero(Z, y)]
  δ_τ(c) = [τ_param] → τ_ret
  applicable_to_mod_borrowing([τ_param'], [τ_param], τ_ret)
  Z; Γ, [ [y : τ_param']ᵢ | i ∈ [0, |[y]|) ∧ is_borrowed_in(c, i) ], x : τ_ret ⊢ F : τ_ret'
Z; Γ, [y : τ_param'] ⊢ let x = c [y]; F : τ_ret'

Let-Pap
  [nonzero(Z, y)]
  δ_τ(c) = [τ_param] → τ_ret
  |[τ_param₁]| < |[τ_param]|
  [τ_param₁] ++ [τ_param₂] = [τ_param]
  Z; Γ, x : ! [τ_param₂] → τ_ret ⊢ F : τ_ret'
Z; Γ, [y : !τ_param₁] ⊢ let x = pap c [y]; F : τ_ret'

Let-Pap-Apply
  [nonzero(Z, y)]
  δ_τ(c) = [τ_param] → τ_ret
  Z; Γ, x : !τ_ret ⊢ F : τ_ret'
Z; Γ, [y : !τ_param] ⊢ let x = pap c [y]; F : τ_ret'

Let-VarApp-Pap
  nonzero(Z, z)
  |[τ_param]| >= 2
  τ_param₁ :: [τ_param₂] = [τ_param]
  Z; Γ, x : ! [τ_param₂] → τ_ret ⊢ F : τ_ret'
Z; Γ, z : !τ_param₁, y : ! [τ_param] → τ_ret ⊢ let x = y z; F : τ_ret'

Let-VarApp-Apply
  nonzero(Z, z)
  Z; Γ, x : !τ_ret ⊢ F : τ_ret'
Z; Γ, z : !τ_param, y : ! τ_param → τ_ret ⊢ let x = y z; F : τ_ret'

Let-Ctor
  [nonzero(Z, y)]
  γ(A) = μ x_κ_adt. [c]
  [c]ᵢ = [τ_field] → *x_κ_adt
  Z; Γ, x : * A [τ_arg] ⊢ F : τ_ret'
Z; Γ, [y : τ_field(A [τ_arg], [τ_arg])] ⊢ let x = (A [τ_arg]).ctorᵢ [y]; F : τ_ret'

Let-Proj
  γ(A) = μ x_κ_adt. [c]
  [c]ᵢ = [τ_field] → *x_κ_adt
  ¬ Z(y, i, j) -- TODO: make shared
  zero(Z, y, i, j, m A [τ_arg]); Γ, y : m A [τ_arg], x : [τ_field]ⱼ(A [τ_arg], [τ_arg]) ⊢ F : τ_ret'
Z; Γ, y : m A [τ_arg] ⊢ let x = projᵢⱼ y; F : τ_ret'

Case
  nonzero(Z, x)
  [Z; Γ, x : m A [τ_arg] ⊢ F : τ_ret']
Z; Γ, x : m A [τ_arg] ⊢ case x of [F] : τ_ret'

Case'
  nonzero(Z, x)
  γ(A) = μ x_κ_adt. [c]
  [c]ᵢ = [τ_field] → *x_κ_adt -- TODO: make shared
  [Z; Γ, [y : τ_field(A [τ_arg], [τ_arg])] ⊢ F : τ_ret']
Z; Γ, x : m A [τ_arg] ⊢ case' x of [ctorᵢ [y] ⇒ F] : τ_ret'