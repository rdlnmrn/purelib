module

public import Purelib.Polynomial.Multivariate.Sparse
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Checked constant coefficient views

Inspection returns an exact constant certificate or the actual remaining
formal variable terms. The variable cases request additional relations between
the original bindings; they establish no inequality of numerical values.
-/

public section

namespace Purelib.Polynomial.Multivariate.Sparse

variable {R : Type} [Zero R] [Add R] [DecidableEq R] {arity : Nat}

set_option genInjectivity false in
/-- A canonical polynomial's exact constant reading or its retained formal variable terms. -/
inductive ConstantView (polynomial : Sparse R arity) where
  /-- Retain the exact coefficient and a proof of the whole constant normal form. -/
  | exact (value : R) (terms_eq : polynomial.terms = (constant value).terms)
  /-- Retain an actual single term whose original monomial contains variable exponents. -/
  | variable (term : Term R arity) (terms_eq : polynomial.terms = [term])
      (monomial_ne : term.monomial ≠ Monomial.zero arity)
  /-- Retain the actual ordered term list when more than one formal monomial remains. -/
  | multiple (first second : Term R arity) (remaining : List (Term R arity))
      (terms_eq : polynomial.terms = first :: second :: remaining)

constructive_injectivity ConstantView

/-- The inspected coefficient form retains formal variable terms instead of an exact constant. -/
@[expose] def ConstantView.Nonconstant {polynomial : Sparse R arity} : ConstantView polynomial → Prop
  | .exact _ _ => False
  | .variable _ _ _ => True
  | .multiple _ _ _ _ => True

/-- Inspect canonical coefficients, returning an authenticated constant or precise remaining formal terms. -/
@[expose] def constantView (polynomial : Sparse R arity) : ConstantView polynomial :=
  match entries : polynomial.terms with
  | [] => .exact 0 (by
      rewrite [entries]
      change [] = Terms.insert ⟨Monomial.zero arity, (0 : R)⟩ []
      rewrite [Terms.insert, if_pos rfl]
      rfl)
  | [term] =>
      if same : term.monomial = Monomial.zero arity then
        .exact term.coefficient (by
          have nonzero : term.coefficient ≠ 0 := by
            have canonical := polynomial.canonical
            rewrite [entries] at canonical
            exact canonical.1
          rewrite [entries]
          change [term] = Terms.insert ⟨Monomial.zero arity, term.coefficient⟩ []
          rewrite [Terms.insert, if_neg nonzero]
          cases term with
          | mk monomial coefficient =>
              change monomial = Monomial.zero arity at same
              rewrite [same]
              rfl)
      else .variable term entries same
  | first :: second :: remaining => .multiple first second remaining entries

/-- An actual coefficient list containing at least two terms has a nonconstant inspection. -/
theorem constantView_nonconstant_of_multiple (polynomial : Sparse R arity)
    (first second : Term R arity) (remaining : List (Term R arity))
    (entries : polynomial.terms = first :: second :: remaining) : polynomial.constantView.Nonconstant := by
  unfold constantView
  split
  · rename_i selected
    cases selected.symm.trans entries
  · rename_i term selected
    cases congrArg List.tail (selected.symm.trans entries)
  · exact True.intro

/-- Whole-form equality to a constant determines the exact coefficient returned by inspection. -/
theorem constantView_eq_exact (polynomial : Sparse R arity) (value : R)
    (same : polynomial.terms = (constant value).terms) : polynomial.constantView = .exact value same := by
  cases polynomial with
  | mk terms canonical =>
      cases same
      change (constant value : Sparse R arity).constantView = .exact value rfl
      by_cases zero : value = 0
      · subst value
        have entries : (constant (0 : R) : Sparse R arity).terms = [] := by
          change Terms.insert ⟨Monomial.zero arity, (0 : R)⟩ [] = []
          rewrite [Terms.insert, if_pos rfl]
          rfl
        unfold constantView
        split
        · rfl
        · rename_i term selected
          cases entries.symm.trans selected
        · rename_i first second remaining selected
          cases entries.symm.trans selected
      · have entries : (constant value : Sparse R arity).terms = [⟨Monomial.zero arity, value⟩] := by
          change Terms.insert ⟨Monomial.zero arity, value⟩ [] = _
          rewrite [Terms.insert, if_neg zero]
          rfl
        unfold constantView
        split
        · rename_i selected
          cases entries.symm.trans selected
        · rename_i term selected
          have term_eq : (⟨Monomial.zero arity, value⟩ : Term R arity) = term :=
            congrArg (fun terms : List (Term R arity) => terms.headD ⟨Monomial.zero arity, value⟩)
              (entries.symm.trans selected)
          cases term_eq
          rewrite [dif_pos rfl]
          rfl
        · rename_i first second remaining selected
          cases congrArg List.tail (entries.symm.trans selected)

end Purelib.Polynomial.Multivariate.Sparse

end
