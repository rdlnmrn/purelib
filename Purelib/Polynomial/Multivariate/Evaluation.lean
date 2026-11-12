module

public import Purelib.Polynomial.Multivariate.Sparse
import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

/-!
# Scalar interpretation of canonical sparse polynomials

Evaluation uses the original finite variable indices. The insertion and finite
convolution laws apply to arbitrary input lists, so canonicalization preserves
the scalar polynomial even when the input has unordered or cancelling terms.
-/

public section

namespace Purelib.Polynomial.Multivariate

variable {R : Type} [CommRing R] {arity : Nat}

namespace Monomial

/-- Evaluate the retained exponent vector at the original finite variable environment. -/
@[expose] def eval : {arity : Nat} → Monomial arity → (Fin arity → R) → R
  | 0, .nil, _ => 1
  | _ + 1, .cons exponent tail, environment =>
      environment 0 ^ exponent * eval tail (fun index => environment index.succ)

/-- Pointwise equal finite variable readings give the same original monomial reading. -/
theorem eval_congr : {arity : Nat} → (monomial : Monomial arity) → (first second : Fin arity → R) →
    (∀ index, first index = second index) → monomial.eval first = monomial.eval second
  | 0, .nil, _, _, _ => rfl
  | _ + 1, .cons exponent remaining, first, second, same =>
      congrArg₂ (fun head tail => head ^ exponent * tail) (same 0)
        (eval_congr remaining (fun index => first index.succ) (fun index => second index.succ)
          (fun index => same index.succ))

/-- The constant exponent vector evaluates to one at every environment. -/
theorem eval_zero (arity : Nat) (environment : Fin arity → R) : eval (zero arity) environment = 1 := by
  induction arity with
  | zero => rfl
  | succ arity ih =>
      change environment 0 ^ 0 * eval (zero arity) (fun index => environment index.succ) = 1
      rewrite [pow_zero, ih, one_mul]
      rfl

/-- The degree-one exponent vector reads its original variable index. -/
theorem eval_atom (arity : Nat) (index : Fin arity) (environment : Fin arity → R) :
    eval (atom arity index) environment = environment index := by
  induction arity with
  | zero => exact Fin.elim0 index
  | succ arity ih =>
      refine Fin.cases ?_ ?_ index
      · change environment 0 ^ 1 * eval (zero arity) _ = environment 0
        rewrite [pow_one, eval_zero, mul_one]
        rfl
      · intro tailIndex
        change environment 0 ^ 0 * eval (atom arity tailIndex) _ = environment tailIndex.succ
        rewrite [pow_zero, one_mul, ih]
        rfl

/-- Evaluation turns componentwise exponent addition into scalar multiplication. -/
theorem eval_add (left right : Monomial arity) (environment : Fin arity → R) :
    eval (add left right) environment = eval left environment * eval right environment := by
  induction left with
  | nil => cases right; change (1 : R) = 1 * 1; exact (one_mul 1).symm
  | cons first tail ih =>
      cases right with
      | cons second remaining =>
          change environment 0 ^ (first + second) * eval (add tail remaining) _ =
            (environment 0 ^ first * eval tail _) * (environment 0 ^ second * eval remaining _)
          rewrite [pow_add, ih]
          ring0

end Monomial

namespace Term

/-- Evaluate an exact coefficient multiplied by its original finite monomial. -/
@[expose] def eval (environment : Fin arity → R) (term : Term R arity) : R :=
  term.coefficient * term.monomial.eval environment

/-- The product term evaluates to the product of the two original term readings. -/
theorem eval_product (environment : Fin arity → R) (left right : Term R arity) :
    eval environment ⟨Monomial.add left.monomial right.monomial, left.coefficient * right.coefficient⟩ =
      eval environment left * eval environment right := by
  change (left.coefficient * right.coefficient) * (Monomial.add _ _).eval environment = _
  rewrite [Monomial.eval_add]
  unfold eval
  ring0

end Term

namespace Terms

/-- Evaluate a finite term list by its retained ordered scalar sum. -/
@[expose] def eval (environment : Fin arity → R) : List (Term R arity) → R
  | [] => 0
  | first :: remaining => first.eval environment + eval environment remaining

/-- Pointwise equal finite variable readings preserve the complete original ordered coefficient sum. -/
theorem eval_congr (first second : Fin arity → R) (same : ∀ index, first index = second index) :
    (terms : List (Term R arity)) → eval first terms = eval second terms
  | [] => rfl
  | head :: remaining =>
      congrArg₂ (fun value tail => head.coefficient * value + tail)
        (head.monomial.eval_congr first second same) (eval_congr first second same remaining)

/-- Combining and removing coefficients during insertion preserves scalar evaluation. -/
theorem eval_insert [DecidableEq R] (environment : Fin arity → R) (term : Term R arity)
    (terms : List (Term R arity)) :
    eval environment (insert term terms) = term.eval environment + eval environment terms := by
  induction terms with
  | nil =>
      unfold insert
      split
      · rename_i zero
        change 0 = term.coefficient * term.monomial.eval environment + 0
        rewrite [zero, zero_mul, add_zero]
        rfl
      · exact Eq.refl _
  | cons first remaining ih =>
      unfold insert
      split
      · rename_i zero
        change _ = term.coefficient * term.monomial.eval environment + _
        rewrite [zero, zero_mul, zero_add]
        rfl
      · split
        · exact Eq.refl _
        · split
          · rename_i same
            split
            · rename_i cancel
              change eval environment remaining =
                term.coefficient * term.monomial.eval environment +
                  (first.coefficient * first.monomial.eval environment + eval environment remaining)
              rewrite [same, ← add_assoc, ← add_mul, cancel, zero_mul, zero_add]
              rfl
            · change (term.coefficient + first.coefficient) * first.monomial.eval environment +
                  eval environment remaining =
                term.coefficient * term.monomial.eval environment +
                  (first.coefficient * first.monomial.eval environment + eval environment remaining)
              rewrite [same, add_mul, add_assoc]
              rfl
          · change first.eval environment + eval environment (insert term remaining) =
              term.eval environment + (first.eval environment + eval environment remaining)
            rewrite [ih]
            ring0

/-- Accumulation adds the input polynomial to the retained accumulator's value. -/
theorem eval_accumulate [DecidableEq R] (environment : Fin arity → R)
    (input result : List (Term R arity)) :
    eval environment (accumulate input result) = eval environment input + eval environment result := by
  induction input generalizing result with
  | nil => exact (zero_add _).symm
  | cons first remaining ih =>
      change eval environment (accumulate remaining (insert first result)) = _
      rewrite [ih, eval_insert]
      change _ = (first.eval environment + eval environment remaining) + eval environment result
      ring0

/-- Complete term convolution multiplies the input readings and adds the retained accumulator. -/
theorem eval_multiplyTerm [DecidableEq R] (environment : Fin arity → R)
    (term : Term R arity) (input result : List (Term R arity)) :
    eval environment (multiplyTerm term input result) =
      term.eval environment * eval environment input + eval environment result := by
  induction input generalizing result with
  | nil => change _ = _ * 0 + _; rewrite [mul_zero, zero_add]; rfl
  | cons first remaining ih =>
      change eval environment (multiplyTerm term remaining (insert _ result)) = _
      rewrite [ih, eval_insert, Term.eval_product]
      change _ = term.eval environment * (first.eval environment + eval environment remaining) + _
      ring0

/-- Complete finite convolution preserves the scalar product of its two inputs. -/
theorem eval_multiply [DecidableEq R] (environment : Fin arity → R)
    (left right result : List (Term R arity)) :
    eval environment (multiply left right result) =
      eval environment left * eval environment right + eval environment result := by
  induction left generalizing result with
  | nil => change _ = 0 * _ + _; rewrite [zero_mul, zero_add]; rfl
  | cons first remaining ih =>
      change eval environment (multiply remaining right (multiplyTerm first right result)) = _
      rewrite [ih, eval_multiplyTerm]
      change _ = (first.eval environment + eval environment remaining) * eval environment right + _
      ring0

/-- Negating each displayed coefficient negates the finite scalar sum. -/
theorem eval_negated (environment : Fin arity → R) (terms : List (Term R arity)) :
    eval environment (terms.map (fun term => ⟨term.monomial, -term.coefficient⟩)) =
      -eval environment terms := by
  induction terms with
  | nil => change (0 : R) = -0; exact neg_zero.symm
  | cons first remaining ih =>
      change -first.coefficient * first.monomial.eval environment +
          eval environment (remaining.map _) = -(first.eval environment + eval environment remaining)
      rewrite [ih]
      unfold Term.eval
      ring0

end Terms

namespace Sparse

/-- Evaluate the retained canonical coefficient list at its original environment. -/
@[expose] def eval (environment : Fin arity → R) (polynomial : Sparse R arity) : R :=
  Terms.eval environment polynomial.terms

/-- Canonical zero has scalar reading zero at every retained environment. -/
theorem eval_zero (environment : Fin arity → R) : eval environment (zero : Sparse R arity) = 0 := rfl

/-- Canonicalization preserves the exact scalar reading of an arbitrary finite term list. -/
theorem eval_ofTerms [DecidableEq R] (environment : Fin arity → R) (terms : List (Term R arity)) :
    eval environment (ofTerms terms) = Terms.eval environment terms := by
  change Terms.eval environment (Terms.accumulate terms []) = _
  rewrite [Terms.eval_accumulate]
  exact add_zero _

/-- A constant sparse polynomial evaluates to its retained scalar coefficient. -/
theorem eval_constant [DecidableEq R] (environment : Fin arity → R) (value : R) :
    eval environment (constant value) = value := by
  rewrite [constant, eval_ofTerms]
  change value * (Monomial.zero arity).eval environment + 0 = value
  rewrite [Monomial.eval_zero, mul_one, add_zero]
  rfl

/-- A canonical degree-one polynomial reads its original variable index. -/
theorem eval_atom [DecidableEq R] (environment : Fin arity → R) (index : Fin arity) :
    eval environment (atom index) = environment index := by
  rewrite [atom, eval_ofTerms]
  change 1 * (Monomial.atom arity index).eval environment + 0 = environment index
  rewrite [Monomial.eval_atom, one_mul, add_zero]
  rfl

/-- Sparse addition preserves addition of the two retained scalar readings. -/
theorem eval_add [DecidableEq R] (environment : Fin arity → R) (left right : Sparse R arity) :
    eval environment (add left right) = eval environment left + eval environment right :=
  Terms.eval_accumulate environment left.terms right.terms

/-- Sparse negation preserves state-independent scalar negation. -/
theorem eval_neg [DecidableEq R] (environment : Fin arity → R) (input : Sparse R arity) :
    eval environment (neg input) = -eval environment input := by
  rewrite [neg, eval_ofTerms]
  exact Terms.eval_negated environment input.terms

/-- Sparse subtraction preserves subtraction of the two retained scalar readings. -/
theorem eval_sub [DecidableEq R] (environment : Fin arity → R) (left right : Sparse R arity) :
    eval environment (sub left right) = eval environment left - eval environment right := by
  rewrite [sub, eval_add, eval_neg]
  exact (sub_eq_add_neg _ _).symm

/-- Sparse multiplication preserves the product of the two retained scalar readings. -/
theorem eval_mul [DecidableEq R] (environment : Fin arity → R) (left right : Sparse R arity) :
    eval environment (mul left right) = eval environment left * eval environment right := by
  change Terms.eval environment (Terms.multiply left.terms right.terms []) = _
  rewrite [Terms.eval_multiply]
  exact add_zero _

/-- Repeated sparse multiplication preserves every natural scalar power. -/
theorem eval_pow [DecidableEq R] (environment : Fin arity → R) (input : Sparse R arity) (exponent : Nat) :
    eval environment (pow input exponent) = eval environment input ^ exponent := by
  induction exponent with
  | zero => rewrite [pow, eval_constant, pow_zero]; rfl
  | succ exponent ih =>
      rewrite [pow, eval_mul, ih, pow_succ]
      exact mul_comm _ _

/-- Equal retained coefficient lists have equal scalar readings at every original environment. -/
theorem eval_eq_of_terms_eq (environment : Fin arity → R) {left right : Sparse R arity}
    (same : left.terms = right.terms) : eval environment left = eval environment right :=
  congrArg (Terms.eval environment) same

end Sparse

end Purelib.Polynomial.Multivariate

end
