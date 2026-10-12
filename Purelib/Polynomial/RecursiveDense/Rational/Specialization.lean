module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.DropWhile.Basic
public import Purelib.Polynomial.RecursiveDense.Rational.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

section
public section

/-!
# Outer specialization of recursively dense rational polynomials

The retained inner point evaluates the original ordered coefficient sequence
into one dense rational polynomial in the final variable. Exact Horner
agreement and nonzero-coefficient certificates retain that point and the
original coefficient occurrence witnesses.
-/

namespace Purelib.Polynomial.RecursiveDense.Rational.Specialization

/- Finite recursively dense polynomials in exactly the displayed number of
variables.  `Coefficients` is a project-owned finite list constructor so the
kernel sees the mutual recursion directly, without a nested inductive. -/

/- Horner evaluation, inner coordinates first and the last coordinate
outermost. -/

/-- Specialize all inner variables, leaving an ordinary dense polynomial in
the final variable. -/
@[expose] def specializeOuter {arity : Nat}
    (coefficients : Basic.Coefficients arity) (inner : Basic.Point arity) :
    Basic.DensePolynomial :=
  ⟨coefficients.toList.map (fun coefficient => coefficient.eval inner)⟩

/-- Recursive coefficient evaluation equals a Horner fold of specialized coefficients.

The equality retains the inner point, outer variable and initial accumulator. -/
private theorem coefficients_eval_eq_foldl {arity : Nat} :
    ∀ (coefficients : Basic.Coefficients arity) (inner : Basic.Point arity)
      (outer value : Fraction.Rational),
      coefficients.eval inner outer value =
        (coefficients.toList.map
          (fun coefficient => coefficient.eval inner)).foldl
            (fun accumulator coefficient =>
              accumulator * outer + coefficient) value
  | .nil, _, _, _ => rfl
  | .cons coefficient remaining, inner, outer, value => by
      simp only [Basic.Coefficients.eval, Basic.Coefficients.toList, List.map_cons,
        List.foldl_cons]
      exact Purelib.Polynomial.RecursiveDense.Rational.Specialization.coefficients_eval_eq_foldl remaining inner outer _
termination_by coefficients _ _ _ => coefficients.toList.length
decreasing_by
  change remaining.toList.length < remaining.toList.length + 1
  exact Nat.le_refl _

/-- Evaluating a successor-arity polynomial agrees with evaluating its outer specialization. -/
@[simp] theorem eval_next {arity : Nat}
    (coefficients : Basic.Coefficients arity) (inner : Basic.Point arity)
    (outer : Fraction.Rational) :
    (Basic.Expression.next coefficients).eval (inner, outer) =
      (specializeOuter coefficients inner).eval outer := by
  rw [Basic.Expression.eval, coefficients_eval_eq_foldl]
  rfl

/-- A nonzero recursive coefficient sequence contains a nonzero coefficient. -/
theorem nonzero_coefficient {arity : Nat} :
    ∀ coefficients : Basic.Coefficients arity,
      coefficients.isZero = false →
      ∃ coefficient ∈ coefficients.toList, coefficient.isZero = false
  | .nil, nonzero => Bool.noConfusion nonzero
  | .cons coefficient remaining, nonzero => by
      cases coefficientZero : coefficient.isZero with
      | false =>
          exact ⟨coefficient, List.Mem.head remaining.toList, coefficientZero⟩
      | true =>
          have remainingNonzero : remaining.isZero = false := by
            change (coefficient.isZero && remaining.isZero) = false at nonzero
            rewrite [coefficientZero] at nonzero
            exact nonzero
          obtain ⟨entry, member, entryNonzero⟩ :=
            Purelib.Polynomial.RecursiveDense.Rational.Specialization.nonzero_coefficient remaining remainingNonzero
          exact ⟨entry, List.Mem.tail coefficient member, entryNonzero⟩

/-- If removing leading zeros empties a rational list, every entry was zero. -/
private theorem all_zero_of_dropWhile_eq_nil :
    ∀ coefficients : List Fraction.Rational,
      coefficients.dropWhile (fun coefficient => decide (coefficient = 0)) = [] →
      ∀ coefficient ∈ coefficients, coefficient = 0
  | [], _, _, member => by nomatch member
  | first :: remaining, dropped, coefficient, member => by
      cases selected : decide (first = 0) with
      | true =>
          have firstZero : first = 0 := of_decide_eq_true selected
          rewrite [Data.List.DropWhile.cons_of_true _ first remaining selected] at dropped
          rcases Data.List.Membership.mem_cons.mp member with equal | later
          · cases equal
            exact firstZero
          · exact Purelib.Polynomial.RecursiveDense.Rational.Specialization.all_zero_of_dropWhile_eq_nil remaining
              dropped coefficient later
      | false =>
          rewrite [Data.List.DropWhile.cons_of_false _ first remaining selected] at dropped
          cases dropped

/-- A nonzero entry in a dense coefficient list forces its zero test to be false. -/
private theorem dense_isZero_false_of_member_ne_zero
    (polynomial : Basic.DensePolynomial) {coefficient : Fraction.Rational}
    (member : coefficient ∈ polynomial.coeffs)
    (nonzero : coefficient ≠ 0) :
    polynomial.isZero = false := by
  cases zero : polynomial.isZero with
  | false => rfl
  | true =>
      have dropped : polynomial.coeffs.dropWhile
          (fun entry => decide (entry = 0)) = [] := by
        change (polynomial.coeffs.dropWhile
          (fun entry => decide (entry = 0))).isEmpty = true at zero
        generalize scanned : polynomial.coeffs.dropWhile (fun entry => decide (entry = 0)) = entries at zero ⊢
        cases entries with
        | nil => rfl
        | cons _ _ => exact Bool.noConfusion zero
      exact (nonzero
        (all_zero_of_dropWhile_eq_nil polynomial.coeffs dropped coefficient
          member)).elim

/-- A coefficient nonzero at the inner point makes the outer specialization nonzero.

The original coefficient membership witness supplies a nonzero entry of the specialized dense list. -/
theorem specializeOuter_nonzero_of_coefficient
    {arity : Nat} {coefficients : Basic.Coefficients arity}
    {coefficient : Basic.Expression arity} {inner : Basic.Point arity}
    (member : coefficient ∈ coefficients.toList)
    (nonzero : coefficient.eval inner ≠ 0) :
    (specializeOuter coefficients inner).isZero = false := by
  apply dense_isZero_false_of_member_ne_zero
    (specializeOuter coefficients inner)
  · exact Data.List.Map.mem_map.mpr
      ⟨coefficient, member, rfl⟩
  · exact nonzero

end Purelib.Polynomial.RecursiveDense.Rational.Specialization

end
