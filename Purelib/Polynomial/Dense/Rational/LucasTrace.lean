module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Leading
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.List.DropWhile.Basic
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Finite Lucas polynomial traces

The original recurrence retains consecutive polynomials at each radius.
The shape certificate follows the same polynomial products and subtraction,
with an exact power-of-two leading coefficient for every retained step.
-/
namespace Purelib.Polynomial.Dense.Rational.LucasTrace

open Purelib.Data.Rat
open Purelib.Polynomial

open Purelib.Data.List

/-- A normalized rational constant, including the zero branch. -/
@[expose] public def normalizedConstant (value : Fraction.Rational) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  if value = 0 then 0 else Dense.Basic.DensePolynomial.constant value

/-- The normalized constant evaluates to the supplied rational value, including zero. -/
@[simp] public theorem eval_normalizedConstant (value point : Fraction.Rational) :
    (normalizedConstant value).eval point = value := by
  rw [normalizedConstant]
  split
  · rename_i zero
    rw [zero, Dense.Basic.DensePolynomial.eval_zero]
  · exact Dense.Basic.DensePolynomial.eval_constant value point

/-- A normalized constant satisfies the degree-at-most-zero certificate. -/
public theorem normalizedConstant_atMost (value : Fraction.Rational) :
    Dense.Leading.DegreeAtMost (normalizedConstant value) 0 := by
  by_cases zero : value = 0
  · rw [normalizedConstant, if_pos zero]
    exact Dense.Leading.DegreeAtMost.zero 0
  · rw [normalizedConstant, if_neg zero]
    exact (Dense.Leading.LeadingTerm.constant zero).atMost

/-- The polynomial `2X`. -/
@[expose] public def twiceVariable : (Dense.Basic.DensePolynomial Fraction.Rational) := ⟨[2, 0]⟩

/-- The displayed polynomial `2X` evaluates as twice the supplied point. -/
@[simp] public theorem eval_twiceVariable (point : Fraction.Rational) :
    twiceVariable.eval point = 2 * point := by
  change (0 * point + 2) * point + 0 = 2 * point
  ring1

/-- The displayed polynomial `2X` has degree one and leading coefficient two.

Its nonzero head retains the original two-entry table. That table supplies
the normalization, nonzero, degree and leading-coefficient fields directly. -/
public theorem twiceVariable_leading : Dense.Leading.LeadingTerm twiceVariable 1 2 := by
  have twoNonzero : (2 : Fraction.Rational) ≠ 0 := by decide
  have retained : ([2, 0] : List Fraction.Rational).dropWhile (· = 0) = [2, 0] :=
    DropWhile.cons_of_false (fun coefficient : Fraction.Rational => decide (coefficient = 0))
      2 [0] (decide_eq_false twoNonzero)
  refine
    { normalized := ?_
      nonzero := ?_
      degree_eq := ?_
      coefficient_eq := ?_ }
  · apply Dense.Basic.DensePolynomial.ext
    change ([2, 0] : List Fraction.Rational).dropWhile (· = 0) = [2, 0]
    exact retained
  · change (([2, 0] : List Fraction.Rational).dropWhile (· = 0)).isEmpty = false
    rewrite [retained]
    exact Eq.refl _
  · change (([2, 0] : List Fraction.Rational).dropWhile (· = 0)).length - 1 = 1
    rewrite [retained]
    exact Eq.refl _
  · change (([2, 0] : List Fraction.Rational).dropWhile (· = 0)).headD 0 = 2
    rewrite [retained]
    exact Eq.refl _

/-- Consecutive Lucas polynomials `(A_n,A_{n+1})` at one displayed radius.

At each successor step, the previous second polynomial becomes the first.
The original two products and subtraction construct the next polynomial at the
same retained radius. -/
@[expose] public def tracePair (radius : Fraction.Rational) : Nat → Dense.Rational.Basic.CoordinatePolynomial ×
  Dense.Rational.Basic.CoordinatePolynomial
  | 0 => (normalizedConstant 2, twiceVariable)
  | index + 1 =>
      let previous := tracePair radius index
      (previous.2,
        twiceVariable * previous.2 -
          normalizedConstant radius * previous.1)

/-- The finite Lucas coordinate polynomial `A_n(X,radius)`. -/
@[expose] public def tracePolynomial (radius : Fraction.Rational) (degree : Nat) : (Dense.Basic.DensePolynomial
  Fraction.Rational) :=
  (tracePair radius degree).1

/-- The recurrence step exposed without the implementation pair. -/
public theorem tracePolynomial_succ_succ (radius : Fraction.Rational) (degree : Nat) :
    tracePolynomial radius (degree + 2) =
      twiceVariable * tracePolynomial radius (degree + 1) -
        normalizedConstant radius * tracePolynomial radius degree := by
  rfl

/-- The zeroth Lucas coordinate polynomial is the normalized constant two. -/
@[simp] public theorem tracePolynomial_zero (radius : Fraction.Rational) :
    tracePolynomial radius 0 = normalizedConstant 2 := rfl

/-- The first Lucas coordinate polynomial is `2X`. -/
@[simp] public theorem tracePolynomial_one (radius : Fraction.Rational) :
    tracePolynomial radius 1 = twiceVariable := rfl

/-- Certify the degree bound and exact leading term of consecutive Lucas coordinate polynomials.

At index `n`, the first component has degree at most `n`; the second has degree `n + 1` and leading coefficient `2^(n +
1)` for every rational radius. -/
public theorem tracePair_shape (radius : Fraction.Rational) : ∀ degree,
    Dense.Leading.DegreeAtMost (tracePair radius degree).1 degree ∧
      Dense.Leading.LeadingTerm (tracePair radius degree).2 (degree + 1)
        (2 ^ (degree + 1)) := by
  intro degree
  induction degree with
  | zero =>
      constructor
      · exact normalizedConstant_atMost 2
      · exact Dense.Leading.LeadingTerm.of_equal rfl rfl
          (by rw [Nat.zero_add, pow_one]) twiceVariable_leading
  | succ degree inductionHypothesis =>
      rw [tracePair]
      let previous := tracePair radius degree
      constructor
      · exact inductionHypothesis.2.atMost
      have firstLeading :
          Dense.Leading.LeadingTerm (twiceVariable * previous.2) (degree + 2)
            (2 * 2 ^ (degree + 1)) := by
        have multiplied :=
          Dense.Leading.LeadingTerm.mul twiceVariable_leading inductionHypothesis.2
        exact Dense.Leading.LeadingTerm.of_equal rfl
          (by rw [Nat.one_add]) rfl multiplied
      have previousFirstAtMost :
          Dense.Leading.DegreeAtMost previous.1 degree := inductionHypothesis.1
      have radiusAtMost : Dense.Leading.DegreeAtMost (normalizedConstant radius) 0 :=
        normalizedConstant_atMost radius
      have lowerBelow :
          Dense.Leading.DegreeBelow (normalizedConstant radius * previous.1)
            (degree + 2) := by
        have below :=
          (Dense.Leading.DegreeAtMost.mul radiusAtMost previousFirstAtMost).toBelowSucc
        exact below.mono (by
          calc
            0 + degree + 1 = degree + 1 := by rw [Nat.zero_add]
            _ ≤ degree + 2 := Nat.le_succ (degree + 1))
      have result := firstLeading.subBelow lowerBelow
      change Dense.Leading.LeadingTerm
        (twiceVariable * previous.2 - normalizedConstant radius * previous.1)
        (Nat.succ degree + 1) (2 ^ (Nat.succ degree + 1))
      have coefficientIdentity :
          (2 : Fraction.Rational) * 2 ^ (degree + 1) = 2 ^ (degree + 2) := by
        exact (mul_comm (2 : Fraction.Rational) (2 ^ (degree + 1))).trans
          (pow_succ (2 : Fraction.Rational) (degree + 1)).symm
      exact Dense.Leading.LeadingTerm.of_equal rfl rfl coefficientIdentity.symm result

/-- The second retained Lucas polynomial has the successor degree and corresponding power-of-two leading coefficient. -/
public theorem tracePair_leading (radius : Fraction.Rational) (degree : Nat) :
    Dense.Leading.LeadingTerm (tracePair radius degree).2 (degree + 1)
      (2 ^ (degree + 1)) :=
  (tracePair_shape radius degree).2

/-- At positive index, a Lucas coordinate polynomial has that degree and leading coefficient `2^degree`. -/
public theorem tracePolynomial_leading (radius : Fraction.Rational) (degree : Nat)
    (positive : 0 < degree) :
    Dense.Leading.LeadingTerm (tracePolynomial radius degree) degree (2 ^ degree) := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  change Dense.Leading.LeadingTerm (tracePair radius predecessor).2
    (predecessor + 1) (2 ^ (predecessor + 1))
  exact tracePair_leading radius predecessor
end Purelib.Polynomial.Dense.Rational.LucasTrace
