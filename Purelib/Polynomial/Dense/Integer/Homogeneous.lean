module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
public import Purelib.Algebra.Monoid.Int
import Purelib.Data.Int.Arithmetic
import Purelib.Data.List.Map
import Purelib.Algebra.Semiring.Normalization

/-!
# Homogeneous readbacks of descending integer coefficient tables

The original integer power recurrence and ordered coefficient list determine
the homogeneous evaluation. Direct scalar transports compare its retained
integer value with the same rational Horner evaluation.
-/

namespace Purelib.Polynomial.Dense.Integer.Homogeneous

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Algebra
open Purelib.Data.List
open Purelib.Data.Int

/-- Horner evaluation of an integer coefficient list after embedding it in
the constructive rationals.

The original ordered integer table is embedded coefficient by coefficient.
Its unchanged descending Horner evaluation supplies the rational value. -/
@[expose] public def evalIntegers (point : Fraction.Rational) (coefficients : List Int) : Fraction.Rational :=
  Dense.Basic.DensePolynomial.evalCoeffs point (coefficients.map fun (coefficient : Int) =>
    (coefficient : Fraction.Rational))

/-- An empty integer coefficient list evaluates to the constructive rational zero. -/
@[simp] public theorem evalIntegers_nil (point : Fraction.Rational) :
    evalIntegers point [] = 0 := rfl

/-- Split descending integer-coefficient evaluation into the leading monomial and the remaining list.

The retained head contributes its monomial at the original tail length.
The unchanged mapped tail supplies the remaining descending evaluation. -/
public theorem evalIntegers_cons (point : Fraction.Rational) (coefficient : Int)
    (remaining : List Int) :
    evalIntegers point (coefficient :: remaining) =
      (coefficient : Fraction.Rational) * point ^ remaining.length +
        evalIntegers point remaining := by
  change Dense.Basic.DensePolynomial.evalCoeffs point
      ((coefficient : Fraction.Rational) :: remaining.map (fun value : Int => (value : Fraction.Rational))) = _
  rewrite [Dense.Basic.DensePolynomial.evalCoeffs_cons_expansion,
    Map.length_map]
  exact Eq.refl _

/-- Multiplying each integer coefficient by a fixed integer multiplies its rational evaluation by that integer.

The same fixed integer multiplies each original coefficient. Scalar cast
transport and the unchanged descending tail account for the common factor. -/
public theorem evalIntegers_map_mul (point : Fraction.Rational) (initial : Int)
    (coefficients : List Int) :
    evalIntegers point (coefficients.map fun value => initial * value) =
      (initial : Fraction.Rational) * evalIntegers point coefficients := open Purelib.Algebra in by
  induction coefficients with
  | nil => exact (mul_zero (initial : Fraction.Rational)).symm
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.map_cons, evalIntegers_cons, Map.length_map,
        Ring.IntCast.intCast_mul, inductionHypothesis]
      ring1

/-! ## Homogeneous integer evaluation -/

/-- High-to-low homogeneous evaluation.  For `m+1` coefficients it is the
ordinary rational evaluation at `num/den`, multiplied by `den^m`.

Each original head contributes its numerator power at the retained tail length.
The original natural denominator multiplies the recursive evaluation of that tail. -/
@[expose] public def homogeneousEval (num : Int) (den : Nat) : List Int → Int
  | [] => 0
  | coefficient :: remaining =>
      coefficient * num ^ remaining.length +
        (den : Int) * homogeneousEval num den remaining

/-- Last high-to-low coefficient, with zero only for the empty list. -/
@[expose] public def constantCoefficient : List Int → Int
  | [] => 0
  | coefficient :: remaining =>
      remaining.foldl (fun _ next => next) coefficient

/-- A singleton descending coefficient list has its sole entry as constant coefficient. -/
@[simp] public theorem constantCoefficient_singleton (coefficient : Int) :
    constantCoefficient [coefficient] = coefficient := rfl

/-- Removing a leading entry from a list with at least two coefficients preserves the constant coefficient.

The last-entry accumulator overwrites the first retained coefficient with
the next one before scanning the unchanged remaining table. -/
@[simp] public theorem constantCoefficient_cons_cons
    (leading next : Int) (remaining : List Int) :
    constantCoefficient (leading :: next :: remaining) =
      constantCoefficient (next :: remaining) := rfl

/-- Every term below the leading term contains the displayed denominator.

The exact recursive tail evaluation is the retained integer divisibility
witness after removing the displayed leading monomial. -/
public theorem denominator_dvd_homogeneousEval_sub_leading
    (num : Int) (den : Nat) (leading : Int) (remaining : List Int) :
    (den : Int) ∣
      homogeneousEval num den (leading :: remaining) -
        leading * num ^ remaining.length := by
  refine ⟨homogeneousEval num den remaining, ?_⟩
  simp only [homogeneousEval]
  ring1

/-- Every term above the constant term contains the displayed numerator.

Structural recursion retains the original constant coefficient and denominator
power. Each preceding original head contributes to the explicit integer factor. -/
public theorem numerator_dvd_homogeneousEval_sub_constant
    (num : Int) (den : Nat) (leading : Int) (remaining : List Int) :
    num ∣
      homogeneousEval num den (leading :: remaining) -
        constantCoefficient (leading :: remaining) *
          (den : Int) ^ remaining.length := by
  induction remaining generalizing leading with
  | nil =>
      refine ⟨0, ?_⟩
      rewrite [homogeneousEval, homogeneousEval, constantCoefficient_singleton,
        List.length_nil, Arithmetic.pow_zero]
      ring1
  | cons next remaining inductionHypothesis =>
      rcases inductionHypothesis next with ⟨factor, factorization⟩
      refine ⟨leading * num ^ remaining.length + (den : Int) * factor, ?_⟩
      simp only [homogeneousEval, constantCoefficient_cons_cons,
        List.length_cons, pow_succ]
      calc
        leading * (num ^ remaining.length * num) +
              (den : Int) * homogeneousEval num den (next :: remaining) -
            constantCoefficient (next :: remaining) *
              ((den : Int) ^ remaining.length * den) =
            num * (leading * num ^ remaining.length) +
              (den : Int) *
                (homogeneousEval num den (next :: remaining) -
                  constantCoefficient (next :: remaining) *
                    (den : Int) ^ remaining.length) := by
          ring1
        _ = num *
            (leading * num ^ remaining.length + (den : Int) * factor) := by
          rw [factorization]
          ring1

/-- Homogeneous integer evaluation clears the denominator power of rational evaluation.

For a nonempty coefficient list and positive natural denominator, its integer value embeds as the ordinary rational
evaluation multiplied by the denominator raised to the tail length. -/
public theorem homogeneousEval_cons_eq_scaled
    (num : Int) {den : Nat} (denPositive : 0 < den)
    (coefficient : Int) (remaining : List Int) :
    ((homogeneousEval num den (coefficient :: remaining) : Int) : Fraction.Rational) =
      (den : Fraction.Rational) ^ remaining.length *
        evalIntegers ((num : Fraction.Rational) / (den : Fraction.Rational))
          (coefficient :: remaining) := open Purelib.Algebra.Field in open Purelib.Algebra in by
  induction remaining generalizing coefficient with
  | nil =>
      rewrite [homogeneousEval, homogeneousEval, evalIntegers_cons, evalIntegers_nil,
        List.length_nil, Arithmetic.pow_zero, pow_zero, pow_zero,
        Arithmetic.mul_one, Int.mul_zero, Int.add_zero,
        mul_one, add_zero, one_mul]
      exact Eq.refl _
  | cons next remaining inductionHypothesis =>
      let denominator : Fraction.Rational := den
      let numerator : Fraction.Rational := num
      let point : Fraction.Rational := numerator / denominator
      have denominatorNonzero : denominator ≠ 0 := by
        change (den : Fraction.Rational) ≠ 0
        intro equal
        have denZero : den = 0 :=
          Fraction.Cast.Compatibility.natCast_injective_direct
            (equal.trans (Nat.cast_zero).symm)
        exact (Nat.ne_of_gt denPositive) denZero
      have pointClear : denominator * point = numerator := by
        change (den : Fraction.Rational) * ((num : Fraction.Rational) / (den : Fraction.Rational)) =
          (num : Fraction.Rational)
        rw [Fraction.Field.mul_comm]
        exact ExplicitField.div_mul_cancel _ denominatorNonzero
      have powerClear :
          denominator ^ (List.length (next :: remaining)) *
              point ^ (List.length (next :: remaining)) =
            numerator ^ (List.length (next :: remaining)) := by
        rewrite [← Semiring.Normalization.product_pow, pointClear]
        exact Eq.refl _
      change
        ((coefficient * num ^ (next :: remaining).length +
            (den : Int) * homogeneousEval num den (next :: remaining) : Int) :
            Fraction.Rational) =
          denominator ^ (List.length (next :: remaining)) *
            evalIntegers point (coefficient :: next :: remaining)
      rw [Ring.IntCast.add, Ring.IntCast.intCast_mul, Ring.IntCast.intCast_mul, Ring.IntCast.intCast_pow,
        Int.cast_natCast, inductionHypothesis]
      conv_rhs =>
        rw [evalIntegers_cons point coefficient (next :: remaining)]
      change
        (coefficient : Fraction.Rational) *
              numerator ^ (List.length (next :: remaining)) +
            denominator *
              (denominator ^ remaining.length *
                evalIntegers point (next :: remaining)) =
          denominator ^ (List.length (next :: remaining)) *
            ((coefficient : Fraction.Rational) *
                point ^ (List.length (next :: remaining)) +
              evalIntegers point (next :: remaining))
      calc
        (coefficient : Fraction.Rational) *
              numerator ^ (List.length (next :: remaining)) +
            denominator *
              (denominator ^ remaining.length *
                evalIntegers point (next :: remaining)) =
            (coefficient : Fraction.Rational) *
                (denominator ^ (List.length (next :: remaining)) *
                  point ^ (List.length (next :: remaining))) +
              (denominator * denominator ^ remaining.length) *
                evalIntegers point (next :: remaining) := by
          rw [powerClear]
          ring1
        _ = _ := by
          rw [List.length_cons, pow_succ]
          ring1

end Purelib.Polynomial.Dense.Integer.Homogeneous
