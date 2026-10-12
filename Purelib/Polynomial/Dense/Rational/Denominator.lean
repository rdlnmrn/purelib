module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Integer.Homogeneous
public import Purelib.Polynomial.Dense.Rational.Coefficients
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Data.List.Map
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.NatCast
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite retained denominator clearance

The original descending rational table is cleared by a structural product
of its canonical positive denominators. The cached integer table, common
denominator and endpoint certificates all concern that same construction.
-/

namespace Purelib.Polynomial.Dense.Rational.Denominator

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Algebra
open Purelib.Data.List
open Purelib.Data.Int

set_option genInjectivity false in
/-- Integer coefficients together with their common positive denominator.

The positive common denominator and ordered integer table belong to the same
finite clearance result. The construction retains that exact denominator witness. -/
public structure ClearedCoefficients where
  /-- The common natural denominator retained for the integer coefficient list. -/ denominator : Nat
  /-- The common denominator is strictly positive. -/ denominatorPositive : 0 < denominator
  /-- The integer coefficient table in the same descending order as its rational source. -/ coefficients : List Int

constructive_injectivity ClearedCoefficients

/-- Clear a finite high-to-low coefficient list by a structural product of
its canonical positive denominators.

The original head numerator is scaled by the retained tail denominator. The
original head denominator scales the unchanged tail table in its original order. -/
@[expose] public def clear : List Fraction.Rational → ClearedCoefficients
  | [] => ⟨1, by decide, []⟩
  | coefficient :: remaining =>
      let head := Fraction.Basic.representative coefficient
      let tail := clear remaining
      { denominator := head.den * tail.denominator
        denominatorPositive := Nat.mul_pos head.den_pos tail.denominatorPositive
        coefficients :=
          head.num * (tail.denominator : Int) ::
            tail.coefficients.map (fun value => (head.den : Int) * value) }

/-- Finite denominator clearing preserves the number of coefficients.

The original head contributes one retained integer slot. Mapping the cached
tail table retains exactly its original coefficient count. -/
@[simp] public theorem clear_length (coefficients : List Fraction.Rational) :
    (clear coefficients).coefficients.length = coefficients.length := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      change ((clear remaining).coefficients.map
        (fun value : Int => ((Fraction.Basic.representative coefficient).den : Int) * value)).length + 1 =
          remaining.length + 1
      rewrite [Map.length_map, inductionHypothesis]
      exact Eq.refl _

/-- Clearing multiplies evaluation by exactly the displayed common
denominator.

The canonical head numerator/denominator equality transports one Horner
step. The exact cached tail clearance supplies the remaining scaled evaluation. -/
public theorem eval_clear (point : Fraction.Rational) (coefficients : List Fraction.Rational) :
    Dense.Integer.Homogeneous.evalIntegers point (clear coefficients).coefficients =
      ((clear coefficients).denominator : Fraction.Rational) *
        Dense.Basic.DensePolynomial.evalCoeffs point coefficients := open Purelib.Algebra in by
  induction coefficients with
  | nil =>
      change (0 : Fraction.Rational) = 1 * 0
      exact (one_mul (0 : Fraction.Rational)).symm
  | cons coefficient remaining inductionHypothesis =>
      let head := Fraction.Basic.representative coefficient
      let tail := clear remaining
      rw [show (clear (coefficient :: remaining)).coefficients =
          head.num * (tail.denominator : Int) ::
            tail.coefficients.map (fun value => (head.den : Int) * value)
        from rfl]
      rw [Dense.Integer.Homogeneous.evalIntegers_cons, Map.length_map, clear_length,
        Dense.Integer.Homogeneous.evalIntegers_map_mul, Ring.IntCast.intCast_mul, Int.cast_natCast,
        inductionHypothesis]
      change
        (head.num : Fraction.Rational) * (tail.denominator : Fraction.Rational) *
              point ^ remaining.length +
            (head.den : Fraction.Rational) *
              ((tail.denominator : Fraction.Rational) * Dense.Basic.DensePolynomial.evalCoeffs point remaining) =
          ((head.den * tail.denominator : Nat) : Fraction.Rational) *
            Dense.Basic.DensePolynomial.evalCoeffs point (coefficient :: remaining)
      have clearance := Fraction.Cast.representative_mul_den coefficient
      change coefficient * (head.den : Fraction.Rational) =
        (head.num : Fraction.Rational) at clearance
      rw [Dense.Basic.DensePolynomial.evalCoeffs_cons_expansion, ← clearance, NatCast.mul]
      ring1

/-- A nonzero constructive rational has a nonzero canonical numerator.

A zero canonical numerator would read back as the original rational zero.
The supplied nonzero witness excludes that same retained representative. -/
public theorem representative_num_ne_zero {value : Fraction.Rational}
    (nonzero : value ≠ 0) : (Fraction.Basic.representative value).num ≠ 0 := open Purelib.Algebra.Field in by
  intro numeratorZero
  apply nonzero
  rw [Fraction.Cast.representative_eq_num_div_den value, numeratorZero]
  exact ExplicitField.zero_div _

/-- Multiplying every entry of a nonempty integer coefficient list scales its constant coefficient.

The original last-entry accumulator retains the same final occurrence.
Its displayed integer factor multiplies that retained constant coefficient. -/
private theorem constantCoefficient_map_mul (factor : Int)
    (leading : Int) (remaining : List Int) :
    Dense.Integer.Homogeneous.constantCoefficient
        ((leading :: remaining).map fun value => factor * value) =
      factor * Dense.Integer.Homogeneous.constantCoefficient (leading :: remaining) := by
  induction remaining generalizing leading with
  | nil => rfl
  | cons next remaining inductionHypothesis =>
      rw [List.map_cons, List.map_cons, Dense.Integer.Homogeneous.constantCoefficient_cons_cons,
        Dense.Integer.Homogeneous.constantCoefficient_cons_cons]
      exact inductionHypothesis next

/-- A nonzero first rational coefficient clears to a nonzero first integer
coefficient.

The exact canonical numerator and cached tail denominator form the retained
leading integer. Their supplied nonzero witnesses certify that same product. -/
public theorem clear_leading_nonzero
    (leading : Fraction.Rational) (remaining : List Fraction.Rational)
    (nonzero : leading ≠ 0) :
    ∃ integerLeading integerRemaining,
      (clear (leading :: remaining)).coefficients =
          integerLeading :: integerRemaining ∧
        integerLeading ≠ 0 := by
  let numerator := (Fraction.Basic.representative leading).num
  let multiplier : Int := clear remaining |>.denominator
  refine ⟨numerator * multiplier,
    (clear remaining).coefficients.map
      (fun value => ((Fraction.Basic.representative leading).den : Int) * value), rfl, ?_⟩
  intro vanished
  exact (Arithmetic.eq_zero_of_mul_eq_zero vanished).elim
    (representative_num_ne_zero nonzero)
    (Int.ofNat_ne_zero.mpr
      (Nat.ne_of_gt (clear remaining).denominatorPositive))

/-- A nonzero last rational coefficient clears to a nonzero last integer
coefficient.

The unchanged original final coefficient supplies its nonzero representative.
Each preceding canonical positive denominator retains the nonzero integer scaling. -/
public theorem clear_constant_nonzero
    (leading : Fraction.Rational) (remaining : List Fraction.Rational)
    (nonzero : Dense.Rational.Coefficients.rationalConstantCoefficient (leading :: remaining) ≠ 0) :
    Dense.Integer.Homogeneous.constantCoefficient (clear (leading :: remaining)).coefficients ≠ 0 := by
  induction remaining generalizing leading with
  | nil =>
      have leadingNonzero : leading ≠ 0 := nonzero
      change (Fraction.Basic.representative leading).num * (1 : Int) ≠ 0
      rewrite [Arithmetic.mul_one]
      exact representative_num_ne_zero leadingNonzero
  | cons next remaining inductionHypothesis =>
      let integerLeading :=
        (Fraction.Basic.representative next).num * ((clear remaining).denominator : Int)
      let integerRemaining :=
        (clear remaining).coefficients.map
          (fun value => ((Fraction.Basic.representative next).den : Int) * value)
      have tailShape :
          (clear (next :: remaining)).coefficients =
            integerLeading :: integerRemaining := rfl
      rw [show (clear (leading :: next :: remaining)).coefficients =
          (Fraction.Basic.representative leading).num *
              ((clear (next :: remaining)).denominator : Int) ::
            (clear (next :: remaining)).coefficients.map
              (fun value => ((Fraction.Basic.representative leading).den : Int) * value)
        from rfl]
      rw [tailShape, List.map_cons, Dense.Integer.Homogeneous.constantCoefficient_cons_cons]
      rw [← List.map_cons, constantCoefficient_map_mul]
      intro vanished
      exact (Arithmetic.eq_zero_of_mul_eq_zero vanished).elim
        (Int.ofNat_ne_zero.mpr
          (Nat.ne_of_gt (Fraction.Basic.representative leading).den_pos))
        (by
          rw [← tailShape]
          exact inductionHypothesis next nonzero)

end Purelib.Polynomial.Dense.Rational.Denominator
