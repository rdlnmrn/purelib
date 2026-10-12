module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.List.Reverse

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

/-!
# Finite power-of-two coefficient weights

The original reversed coefficient list and natural exponent determine its
weighted quadrance sum. Scalar and structural laws bound its monomial sum.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm.Weighted

/-- Finite weighted sum of squared coefficient norms, with the displayed
natural exponent as the first weight.

Each successive coefficient uses the next natural exponent of two.
The finite recursion retains the supplied coefficient order and ends
with the original zero accumulator. -/
@[expose] public def weightedNormSum : List Gaussian.Basic.Canonical → Nat → Fraction.Rational
  | [], _ => 0
  | coefficient :: coefficients, exponent =>
      Data.Gaussian.Norm.Basic.normSq coefficient * (2 : Fraction.Rational) ^ exponent +
        weightedNormSum coefficients (exponent + 1)

/-- The finite power-of-two weighted coefficient quadrance sum is nonnegative.

Every coefficient quadrance and every power-of-two weight is nonnegative.
Finite recursion adds these contributions in their original order. -/
public theorem weightedNormSum_nonneg (coefficients : List Gaussian.Basic.Canonical) (exponent : Nat) :
    0 ≤ weightedNormSum coefficients exponent := by
  induction coefficients generalizing exponent with
  | nil => exact Fraction.Order.Basic.le_refl 0
  | cons coefficient coefficients inductionHypothesis =>
      exact add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Gaussian.Norm.Basic.normSq_nonneg coefficient)
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            (by decide : (0 : Fraction.Rational) ≤ 2) exponent))
        (inductionHypothesis (exponent + 1))

/-- Split a weighted sum over appended coefficient lists.

The second list starts at the original exponent plus the length of the first list. -/
public theorem weightedNormSum_append (left right : List Gaussian.Basic.Canonical)
    (exponent : Nat) :
    weightedNormSum (left ++ right) exponent =
      weightedNormSum left exponent +
        weightedNormSum right (exponent + left.length) := by
  induction left generalizing exponent with
  | nil =>
      change weightedNormSum right exponent =
        0 + weightedNormSum right (exponent + 0)
      rewrite [Nat.add_zero]
      exact (_root_.zero_add _).symm
  | cons coefficient coefficients inductionHypothesis =>
      rw [List.cons_append, weightedNormSum,
        weightedNormSum,
        inductionHypothesis]
      simp only [List.length_cons]
      have exponentIdentity :
          exponent + 1 + coefficients.length =
            exponent + (coefficients.length + 1) := by ring1
      rw [exponentIdentity]
      ring1

/-- Adding a leading coefficient adds its reversed-list power-of-two contribution.

Reversing the list places the new leading coefficient after the retained
tail. Its exponent is precisely the tail length, with all earlier weights
unchanged. -/
public theorem weightedNormSum_reverse_cons
    (coefficient : Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical) :
    weightedNormSum ((coefficient :: coefficients).reverse) 0 =
      weightedNormSum coefficients.reverse 0 +
        Data.Gaussian.Norm.Basic.normSq coefficient * (2 : Fraction.Rational) ^ coefficients.length := by
  rw [List.Reverse.reverse_cons, weightedNormSum_append]
  simp only [List.Reverse.length_reverse, Nat.zero_add, weightedNormSum]
  ring1

/-- The monomial squared-norm sum is bounded by the explicit reversed
coefficient weight and the largest displayed radial power.

The coefficient list is nonempty, its squared radius is nonnegative and
at most twice the radial square, and the radial square is at least one.
These bounds control each power while preserving the reversed weights. -/
public theorem monomialNormSqSum_le_weighted :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (radiusSq radialSq : Fraction.Rational),
      coefficients ≠ [] → 0 ≤ radiusSq →
      radiusSq ≤ 2 * radialSq → 1 ≤ radialSq →
      Dense.Gaussian.Evaluation.Norm.monomialNormSqSum coefficients radiusSq ≤
        weightedNormSum coefficients.reverse 0 *
          radialSq ^ (coefficients.length - 1)
  | [], _, _, nonempty, _, _, _ => (nonempty rfl).elim
  | coefficient :: coefficients, radiusSq, radialSq,
      _, radiusNonnegative, radiusBound, oneLeRadial => by
      cases coefficients with
      | nil =>
          have sourceReadback :
              Dense.Gaussian.Evaluation.Norm.monomialNormSqSum [coefficient] radiusSq =
                Data.Gaussian.Norm.Basic.normSq coefficient := by
            change Data.Gaussian.Norm.Basic.normSq coefficient * radiusSq ^ 0 + 0 = _
            ring1
          have targetReadback :
              weightedNormSum [coefficient].reverse 0 *
                  radialSq ^ ([coefficient].length - 1) =
                Data.Gaussian.Norm.Basic.normSq coefficient := by
            change (Data.Gaussian.Norm.Basic.normSq coefficient *
              (2 : Fraction.Rational) ^ 0 + 0) * radialSq ^ 0 = _
            ring1
          rewrite [sourceReadback, targetReadback]
          exact Fraction.Order.Basic.le_refl _
      | cons next remaining =>
          let tail := next :: remaining
          have tailNonempty : tail ≠ [] := by
            change next :: remaining ≠ []
            intro empty
            cases empty
          have tailBound := monomialNormSqSum_le_weighted
            tail radiusSq
            radialSq tailNonempty radiusNonnegative radiusBound oneLeRadial
          have powerBound := Fraction.Order.Arithmetic.pow_le_pow_direct
            radiusNonnegative radiusBound tail.length
          have firstBound :
              Data.Gaussian.Norm.Basic.normSq coefficient * radiusSq ^ tail.length ≤
                Data.Gaussian.Norm.Basic.normSq coefficient * (2 * radialSq) ^ tail.length :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              powerBound (Gaussian.Norm.Basic.normSq_nonneg coefficient)
          have radialNonnegative : 0 ≤ radialSq :=
            (by decide : (0 : Fraction.Rational) ≤ 1).trans oneLeRadial
          have radialPowerLift :
              radialSq ^ remaining.length ≤
                radialSq ^ (remaining.length + 1) := by
            calc
              radialSq ^ remaining.length =
                  radialSq ^ remaining.length * 1 := by ring1
              _ ≤ radialSq ^ remaining.length * radialSq :=
                Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                  oneLeRadial
                  (Fraction.Order.Arithmetic.pow_nonneg_direct
                    radialNonnegative remaining.length)
              _ = radialSq ^ (remaining.length + 1) := (pow_succ radialSq remaining.length).symm
          have weightedLift :
              weightedNormSum tail.reverse 0 *
                  radialSq ^ remaining.length ≤
                weightedNormSum tail.reverse 0 *
                  radialSq ^ (remaining.length + 1) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              radialPowerLift (weightedNormSum_nonneg tail.reverse 0)
          have tailLift :
              Dense.Gaussian.Evaluation.Norm.monomialNormSqSum tail radiusSq ≤
                weightedNormSum tail.reverse 0 *
                  radialSq ^ tail.length := by
            change Dense.Gaussian.Evaluation.Norm.monomialNormSqSum tail radiusSq ≤
              weightedNormSum tail.reverse 0 *
                radialSq ^ remaining.length at tailBound
            exact tailBound.trans weightedLift
          rw [Dense.Gaussian.Evaluation.Norm.monomialNormSqSum]
          rw [weightedNormSum_reverse_cons]
          simp only [List.length_cons]
          calc
            Data.Gaussian.Norm.Basic.normSq coefficient * radiusSq ^ (remaining.length + 1) +
                  Dense.Gaussian.Evaluation.Norm.monomialNormSqSum tail radiusSq ≤
                Data.Gaussian.Norm.Basic.normSq coefficient * (2 * radialSq) ^
                    (remaining.length + 1) +
                  weightedNormSum tail.reverse 0 *
                    radialSq ^ (remaining.length + 1) :=
              add_le_add firstBound tailLift
            _ = (weightedNormSum tail.reverse 0 +
                  Data.Gaussian.Norm.Basic.normSq coefficient * (2 : Fraction.Rational) ^
                    (remaining.length + 1)) *
                radialSq ^ (remaining.length + 1) := by
              ring1

end Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm.Weighted
