module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

namespace Purelib.Polynomial.Clearance.Pair.Dominance

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

/-- Construct quantitative sum-path clearance from a displayed positive squared-norm margin.

The original positive margin and coordinate-sum identities determine
the sum path clearance. Its cached bound uses the same margin square,
factor four and maximum of one with the retained dominant Horner sum. -/
@[expose] public def sumCertificate_of_normDominance
    {A B C D U V : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (margin : Fraction.Rational) (marginPositive : 0 < margin)
    (dominance : ∀ x : Fraction.Rational, root.Contains x →
      margin ≤ A.eval x ^ 2 + B.eval x ^ 2 -
        (C.eval x ^ 2 + D.eval x ^ 2))
    (sumReal : ∀ x : Fraction.Rational,
      U.eval x = A.eval x + C.eval x)
    (sumImag : ∀ x : Fraction.Rational,
      V.eval x = B.eval x + D.eval x) :
    Clearance.Pair.Basic.Certificate U V root := by
  let majorant := max 1
    (Dense.Rational.Bounds.Horner.evalSqBound A root +
      Dense.Rational.Bounds.Horner.evalSqBound B root)
  have majorantPositive : 0 < majorant := by
    dsimp only [majorant]
    exact (show (0 : Fraction.Rational) < 1 by decide).trans_le
      (Fraction.Order.Basic.le_max_left _ _)
  let denominator := 4 * majorant
  have denominatorPositive : 0 < denominator :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) majorantPositive
  exact
    { bound := margin ^ 2 / denominator
      positive := Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Arithmetic.pow_pos_direct marginPositive 2)
        denominatorPositive
      lower := by
        intro x inside
        let leftSq := A.eval x ^ 2 + B.eval x ^ 2
        let sumSq := U.eval x ^ 2 + V.eval x ^ 2
        let dot := A.eval x * U.eval x + B.eval x * V.eval x
        have leftSqNonnegative : 0 ≤ leftSq :=
          add_nonneg
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        have sumSqNonnegative : 0 ≤ sumSq :=
          add_nonneg
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        have leftSqBound : leftSq ≤ majorant := by
          dsimp only [leftSq, majorant]
          exact (add_le_add
            (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound A root inside)
            (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound B root inside)).trans
            (Fraction.Order.Basic.le_max_right _ _)
        have doubledDot : 2 * dot =
            (A.eval x ^ 2 + B.eval x ^ 2 -
              (C.eval x ^ 2 + D.eval x ^ 2)) + sumSq := by
          dsimp only [dot, sumSq]
          rw [sumReal x, sumImag x]
          ring1
        have marginLeDoubledDot : margin ≤ 2 * dot := by
          rw [doubledDot]
          exact (dominance x inside).trans
            (le_add_of_nonneg_right sumSqNonnegative)
        have doubledDotNonnegative : 0 ≤ 2 * dot :=
          marginPositive.le.trans marginLeDoubledDot
        have squaredMargin : margin ^ 2 ≤ (2 * dot) ^ 2 :=
          Fraction.Order.Arithmetic.pow_le_pow_direct marginPositive.le
            marginLeDoubledDot 2
        have dotCauchy : dot ^ 2 ≤ leftSq * sumSq := by
          dsimp only [dot, leftSq, sumSq]
          exact Bounds.Square.dot_sq_le_product_sums _ _ _ _
        have scaledCauchy : (2 * dot) ^ 2 ≤
            denominator * sumSq := by
          calc
            (2 * dot) ^ 2 = 4 * dot ^ 2 := by ring1
            _ ≤ 4 * (leftSq * sumSq) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                dotCauchy (by decide)
            _ ≤ 4 * (majorant * sumSq) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
                  leftSqBound sumSqNonnegative) (by decide)
            _ = denominator * sumSq := by
              dsimp only [denominator]
              ring1
        apply (Fraction.Order.Field.div_le_iff_pos
          denominatorPositive).2
        rw [Fraction.Field.mul_comm sumSq denominator]
        exact squaredMargin.trans scaledCauchy }

/-- Exact rational bound cached by the finite norm-dominance constructor.

The certificate caches the square of the supplied original margin
divided by four times its retained dominant-path Horner majorant.
This equation is its exact rational field readback. -/
@[simp] public theorem sumCertificate_of_normDominance_bound
    {A B C D U V : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (margin : Fraction.Rational) (marginPositive : 0 < margin)
    (dominance : ∀ x : Fraction.Rational, root.Contains x →
      margin ≤ A.eval x ^ 2 + B.eval x ^ 2 -
        (C.eval x ^ 2 + D.eval x ^ 2))
    (sumReal : ∀ x : Fraction.Rational,
      U.eval x = A.eval x + C.eval x)
    (sumImag : ∀ x : Fraction.Rational,
      V.eval x = B.eval x + D.eval x) :
    (sumCertificate_of_normDominance margin marginPositive dominance sumReal
      sumImag).bound =
      margin ^ 2 /
        (4 * max 1
          (Dense.Rational.Bounds.Horner.evalSqBound A root +
            Dense.Rational.Bounds.Horner.evalSqBound B root)) := rfl

end Purelib.Polynomial.Clearance.Pair.Dominance
