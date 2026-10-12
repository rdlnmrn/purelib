module
import Purelib.Algebra.Field.Ratio
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7 field-fragment examples

The book's two complex examples need only one explicitly supplied element
`i` satisfying `i²=-1`.  Keeping that finite field fragment abstract makes the
same proofs usable in admissible finite fields and in the constructive
Gaussian rationals; no completed complex carrier is introduced.
-/

namespace Purelib.Algebra.Field.Ratio.Finite

section ChapterSevenFieldFragments

variable {K : Type*} [ExplicitField K]

/-- Combine three fractions over their product denominator.

Every denominator is supplied as nonzero, so the common numerator is the sum of each numerator times the other two
denominators. -/
private theorem three_fraction_sum
    (firstNumerator secondNumerator thirdNumerator
      firstDenominator secondDenominator thirdDenominator : K)
    (firstNonzero : firstDenominator ≠ 0)
    (secondNonzero : secondDenominator ≠ 0)
    (thirdNonzero : thirdDenominator ≠ 0) :
    firstNumerator / firstDenominator +
        secondNumerator / secondDenominator +
        thirdNumerator / thirdDenominator =
      (firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator) /
        (firstDenominator * secondDenominator * thirdDenominator) := by
  have denominatorNonzero :
      firstDenominator * secondDenominator * thirdDenominator ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero firstNonzero secondNonzero) thirdNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (firstNumerator / firstDenominator +
          secondNumerator / secondDenominator +
          thirdNumerator / thirdDenominator) *
        (firstDenominator * secondDenominator * thirdDenominator) =
      (firstNumerator / firstDenominator * firstDenominator) *
          secondDenominator * thirdDenominator +
        (secondNumerator / secondDenominator * secondDenominator) *
          firstDenominator * thirdDenominator +
        (thirdNumerator / thirdDenominator * thirdDenominator) *
          firstDenominator * secondDenominator := by ring1
    _ = firstNumerator * secondDenominator * thirdDenominator +
        secondNumerator * firstDenominator * thirdDenominator +
        thirdNumerator * firstDenominator * secondDenominator := by
      rw [ExplicitField.div_mul_cancel firstNumerator firstNonzero,
        ExplicitField.div_mul_cancel secondNumerator secondNonzero,
        ExplicitField.div_mul_cancel thirdNumerator thirdNonzero]
    _ = ((firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator) /
        (firstDenominator * secondDenominator * thirdDenominator)) *
          (firstDenominator * secondDenominator * thirdDenominator) :=
      (ExplicitField.div_mul_cancel _ denominatorNonzero).symm

open Purelib in
/-- A retained cross-product equality identifies the sum of three fractions with a target fraction.

All four displayed denominators are nonzero, justifying the common-denominator reduction and final cancellation. -/
public theorem three_fraction_sum_eq
    (firstNumerator secondNumerator thirdNumerator targetNumerator
      firstDenominator secondDenominator thirdDenominator targetDenominator : K)
    (firstNonzero : firstDenominator ≠ 0)
    (secondNonzero : secondDenominator ≠ 0)
    (thirdNonzero : thirdDenominator ≠ 0)
    (targetNonzero : targetDenominator ≠ 0)
    (crossProduct :
      (firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator) *
          targetDenominator =
        targetNumerator *
          (firstDenominator * secondDenominator * thirdDenominator)) :
    firstNumerator / firstDenominator +
        secondNumerator / secondDenominator +
        thirdNumerator / thirdDenominator =
      targetNumerator / targetDenominator := open Purelib in by
  calc
    firstNumerator / firstDenominator +
          secondNumerator / secondDenominator +
          thirdNumerator / thirdDenominator =
        (firstNumerator * secondDenominator * thirdDenominator +
            secondNumerator * firstDenominator * thirdDenominator +
            thirdNumerator * firstDenominator * secondDenominator) /
          (firstDenominator * secondDenominator * thirdDenominator) :=
      three_fraction_sum firstNumerator secondNumerator thirdNumerator
        firstDenominator secondDenominator thirdDenominator firstNonzero
        secondNonzero thirdNonzero
    _ = targetNumerator / targetDenominator := by
      apply Algebra.Field.Ratio.ratio_eq_of_cross_product
        (ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero firstNonzero secondNonzero)
          thirdNonzero)
        targetNonzero
      exact crossProduct

/-- A retained cross-product equality identifies three fractions minus their product with a target fraction.

All four denominators are nonzero; the common numerator subtracts the product of the three original numerators. -/

public theorem three_fraction_sum_sub_product_eq
    (firstNumerator secondNumerator thirdNumerator targetNumerator
      firstDenominator secondDenominator thirdDenominator targetDenominator : K)
    (firstNonzero : firstDenominator ≠ 0)
    (secondNonzero : secondDenominator ≠ 0)
    (thirdNonzero : thirdDenominator ≠ 0)
    (targetNonzero : targetDenominator ≠ 0)
    (crossProduct :
      (firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator -
          firstNumerator * secondNumerator * thirdNumerator) *
          targetDenominator =
        targetNumerator *
          (firstDenominator * secondDenominator * thirdDenominator)) :
    firstNumerator / firstDenominator +
        secondNumerator / secondDenominator +
        thirdNumerator / thirdDenominator -
        (firstNumerator / firstDenominator) *
          (secondNumerator / secondDenominator) *
          (thirdNumerator / thirdDenominator) =
      targetNumerator / targetDenominator := open Purelib in by
  have denominatorNonzero :
      firstDenominator * secondDenominator * thirdDenominator ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero firstNonzero secondNonzero) thirdNonzero
  calc
    firstNumerator / firstDenominator +
          secondNumerator / secondDenominator +
          thirdNumerator / thirdDenominator -
          firstNumerator / firstDenominator *
            (secondNumerator / secondDenominator) *
            (thirdNumerator / thirdDenominator) =
        (firstNumerator * secondDenominator * thirdDenominator +
            secondNumerator * firstDenominator * thirdDenominator +
            thirdNumerator * firstDenominator * secondDenominator -
            firstNumerator * secondNumerator * thirdNumerator) /
          (firstDenominator * secondDenominator * thirdDenominator) := by
      apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
      calc
        (firstNumerator / firstDenominator +
              secondNumerator / secondDenominator +
              thirdNumerator / thirdDenominator -
              firstNumerator / firstDenominator *
                (secondNumerator / secondDenominator) *
                (thirdNumerator / thirdDenominator)) *
            (firstDenominator * secondDenominator * thirdDenominator) =
          (firstNumerator / firstDenominator * firstDenominator) *
                secondDenominator * thirdDenominator +
            (secondNumerator / secondDenominator * secondDenominator) *
                firstDenominator * thirdDenominator +
            (thirdNumerator / thirdDenominator * thirdDenominator) *
                firstDenominator * secondDenominator -
            (firstNumerator / firstDenominator * firstDenominator) *
              (secondNumerator / secondDenominator * secondDenominator) *
              (thirdNumerator / thirdDenominator * thirdDenominator) := by ring1
        _ = firstNumerator * secondDenominator * thirdDenominator +
              secondNumerator * firstDenominator * thirdDenominator +
              thirdNumerator * firstDenominator * secondDenominator -
              firstNumerator * secondNumerator * thirdNumerator := by
          rw [ExplicitField.div_mul_cancel firstNumerator firstNonzero,
            ExplicitField.div_mul_cancel secondNumerator secondNonzero,
            ExplicitField.div_mul_cancel thirdNumerator thirdNonzero]
        _ = ((firstNumerator * secondDenominator * thirdDenominator +
              secondNumerator * firstDenominator * thirdDenominator +
              thirdNumerator * firstDenominator * secondDenominator -
              firstNumerator * secondNumerator * thirdNumerator) /
            (firstDenominator * secondDenominator * thirdDenominator)) *
              (firstDenominator * secondDenominator * thirdDenominator) :=
          (ExplicitField.div_mul_cancel _ denominatorNonzero).symm
    _ = targetNumerator / targetDenominator := by
      apply Algebra.Field.Ratio.ratio_eq_of_cross_product denominatorNonzero targetNonzero
      exact crossProduct

/-- A retained cross-product equality identifies a squared fraction with a target fraction.

Both displayed denominators are nonzero, so numerator and denominator squares can be cleared and cancelled. -/

public theorem square_fraction_eq
    (numerator denominator targetNumerator targetDenominator : K)
    (denominatorNonzero : denominator ≠ 0)
    (targetNonzero : targetDenominator ≠ 0)
    (crossProduct :
      numerator ^ 2 * targetDenominator =
        targetNumerator * denominator ^ 2) :
    (numerator / denominator) ^ 2 =
      targetNumerator / targetDenominator := open Purelib in by
  have denominatorSquareNonzero : denominator ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero denominatorNonzero denominatorNonzero
  calc
    (numerator / denominator) ^ 2 = numerator ^ 2 / denominator ^ 2 := by
      apply ExplicitField.eq_of_mul_eq_mul_right denominatorSquareNonzero
      calc
        (numerator / denominator) ^ 2 * denominator ^ 2 =
            ((numerator / denominator) * denominator) ^ 2 := by ring1
        _ = numerator ^ 2 := by
          rw [ExplicitField.div_mul_cancel numerator denominatorNonzero]
        _ = (numerator ^ 2 / denominator ^ 2) * denominator ^ 2 :=
          (ExplicitField.div_mul_cancel _ denominatorSquareNonzero).symm
    _ = targetNumerator / targetDenominator :=
      Algebra.Field.Ratio.ratio_eq_of_cross_product denominatorSquareNonzero targetNonzero
        crossProduct

/-- Dividing a fraction by another nonzero scalar multiplies its denominator.

Both the original denominator and the additional divisor are supplied as nonzero. -/

public theorem fraction_div
    (numerator denominator divisor : K)
    (denominatorNonzero : denominator ≠ 0) (divisorNonzero : divisor ≠ 0) :
    (numerator / denominator) / divisor =
      numerator / (denominator * divisor) := by
  have productNonzero :=
    ExplicitField.mul_ne_zero denominatorNonzero divisorNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right productNonzero
  calc
    ((numerator / denominator) / divisor) * (denominator * divisor) =
        (((numerator / denominator) / divisor) * divisor) * denominator := by
      ring1
    _ = (numerator / denominator) * denominator := by
      rw [ExplicitField.div_mul_cancel _ divisorNonzero]
    _ = numerator :=
      ExplicitField.div_mul_cancel numerator denominatorNonzero
    _ = (numerator / (denominator * divisor)) *
        (denominator * divisor) :=
      (ExplicitField.div_mul_cancel numerator productNonzero).symm

end ChapterSevenFieldFragments

end Purelib.Algebra.Field.Ratio.Finite

end
