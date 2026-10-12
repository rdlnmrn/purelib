module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
public import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
public import Purelib.Polynomial.Clearance.Pair.Operations
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Algebra.Semiring.Normalization

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Dominance

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.Rat.Fraction.Order
open Purelib.Algebra.Semiring

/-- Quantitative dominance of the next signed remainder over an unresolved
middle member after multiplying by the displayed quotient.

The original middle Lipschitz bound, squared endpoint radius and
quotient square majorant are retained in one strict comparison with
the same adjacent-pair clearance. -/
@[expose] public def DominanceResolution
    (q quotient next : Dense.Rational.Basic.CoordinatePolynomial) {interval : Data.Rat.Interval.Bounds}
    (rightClearance : Clearance.Pair.Basic.Certificate q next interval) : Prop :=
  Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval *
      Interval.Radius.sampleRadiusSq interval interval.lower *
      (Dense.Rational.Bounds.Horner.evalSqBound quotient interval + 1) <
    rightClearance.bound

/-- Decide the signed-remainder dominance inequality using exact rational comparison. -/
public instance (q quotient next : Dense.Rational.Basic.CoordinatePolynomial) {interval : Data.Rat.Interval.Bounds}
    (rightClearance : Clearance.Pair.Basic.Certificate q next interval) :
    Decidable (DominanceResolution q quotient next rightClearance) := by
  unfold DominanceResolution
  infer_instance

/-- Positive ambient squared radius forcing the signed-remainder dominance
test on every displayed refinement.

The original middle Lipschitz and quotient square bounds form the
retained denominator coefficient. Increasing it by one gives the
exact positive squared-radius threshold for the same clearance. -/
@[expose] public def dominanceResolutionRadiusSq
    (q quotient next : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
    (rightClearance : Clearance.Pair.Basic.Certificate q next root) : Fraction.Rational :=
  rightClearance.bound /
    (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q root *
      (Dense.Rational.Bounds.Horner.evalSqBound quotient root + 1) + 1)

/-- Positive adjacent-pair clearance gives a positive ambient squared-radius threshold for remainder dominance.

The retained Lipschitz and quotient factors are nonnegative. Their
product increased by one is positive, so division of the same positive
clearance gives a positive threshold. -/
public theorem dominanceResolutionRadiusSq_pos
    (q quotient next : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
    (rightClearance : Clearance.Pair.Basic.Certificate q next root) :
    0 < dominanceResolutionRadiusSq q quotient next rightClearance := by
  apply Fraction.Order.Field.div_pos_direct
  · exact rightClearance.positive
  · have coefficientNonnegative : 0 ≤
        Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q root *
          (Dense.Rational.Bounds.Horner.evalSqBound quotient root + 1) :=
      Arithmetic.mul_nonneg_direct
        (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg q root).2
        (add_nonneg
          (Dense.Rational.Bounds.Horner.evalSqBound_nonneg quotient root)
          (by decide))
    calc
      0 < 1 := by decide
      _ ≤ Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q root *
          (Dense.Rational.Bounds.Horner.evalSqBound quotient root + 1) + 1 := by
        exact add_le_add coefficientNonnegative (le_refl 1)

/-- Every refined interval below the computed radius threshold satisfies the signed-remainder dominance inequality.

The refinement decreases the original middle and quotient bounds.
Multiplication by the same nonnegative local endpoint radius and
the retained positive denominator transports the original clearance. -/
public theorem dominanceResolution_of_refined_radiusSq
    {q quotient next : Dense.Rational.Basic.CoordinatePolynomial}
    {root interval : Data.Rat.Interval.Bounds}
    (rightClearance : Clearance.Pair.Basic.Certificate q next root)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      dominanceResolutionRadiusSq q quotient next rightClearance) :
    DominanceResolution q quotient next (rightClearance.restrict refines) := by
  let localCoefficient := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval *
    (Dense.Rational.Bounds.Horner.evalSqBound quotient interval + 1)
  let rootCoefficient := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q root *
    (Dense.Rational.Bounds.Horner.evalSqBound quotient root + 1)
  let localRadius := Interval.Radius.sampleRadiusSq interval interval.lower
  have localRadiusNonnegative : 0 ≤ localRadius := Interval.Radius.sampleRadiusSq_nonneg interval
  have localFactorNonnegative : 0 ≤
      Dense.Rational.Bounds.Horner.evalSqBound quotient interval + 1 :=
    add_nonneg
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg quotient interval)
      (by decide)
  have rootLipschitzNonnegative :
      0 ≤ Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q root :=
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg q root).2
  have coefficientLe : localCoefficient ≤ rootCoefficient :=
    Arithmetic.mul_le_mul_direct
      (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines q refines)
      (add_le_add
        (Dense.Rational.Bounds.Horner.evalSqBound_le_of_refines
          quotient refines)
        (le_refl 1))
      localFactorNonnegative rootLipschitzNonnegative
  have rootCoefficientNonnegative : 0 ≤ rootCoefficient :=
    Arithmetic.mul_nonneg_direct rootLipschitzNonnegative
      (add_nonneg
        (Dense.Rational.Bounds.Horner.evalSqBound_nonneg quotient root)
        (by decide))
  have denominatorPositive : 0 < rootCoefficient + 1 := by
    calc
      0 < 1 := by decide
      _ ≤ rootCoefficient + 1 := by
        exact add_le_add rootCoefficientNonnegative (le_refl 1)
  have scaledRadius : (rootCoefficient + 1) * localRadius <
      rightClearance.bound := by
    calc
      (rootCoefficient + 1) * localRadius <
          (rootCoefficient + 1) *
            dominanceResolutionRadiusSq q quotient next rightClearance :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          denominatorPositive radius
      _ = rightClearance.bound := by
        dsimp only [dominanceResolutionRadiusSq]
        rw [Fraction.Field.mul_comm]
        apply Fraction.Field.div_mul_cancel_of_ne
        simpa only [rootCoefficient] using denominatorPositive.ne'
  change Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval * localRadius *
      (Dense.Rational.Bounds.Horner.evalSqBound quotient interval + 1) <
    rightClearance.bound
  calc
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval * localRadius *
        (Dense.Rational.Bounds.Horner.evalSqBound quotient interval + 1) =
        localCoefficient * localRadius := by
      dsimp only [localCoefficient, localRadius]
      ring1
    _ ≤ rootCoefficient * localRadius :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe localRadiusNonnegative
    _ ≤ (rootCoefficient + 1) * localRadius :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right (by decide)) localRadiusNonnegative
    _ < rightClearance.bound := scaledRadius

/-- If the middle member is unresolved, quantitative dominance makes its quotient product strictly smaller in square
than the next remainder at the lower endpoint.

The unresolved middle margin weakly bounds its original endpoint
square. Quotient dominance and the same adjacent-pair clearance
leave its retained quotient product below the next endpoint square. -/
public theorem product_eval_sq_lt_next_eval_sq_of_dominance
    {q quotient next : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (rightClearance : Clearance.Pair.Basic.Certificate q next interval)
    (dominance : DominanceResolution
      q quotient next rightClearance)
    (qUnresolved : ¬(
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval *
          Interval.Radius.sampleRadiusSq interval interval.lower <
        q.eval interval.lower ^ 2)) :
    (q.eval interval.lower * quotient.eval interval.lower) ^ 2 <
      next.eval interval.lower ^ 2 := by
  let radius := Interval.Radius.sampleRadiusSq interval interval.lower
  let qMargin := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval * radius
  let quotientBound :=
    Dense.Rational.Bounds.Horner.evalSqBound quotient interval
  have qSqBound : q.eval interval.lower ^ 2 ≤ qMargin :=
    Arithmetic.le_of_not_gt_direct qUnresolved
  have quotientSqBound : quotient.eval interval.lower ^ 2 ≤ quotientBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound quotient interval ⟨le_rfl, interval.valid⟩
  have qMarginNonnegative : 0 ≤ qMargin :=
    Arithmetic.mul_nonneg_direct
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg q interval).2
      (Interval.Radius.sampleRadiusSq_nonneg interval)
  have quotientSqNonnegative :=
    Arithmetic.sq_nonneg_direct
      (quotient.eval interval.lower)
  have productBound :
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 ≤
        qMargin * quotientBound :=
    Arithmetic.mul_le_mul_direct qSqBound quotientSqBound
      quotientSqNonnegative qMarginNonnegative
  have lower := rightClearance.lower
    interval.lower ⟨le_rfl, interval.valid⟩
  have sumBelow :
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 +
          q.eval interval.lower ^ 2 <
        q.eval interval.lower ^ 2 + next.eval interval.lower ^ 2 := by
    calc
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 +
          q.eval interval.lower ^ 2 ≤
          qMargin * quotientBound + qMargin :=
        add_le_add productBound qSqBound
      _ = qMargin * (quotientBound + 1) := by ring1
      _ < rightClearance.bound := dominance
      _ ≤ q.eval interval.lower ^ 2 + next.eval interval.lower ^ 2 :=
        lower
  have shifted : q.eval interval.lower ^ 2 +
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 <
      q.eval interval.lower ^ 2 + next.eval interval.lower ^ 2 := by
    simpa only [add_comm] using sumBelow
  have productLess :
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 <
        next.eval interval.lower ^ 2 := by
    apply Arithmetic.lt_of_add_lt_add_right_direct (c := q.eval interval.lower ^ 2)
    rw [Fraction.Field.add_comm
        (q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2)
        (q.eval interval.lower ^ 2),
      Fraction.Field.add_comm (next.eval interval.lower ^ 2) (q.eval interval.lower ^ 2)]
    exact shifted
  have productIdentity := Normalization.product_pow
    (q.eval interval.lower) (quotient.eval interval.lower) 2
  rw [productIdentity]
  exact productLess

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Dominance
