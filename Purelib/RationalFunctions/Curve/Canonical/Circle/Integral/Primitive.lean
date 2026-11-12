module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Tangent
public import Purelib.Integration.Polynomial.Gaussian.Cell.Taylor
public import Purelib.Polynomial.Ascending.Gaussian.Antiderivative.Reciprocal
public import Purelib.Polynomial.Ascending.Gaussian.Antiderivative.Taylor
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Reciprocal
public import Purelib.Geometry.Rational.Box.Square.Centered.Norm
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

import Purelib.Data.Gaussian.Basic
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation

/-!
# Actual circle cells and retained primitive comparisons

Each cell reads its coefficient on the supplied original circle curve at
its original left parameter. The exact circle tangent and a retained
primitive Taylor certificate bound its actual constant-polynomial integral
against independently computed primitive endpoint readings.
-/

public section

namespace Purelib.RationalFunctions.Curve.Canonical.Circle.Integral

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel LocalObservation)
open Purelib.Calculus.Jet.Quadratic.Basic (Certificate)
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Geometry.Rational.Box.Square

/-- Form an original constant cell from one actual coefficient reading and the same circle's tangent.

The supplied original curve is evaluated once. The coefficient, constant
polynomial and its exact left observation are each retained once; the two
cell endpoints remain the original rational parameter endpoints.
-/
@[expose] def coefficientCell (base : Canonical)
    (curve : { value : RationalCurve // value = circle base }) (coefficient : Canonical → Canonical)
    (time delta : Fraction.Rational) : CellModel :=
  let point := curve.val.point time
  let reading := velocity base time * coefficient point
  let polynomial := Ascending.Gaussian.Basic.constant reading
  let cell := CellModel.exact ⟨time, 0⟩ ⟨time + delta, 0⟩ polynomial
  { cell with observations :=
      [{ parameter := 0
         integrandReading := reading
         error := 0
         decomposition := by
           change reading - Ascending.Gaussian.Evaluation.eval
             (Ascending.Gaussian.Basic.constant reading) (⟨0, 0⟩ : Canonical) = 0
           rewrite [Ascending.Gaussian.Evaluation.eval_constant]
           exact Basic.sub_self reading
         error_le := by
           change Canonical.normSq (0 : Canonical) ≤ (0 : Fraction.Rational)
           decide +kernel }] }

/-- The same original constant cell retains exactly its original parameter displacement. -/
theorem coefficientCell_displacement (base : Canonical)
    (curve : { value : RationalCurve // value = circle base }) (coefficient : Canonical → Canonical)
    (time delta : Fraction.Rational) :
    (coefficientCell base curve coefficient time delta).displacement = Stereographic.Tangent.increment delta := by
  apply Basic.ext
  · change time + delta - time = delta
    ring1
  · change (0 : Fraction.Rational) - 0 = 0
    ring1

/-- The actual original cell sample is its parameter increment times its retained tangent and coefficient. -/
theorem coefficientCell_integralSample (base : Canonical)
    (curve : { value : RationalCurve // value = circle base }) (coefficient : Canonical → Canonical)
    (time delta : Fraction.Rational) :
    (coefficientCell base curve coefficient time delta).integralSample =
      Stereographic.Tangent.increment delta * (velocity base time * coefficient (curve.val.point time)) := by
  rewrite [CellModel.integralSample_constant _ _ rfl, coefficientCell_displacement]
  rfl

/-- A uniform primitive factor and slope ceiling pay the actual original circle cell's fourth-order error.

The certificate retains its independently prescribed spatial endpoints. The
coefficient is its exact first-order reading on the supplied original curve;
all movement and tangent bounds are derived from that same circle.
-/
theorem coefficientCell_error_le (base : Canonical)
    (curve : { value : RationalCurve // value = circle base }) (coefficient : Canonical → Canonical)
    (time delta : Fraction.Rational)
    (certificate : Certificate (curve.val.point (time + delta) - curve.val.point time))
    (slope : certificate.slope = coefficient (curve.val.point time))
    (factor coefficientBound : Fraction.Rational) (factor_le : certificate.factor ≤ factor)
    (coefficient_le : Norm.Basic.normSq certificate.slope ≤ coefficientBound) :
    Norm.Basic.normSq (certificate.output - certificate.base -
      (coefficientCell base curve coefficient time delta).integralSample) ≤
      (2 * (factor * (4 * Norm.Basic.normSq base) ^ 2 +
        8 * Norm.Basic.normSq base * coefficientBound)) * delta ^ 4 := by
  have stepNorm : Norm.Basic.normSq (Stereographic.Tangent.increment delta) = delta ^ 2 := by
    change delta ^ 2 + 0 ^ 2 = delta ^ 2
    ring1
  have movement : Norm.Basic.normSq (curve.val.point (time + delta) - curve.val.point time) ≤
      (4 * Norm.Basic.normSq base) * Norm.Basic.normSq (Stereographic.Tangent.increment delta) := by
    rewrite [curve.property, stepNorm]
    exact movement_normSq_le base time delta
  have tangent : Norm.Basic.normSq (curve.val.point (time + delta) - curve.val.point time -
      Stereographic.Tangent.increment delta * velocity base time) ≤
      (4 * Norm.Basic.normSq base) * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    rewrite [curve.property, stepNorm]
    exact (remainder_normSq_le base time delta).trans_eq (by ring1)
  have exactCoefficient : Norm.Basic.normSq (certificate.slope - coefficient (curve.val.point time)) ≤
      0 * Norm.Basic.normSq (Stereographic.Tangent.increment delta) := by
    rewrite [slope, Basic.sub_self, Norm.Basic.normSq_zero, Fraction.Field.zero_mul_direct]
    exact Fraction.Order.Basic.le_refl _
  have original := CellModel.charted_quadratic_integral_error_le certificate
    (coefficientCell base curve coefficient time delta) (Stereographic.Tangent.increment delta)
    (velocity base time) (coefficient (curve.val.point time))
    (coefficientCell_displacement base curve coefficient time delta) rfl
    (4 * Norm.Basic.normSq base) (4 * Norm.Basic.normSq base) (4 * Norm.Basic.normSq base) 0
    (by decide +kernel) movement tangent (velocity_normSq_le base time) exactCoefficient
  have factorPayment := Arithmetic.mul_le_mul_of_nonneg_right_direct factor_le
    (Arithmetic.sq_nonneg_direct (4 * Norm.Basic.normSq base))
  have coefficientPayment := Arithmetic.mul_le_mul_of_nonneg_left_direct coefficient_le
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
      (Norm.Basic.normSq_nonneg base))
  have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct factorPayment
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct coefficientPayment
            (Fraction.Order.Basic.le_refl ((4 * Norm.Basic.normSq base) * 0)))
          (by decide +kernel : (0 : Fraction.Rational) ≤ 2)))
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2))
    (Arithmetic.sq_nonneg_direct (Norm.Basic.normSq (Stereographic.Tangent.increment delta)))
  exact original.trans (paid.trans_eq (by rewrite [stepNorm]; ring1))

/-- The computed original square enclosing every point of the same supplied circle. -/
@[expose] def circleBox (base : Canonical) : Geometry.Rational.Box :=
  Centered.normBox (Norm.Basic.normSq base) (Norm.Basic.normSq_nonneg base)

/-- Every actual supplied circle point belongs to the same computed original circle box. -/
theorem circleBox_contains (base : Canonical)
    (curve : { value : RationalCurve // value = circle base }) (time : Fraction.Rational) :
    (circleBox base).Contains (curve.val.point time) := by
  apply Centered.normBox_contains
  rewrite [curve.property, point_normSq]
  exact Fraction.Order.Basic.le_refl _

/-- The computed original square enclosing every inverse point of the same nonzero circle. -/
@[expose] def reciprocalBox (base : Canonical) (nonzero : base ≠ 0) : Geometry.Rational.Box :=
  Centered.normBox (Norm.Basic.normSq base)⁻¹
    (Fraction.Order.Field.inv_pos_direct (Norm.Basic.normSq_pos nonzero)).le

/-- The actual inverse of each supplied original circle point belongs to the same computed reciprocal box. -/
theorem reciprocalBox_contains (base : Canonical) (nonzero : base ≠ 0)
    (curve : { value : RationalCurve // value = circle base }) (time : Fraction.Rational) :
    (reciprocalBox base nonzero).Contains (curve.val.point time)⁻¹ := by
  apply Centered.normBox_contains
  apply Norm.Reciprocal.normSq_le (Norm.Basic.normSq_pos nonzero)
  rewrite [curve.property, point_normSq]
  exact Fraction.Order.Basic.le_refl _

/-- The retained regular polynomial primitive bounds the actual same-curve constant cell.

The original numerator, retained antiderivative, boxed primitive and Horner
coefficient ceiling are all consumed from the supplied preparation. No
primitive endpoint is defined from the cell's integral output.
-/
theorem polynomialCell_error_le (base : Canonical)
    (curve : { value : RationalCurve // value = circle base })
    (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source })
    (preparation : Antiderivative.BoxPreparation source retained (circleBox base))
    (time delta : Fraction.Rational) :
    Norm.Basic.normSq (Evaluation.eval retained.val (curve.val.point (time + delta)) -
      Evaluation.eval retained.val (curve.val.point time) -
        (coefficientCell base curve (Evaluation.eval source) time delta).integralSample) ≤
      (2 * (preparation.1.val.remainderBound * (4 * Norm.Basic.normSq base) ^ 2 +
        8 * Norm.Basic.normSq base * preparation.2.val)) * delta ^ 4 := by
  let certificate := preparation.1.val.quadraticCertificate (curve.val.point time)
    (curve.val.point (time + delta)) (circleBox_contains base curve time)
    (circleBox_contains base curve (time + delta))
  have actualValue : preparation.1.val.value = Dense.Evaluation.toDense retained.val :=
    (congrArg (fun value => value.value) preparation.1.property).trans
      (Antiderivative.inBox_value source retained (circleBox base))
  have slope : certificate.slope = Evaluation.eval source (curve.val.point time) :=
    Dense.Evaluation.toDense_eval _ _
  have bounded : Norm.Basic.normSq certificate.slope ≤ preparation.2.val := by
    rewrite [preparation.2.property]
    exact Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound _ (circleBox_contains base curve time)
  have original := coefficientCell_error_le base curve (Evaluation.eval source) time delta certificate slope
    preparation.1.val.remainderBound preparation.2.val (Fraction.Order.Basic.le_refl _) bounded
  change Norm.Basic.normSq (preparation.1.val.value.eval (curve.val.point (time + delta)) -
    preparation.1.val.value.eval (curve.val.point time) - _) ≤ _ at original
  rewrite [actualValue, Dense.Evaluation.toDense_eval, Dense.Evaluation.toDense_eval] at original
  exact original

/-- The retained reciprocal primitive bounds the actual same-curve nonlogarithmic Laurent cell.

Both inverse points receive their nonzero floor internally from the actual
circle. The original boxed numerator and retained antiderivative provide the
coefficient and uniform quadratic factor; the actual constant cell consumes
the original nonlogarithmic coefficient reading.
-/
theorem reciprocalCell_error_le (base : Canonical) (nonzero : base ≠ 0)
    (curve : { value : RationalCurve // value = circle base })
    {source : CoefficientPolynomial} {order : Nat}
    (retained : Antiderivative.ReciprocalPrimitive source order)
    (preparation : Antiderivative.BoxPreparation retained.1.val retained.2 (reciprocalBox base nonzero))
    (time delta : Fraction.Rational) :
    Norm.Basic.normSq (retained.value (curve.val.point (time + delta)) - retained.value (curve.val.point time) -
      (coefficientCell base curve retained.derivativeValue time delta).integralSample) ≤
      (2 * (preparation.1.val.reciprocalFactor (Norm.Basic.normSq base) preparation.2 *
          (4 * Norm.Basic.normSq base) ^ 2 +
        8 * Norm.Basic.normSq base * (preparation.2.val * (Norm.Basic.normSq base)⁻¹ ^ 2))) * delta ^ 4 := by
  have floor (parameter : Fraction.Rational) :
      Norm.Basic.normSq base ≤ Norm.Basic.normSq (curve.val.point parameter) := by
    rewrite [curve.property, point_normSq]
    exact Fraction.Order.Basic.le_refl _
  let certificate := preparation.1.val.reciprocalCertificate (Norm.Basic.normSq_pos nonzero) preparation.2
    (curve.val.point time) (curve.val.point (time + delta)) (floor time) (floor (time + delta))
    (reciprocalBox_contains base nonzero curve time) (reciprocalBox_contains base nonzero curve (time + delta))
  have actualValue : preparation.1.val.value = Dense.Evaluation.toDense retained.2.val :=
    (congrArg (fun value => value.value) preparation.1.property).trans
      (Antiderivative.inBox_value retained.1.val retained.2 (reciprocalBox base nonzero))
  have slope : certificate.slope = retained.derivativeValue (curve.val.point time) := by
    change (Dense.Evaluation.toDense retained.1.val).eval (curve.val.point time)⁻¹ *
      (curve.val.point time)⁻¹ ^ 2 = _
    rewrite [Dense.Evaluation.toDense_eval]
    rfl
  have bounded : Norm.Basic.normSq certificate.slope ≤
      preparation.2.val * (Norm.Basic.normSq base)⁻¹ ^ 2 := by
    change Norm.Basic.normSq ((Dense.Evaluation.toDense retained.1.val).eval (curve.val.point time)⁻¹ *
      (curve.val.point time)⁻¹ ^ 2) ≤ _
    rewrite [Norm.Basic.normSq_mul]
    have coefficientBounded : Norm.Basic.normSq
        ((Dense.Evaluation.toDense retained.1.val).eval (curve.val.point time)⁻¹) ≤ preparation.2.val := by
      rewrite [preparation.2.property]
      exact Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound _
        (reciprocalBox_contains base nonzero curve time)
    exact Arithmetic.mul_le_mul_direct coefficientBounded
      (Norm.Reciprocal.power_normSq_le (Norm.Basic.normSq_pos nonzero) (floor time) 2)
      (Norm.Basic.normSq_nonneg _) ((Norm.Basic.normSq_nonneg _).trans coefficientBounded)
  have original := coefficientCell_error_le base curve retained.derivativeValue time delta certificate slope
    (preparation.1.val.reciprocalFactor (Norm.Basic.normSq base) preparation.2)
    (preparation.2.val * (Norm.Basic.normSq base)⁻¹ ^ 2) (Fraction.Order.Basic.le_refl _) bounded
  change Norm.Basic.normSq (-preparation.1.val.value.eval (curve.val.point (time + delta))⁻¹ -
    -preparation.1.val.value.eval (curve.val.point time)⁻¹ - _) ≤ _ at original
  rewrite [actualValue, Dense.Evaluation.toDense_eval, Dense.Evaluation.toDense_eval] at original
  exact original

end Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
