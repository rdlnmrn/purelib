module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Calculus.Jet.Quadratic.SquareRoot.Radicand
public import Purelib.Calculus.Jet.Quadratic.Polynomial
public import Purelib.Calculus.Jet.Quadratic.Product
import Purelib.Calculus.Jet.Quadratic.Arithmetic
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
public import Purelib.Geometry.Rational.Box.Outside.Sum
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate.Derivative
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Spatial Taylor bounds on two original paid sheet observations

The original curve and primitive numerator receive polynomial certificates
on one fixed spatial box. Both original root processes retain their actual
selected readings and separate square-residual payments. Their signed window
supplies denominator and sum floors; a fixed inverse box bounds the original
finite power polynomial. Every remainder ceiling depends only on those
boxes, margins and original primitive data, independently of mesh size.

The scalar product-rule slope retains the actual polynomial and reciprocal
composition. Comparing it with independently observed derivative names and
constructing a primitive edge integral are subsequent paid comparisons.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Taylor

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Calculus.Jet
open Purelib.Calculus.Jet.Quadratic
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Riemann.RootContinuation

variable {radicand : Pair.Polynomial.Coefficients}

/-- The retained finite coordinate-power polynomial has exactly the original primitive's odd exponent. -/
@[expose] def powerPolynomial (primitive : OddPowerDifferential radicand) : CoefficientPolynomial :=
  Power.Coordinate.coordinatePositivePower (2 * primitive.denominatorPairs)

/-- The retained power polynomial evaluates to exactly the original primitive's odd scalar power. -/
theorem powerPolynomial_eval (primitive : OddPowerDifferential radicand) (point : Canonical) :
    (powerPolynomial primitive).eval point = point ^ primitive.denominatorExponent :=
  Power.Coordinate.coordinatePositivePower_eval (2 * primitive.denominatorPairs) point

/-- The original odd-power polynomial derivative retains the exponent coefficient of the same primitive.

The original coordinate-power derivative and exact exponent-cast readback
preserve the retained polynomial and coefficient owners pointwise.
-/
theorem powerPolynomial_derivative_eval (primitive : OddPowerDifferential radicand) (point : Canonical) :
    (GCD.derivative (powerPolynomial primitive)).eval point =
      exponentCoefficient primitive * point ^ (2 * primitive.denominatorPairs) := by
  unfold powerPolynomial
  rewrite [Power.Coordinate.derivative_eval, exponentCoefficient_eq_intCast]
  rfl

/-- The spatial derivative ceiling is computed by the original derivative and box Horner algorithms. -/
@[expose] def slopeCeiling (polynomial : CoefficientPolynomial) (box : Box) : Fraction.Rational :=
  Bounds.Box.denseEvalNormBound (GCD.derivative polynomial) box

/-- The spatial remainder ceiling is the original polynomial's finite box Taylor scan. -/
@[expose] def remainderCeiling (polynomial : CoefficientPolynomial) (box : Box) : Fraction.Rational :=
  Bounds.Box.Taylor.denseEvalTaylorRemainderBound polynomial box

/-- The computed inverse-sheet slope ceiling retains the original curve derivative budget and denominator floor. -/
@[expose] def inverseSlopeCeiling (polynomial : CoefficientPolynomial) (box : Box)
    (floor : Fraction.Rational) : Fraction.Rational :=
  slopeCeiling polynomial box * floor⁻¹ ^ 3

/-- Both unit-factor residual payments and the original radicand box factor determine the uniform inverse remainder. -/
@[expose] def inverseCeiling (polynomial : CoefficientPolynomial) (box : Box)
    (floor : Fraction.Rational) : Fraction.Rational :=
  let error := 2 * (remainderCeiling polynomial box + 4)
  let movement := 2 * (slopeCeiling polynomial box + error) * (4 * floor)⁻¹
  let root := 2 * (error + movement ^ 2) * floor⁻¹
  2 * (floor⁻¹ ^ 2 * root + floor⁻¹ ^ 3 * (2 * (slopeCeiling polynomial box * floor⁻¹ + root)) ^ 2)

/-- The original finite reciprocal-power composition receives a ceiling from the retained inverse box. -/
@[expose] def powerCeiling (polynomial : CoefficientPolynomial) (primitive : OddPowerDifferential radicand)
    (box inverseBox : Box) (floor : Fraction.Rational) : Fraction.Rational :=
  let inverse := inverseCeiling polynomial box floor
  2 * (slopeCeiling (powerPolynomial primitive) inverseBox * inverse +
    remainderCeiling (powerPolynomial primitive) inverseBox *
      (2 * (inverseSlopeCeiling polynomial box floor + inverse)) ^ 2)

/-- The primitive's product and scale receive a ceiling depending only on its original boxes and signed floor. -/
@[expose] def ceiling (polynomial : CoefficientPolynomial) (primitive : OddPowerDifferential radicand)
    (box inverseBox : Box) (floor : Fraction.Rational) : Fraction.Rational :=
  let numerator := remainderCeiling primitive.numerator box
  let power := powerCeiling polynomial primitive box inverseBox floor
  let numeratorSensitivity := 2 * (slopeCeiling primitive.numerator box + numerator)
  let powerSensitivity := 2 * (inverseSlopeCeiling polynomial box floor *
    slopeCeiling (powerPolynomial primitive) inverseBox + power)
  Norm.Basic.normSq primitive.scale *
    (4 * (floor⁻¹ ^ primitive.denominatorExponent * numerator +
      Bounds.Box.denseEvalNormBound primitive.numerator box * power + numeratorSensitivity * powerSensitivity))

/-- The original fourth-order request pays one actual retained root observation with a unit residual factor. -/
private theorem paid_residual {parameter increment : Canonical}
    {root : CertifiedSquareRoot.Certificate parameter} {accuracy : Approximation.AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation root accuracy)
    (accuracy_eq : accuracy.tolerance = Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq (sample.reading * sample.reading - parameter) ≤
      1 * Norm.Basic.normSq increment ^ 2 := by
  rewrite [Fraction.Field.one_mul]
  exact sample.reading_residual_lt.le.trans_eq accuracy_eq

/-- The original half has squared norm at most one. -/
private theorem half_norm : Norm.Basic.normSq SquareRoot.half ≤ 1 := by decide +kernel

/-- A retained certificate's original slope and factor bounds give its uniform movement ceiling. -/
private theorem sensitivity_le {increment : Canonical} (certificate : Quadratic.Basic.Certificate increment)
    {slope factor : Fraction.Rational} (slopeBound : Norm.Basic.normSq certificate.slope ≤ slope)
    (factorBound : certificate.factor ≤ factor) : certificate.sensitivity ≤ 2 * (slope + factor) := by
  unfold Quadratic.Basic.Certificate.sensitivity
  rewrite [← Norm.Basic.normSq_eq_canonical]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct slopeBound factorBound) (by decide +kernel)

set_option genInjectivity false in
/-- A uniform spatial expansion indexed by both original certificate owners and their actual selected observations.

The original curve, primitive, spatial points, finite boxes and signed window
remain indices. Actual observed sheet readings give the base and output;
the fixed ceiling bounds the retained quadratic certificate's factor.
-/
structure Expansion (polynomial : CoefficientPolynomial) (primitive : OddPowerDifferential polynomial)
    (box inverseBox window : Box) (side : Box.OutsideSide window 0) (first last : Canonical)
    (source : CertifiedSquareRoot.Certificate (polynomial.eval first))
    (target : CertifiedSquareRoot.Certificate (polynomial.eval last))
    (accuracy : Approximation.AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target accuracy) where
  /-- Both actual selected observations pay the original spatial increment's fourth-order request. -/
  accuracy_eq : accuracy.tolerance = Norm.Basic.normSq (last - first) ^ 2
  /-- The original selected source sheet reading retains the supplied signed window. -/
  sourceInside : window.Contains sourceSample.reading
  /-- The distinct selected target sheet reading retains that same original signed window. -/
  targetInside : window.Contains targetSample.reading
  /-- The actual finite Taylor certificate constructed from these exact original inputs. -/
  certificate : Quadratic.Basic.Certificate (last - first)
  /-- The base is the original primitive coefficient at the actual selected source reading. -/
  base_eq : certificate.base =
    primitive.scale * primitive.numerator.eval first * sourceSample.reading⁻¹ ^ primitive.denominatorExponent
  /-- The output is the original primitive coefficient at the distinct selected target reading. -/
  output_eq : certificate.output =
    primitive.scale * primitive.numerator.eval last * targetSample.reading⁻¹ ^ primitive.denominatorExponent
  /-- The slope retains the original numerator and reciprocal-power polynomial derivative composition. -/
  slope_eq : certificate.slope = primitive.scale *
    ((GCD.derivative primitive.numerator).eval first * sourceSample.reading⁻¹ ^ primitive.denominatorExponent +
      primitive.numerator.eval first *
        (-(SquareRoot.half * (GCD.derivative polynomial).eval first * sourceSample.reading⁻¹ ^ 3) *
          (GCD.derivative (powerPolynomial primitive)).eval sourceSample.reading⁻¹))
  /-- The constructed factor is paid by the retained fixed boxes and original signed denominator margin. -/
  factor_le : certificate.factor ≤ ceiling polynomial primitive box inverseBox side.margin

constructive_injectivity Expansion

/-- Construct the original primitive's uniform finite expansion from both actual paid sheet observations.

The supplied finite containments concern the original spatial points and
selected sheet readings. The original polynomial builders construct both
radicand and numerator expansions. Signed-window margins derive denominator
and sum payments before reciprocal, finite-power and product composition.
-/
def build (polynomial : CoefficientPolynomial) (primitive : OddPowerDifferential polynomial)
    (box inverseBox window : Box) (side : Box.OutsideSide window 0) (first last : Canonical)
    (source : CertifiedSquareRoot.Certificate (polynomial.eval first))
    (target : CertifiedSquareRoot.Certificate (polynomial.eval last))
    (accuracy : Approximation.AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target accuracy)
    (accuracy_eq : accuracy.tolerance = Norm.Basic.normSq (last - first) ^ 2)
    (firstInside : box.Contains first) (lastInside : box.Contains last)
    (sourceInside : window.Contains sourceSample.reading) (targetInside : window.Contains targetSample.reading)
    (sourceInverseInside : inverseBox.Contains sourceSample.reading⁻¹)
    (targetInverseInside : inverseBox.Contains targetSample.reading⁻¹)
    (unit : Norm.Basic.normSq (last - first) ≤ 1) :
    Expansion polynomial primitive box inverseBox window side first last source target accuracy sourceSample
      targetSample := by
  let radicand := Quadratic.Polynomial.certificateInBox polynomial box first last firstInside lastInside
  let numerator := Quadratic.Polynomial.certificateInBox primitive.numerator box first last firstInside lastInside
  let slope := slopeCeiling polynomial box
  let floor := side.margin
  have sourceLower : floor ≤ Norm.Basic.normSq sourceSample.reading := by
    have bound := side.margin_le_normSq_sub sourceInside
    rewrite [Gaussian.Basic.sub_zero] at bound
    exact bound
  have targetLower : floor ≤ Norm.Basic.normSq targetSample.reading := by
    have bound := side.margin_le_normSq_sub targetInside
    rewrite [Gaussian.Basic.sub_zero] at bound
    exact bound
  have sumPositive : 0 < 4 * floor :=
    Arithmetic.mul_pos_direct (by decide +kernel) side.margin_pos
  have radicandSlope : Norm.Basic.normSq radicand.slope ≤ slope :=
    Bounds.Box.normSq_eval_le_denseEvalNormBound (GCD.derivative polynomial) firstInside
  let inverse := SquareRoot.Radicand.inverseCertificate radicand sourceSample.reading targetSample.reading
    1 1 slope floor (4 * floor) (by decide +kernel) (by decide +kernel) side.margin_pos
    sourceLower targetLower sumPositive (side.sum_normSq_lower sourceInside targetInside) radicandSlope unit
    (paid_residual sourceSample accuracy_eq) (paid_residual targetSample accuracy_eq)
  have inverseFactor : inverse.factor = inverseCeiling polynomial box floor := by
    change SquareRoot.Radicand.inverseFactor radicand 1 1 slope floor (4 * floor) = _
    unfold SquareRoot.Radicand.inverseFactor SquareRoot.Radicand.remainderFactor
      SquareRoot.Radicand.movementFactor SquareRoot.Radicand.errorFactor
    change 2 * (floor⁻¹ ^ 2 * (2 * (2 * (remainderCeiling polynomial box + 2 * (1 + 1)) +
        (2 * (slope + 2 * (remainderCeiling polynomial box + 2 * (1 + 1))) * (4 * floor)⁻¹) ^ 2) * floor⁻¹) +
      floor⁻¹ ^ 3 * (2 * (slope * floor⁻¹ +
        2 * (2 * (remainderCeiling polynomial box + 2 * (1 + 1)) +
          (2 * (slope + 2 * (remainderCeiling polynomial box + 2 * (1 + 1))) * (4 * floor)⁻¹) ^ 2) *
            floor⁻¹)) ^ 2) = _
    rewrite [show (2 * (1 + 1) : Fraction.Rational) = 4 by decide +kernel]
    rfl
  have inverseSlope : Norm.Basic.normSq inverse.slope ≤ inverseSlopeCeiling polynomial box floor := by
    change Norm.Basic.normSq
      ((SquareRoot.half * radicand.slope * sourceSample.reading⁻¹) *
        (-(sourceSample.reading⁻¹ * sourceSample.reading⁻¹))) ≤ _
    have identity : (SquareRoot.half * radicand.slope * sourceSample.reading⁻¹) *
        (-(sourceSample.reading⁻¹ * sourceSample.reading⁻¹)) =
      -(SquareRoot.half * radicand.slope * sourceSample.reading⁻¹ ^ 3) := by ring1
    rewrite [identity, Norm.Basic.normSq_neg, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    have coefficient := Arithmetic.mul_le_mul_direct half_norm radicandSlope
      (Norm.Basic.normSq_nonneg _) (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
    rewrite [Fraction.Field.one_mul] at coefficient
    exact Arithmetic.mul_le_mul_direct coefficient
      (Norm.Reciprocal.power_normSq_le side.margin_pos sourceLower 3) (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg radicand.slope).trans radicandSlope)
  let outer := Quadratic.Polynomial.certificateInBox (powerPolynomial primitive) inverseBox
    inverse.base inverse.output sourceInverseInside targetInverseInside
  let power := inverse.compose outer (by simpa only [Norm.Basic.normSq_eq_canonical] using unit)
  have outerSlope : Norm.Basic.normSq outer.slope ≤ slopeCeiling (powerPolynomial primitive) inverseBox :=
    Bounds.Box.normSq_eval_le_denseEvalNormBound (GCD.derivative (powerPolynomial primitive)) sourceInverseInside
  have inverseSensitivity := sensitivity_le inverse inverseSlope inverseFactor.le
  have powerFactor : power.factor ≤ powerCeiling polynomial primitive box inverseBox floor := by
    have firstTerm := Arithmetic.mul_le_mul_of_nonneg_right_direct outerSlope inverse.factor_nonneg
    rewrite [inverseFactor] at firstTerm
    have secondTerm := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.pow_le_pow_direct inverse.sensitivity_nonneg inverseSensitivity 2) outer.factor_nonneg
    change 2 * (Canonical.normSq outer.slope * inverse.factor + outer.factor * inverse.sensitivity ^ 2) ≤ _
    rewrite [← Norm.Basic.normSq_eq_canonical, inverseFactor]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct firstTerm secondTerm) (by decide +kernel)
  have powerSlope : Norm.Basic.normSq power.slope ≤ inverseSlopeCeiling polynomial box floor *
      slopeCeiling (powerPolynomial primitive) inverseBox := by
    change Norm.Basic.normSq (inverse.slope * outer.slope) ≤ _
    rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct inverseSlope outerSlope (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg _).trans inverseSlope)
  have powerBase : Norm.Basic.normSq power.base ≤ floor⁻¹ ^ primitive.denominatorExponent := by
    change Norm.Basic.normSq ((powerPolynomial primitive).eval sourceSample.reading⁻¹) ≤ _
    rewrite [powerPolynomial_eval]
    exact Norm.Reciprocal.power_normSq_le side.margin_pos sourceLower primitive.denominatorExponent
  have numeratorBase : Norm.Basic.normSq numerator.base ≤ Bounds.Box.denseEvalNormBound primitive.numerator box :=
    Bounds.Box.normSq_eval_le_denseEvalNormBound primitive.numerator firstInside
  have numeratorSlope : Norm.Basic.normSq numerator.slope ≤ slopeCeiling primitive.numerator box :=
    Bounds.Box.normSq_eval_le_denseEvalNormBound (GCD.derivative primitive.numerator) firstInside
  have numeratorSensitivity := sensitivity_le numerator numeratorSlope (Fraction.Order.Basic.le_refl numerator.factor)
  have powerSensitivity := sensitivity_le power powerSlope powerFactor
  let product := Quadratic.Product.certificate numerator power unit
  let result := product.scale primitive.scale
  have productFactor : product.factor ≤
      4 * (floor⁻¹ ^ primitive.denominatorExponent * remainderCeiling primitive.numerator box +
        Bounds.Box.denseEvalNormBound primitive.numerator box * powerCeiling polynomial primitive box inverseBox floor +
        (2 * (slopeCeiling primitive.numerator box + remainderCeiling primitive.numerator box)) *
          (2 * (inverseSlopeCeiling polynomial box floor * slopeCeiling (powerPolynomial primitive) inverseBox +
            powerCeiling polynomial primitive box inverseBox floor))) := by
    have firstTerm := Arithmetic.mul_le_mul_of_nonneg_right_direct powerBase numerator.factor_nonneg
    have secondTerm := Arithmetic.mul_le_mul_direct numeratorBase powerFactor power.factor_nonneg
      ((Norm.Basic.normSq_nonneg _).trans numeratorBase)
    have crossTerm := Arithmetic.mul_le_mul_direct numeratorSensitivity powerSensitivity
      power.sensitivity_nonneg (numerator.sensitivity_nonneg.trans numeratorSensitivity)
    change 4 * (Canonical.normSq power.base * numerator.factor + Canonical.normSq numerator.base * power.factor +
      numerator.sensitivity * power.sensitivity) ≤ _
    simp only [← Norm.Basic.normSq_eq_canonical]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct
        (Arithmetic.add_le_add_direct firstTerm secondTerm) crossTerm) (by decide +kernel)
  refine
    { accuracy_eq := accuracy_eq
      sourceInside := sourceInside
      targetInside := targetInside
      certificate := result
      base_eq := ?_
      output_eq := ?_
      slope_eq := ?_
      factor_le := ?_ }
  · change primitive.scale * (primitive.numerator.eval first *
        (powerPolynomial primitive).eval sourceSample.reading⁻¹) = _
    rewrite [powerPolynomial_eval]
    exact Gaussian.Basic.mul_assoc _ _ _ |>.symm
  · change primitive.scale * (primitive.numerator.eval last *
        (powerPolynomial primitive).eval targetSample.reading⁻¹) = _
    rewrite [powerPolynomial_eval]
    exact Gaussian.Basic.mul_assoc _ _ _ |>.symm
  · change primitive.scale *
      ((GCD.derivative primitive.numerator).eval first * (powerPolynomial primitive).eval sourceSample.reading⁻¹ +
        primitive.numerator.eval first *
          (((SquareRoot.half * (GCD.derivative polynomial).eval first * sourceSample.reading⁻¹) *
            (-(sourceSample.reading⁻¹ * sourceSample.reading⁻¹))) *
              (GCD.derivative (powerPolynomial primitive)).eval sourceSample.reading⁻¹)) = _
    rewrite [powerPolynomial_eval]
    ring1
  · change Canonical.normSq primitive.scale * product.factor ≤ _
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct productFactor (Norm.Basic.normSq_nonneg _)

namespace Expansion

/-- The original actual primitive readings satisfy the fixed-box fourth-order remainder ceiling. -/
theorem remainder_le {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}
    {box inverseBox window : Box} {side : Box.OutsideSide window 0} {first last : Canonical}
    {source : CertifiedSquareRoot.Certificate (polynomial.eval first)}
    {target : CertifiedSquareRoot.Certificate (polynomial.eval last)} {accuracy : Approximation.AccuracyRequest}
    {sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source accuracy}
    {targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target accuracy}
    (expansion : Expansion polynomial primitive box inverseBox window side first last source target accuracy
      sourceSample targetSample) :
    Canonical.normSq (expansion.certificate.output - expansion.certificate.base -
      (last - first) * expansion.certificate.slope) ≤
        ceiling polynomial primitive box inverseBox side.margin * Canonical.normSq (last - first) ^ 2 := by
  rewrite [expansion.certificate.expansion]
  exact expansion.certificate.remainder_le.trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct expansion.factor_le
      (Arithmetic.pow_nonneg_direct (Canonical.normSq_nonneg _) 2))

end Expansion

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Taylor
