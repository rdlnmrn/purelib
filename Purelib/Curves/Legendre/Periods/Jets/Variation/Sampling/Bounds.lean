module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
public import Purelib.Calculus.Jet.Quadratic.SquareRoot.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Calculus.Jet.Quadratic.Polynomial.Bounds
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Tactic.Ring

/-! # Fixed-box bounds on the original sampled inverse and cubic caches

The actual two paid root observations retain positive source, target and sum
margins. One fixed spatial box bounds the original Legendre affine coefficient;
one fixed inverse box bounds the original cached cubic polynomial certificate.
The resulting row ceilings depend on those boxes and margins, independently
of the parameter-increment size or spatial quadrature mesh.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation

/-- The original spatial box fold bounds the affine Legendre radicand coefficient. -/
@[expose] def coefficientCeiling (spatialBox : Box) : Fraction.Rational :=
  Bounds.Box.denseEvalNormBound Polynomials.basePolynomial spatialBox

/-- The original source, target and sum margins bound the retained inverse-cache factor. -/
@[expose] def inverseCeiling (spatialBox : Box) (sourceFloor targetFloor sumFloor : Fraction.Rational) :
    Fraction.Rational :=
  Quadratic.SquareRoot.inverseCeiling (coefficientCeiling spatialBox) sourceFloor targetFloor sumFloor 1 1

/-- The original half coefficient and source margin bound the retained inverse-cache slope quadrance. -/
@[expose] def inverseSlopeCeiling (spatialBox : Box) (sourceFloor : Fraction.Rational) : Fraction.Rational :=
  Norm.Basic.normSq Quadratic.SquareRoot.half * coefficientCeiling spatialBox * sourceFloor⁻¹ ^ 3

/-- The original fixed-box power fold and inverse-cache bounds give the retained cubic-cache factor ceiling. -/
@[expose] def cubicCeiling (spatialBox inverseBox : Box) (sourceFloor targetFloor sumFloor : Fraction.Rational) :
    Fraction.Rational :=
  let inverse := inverseCeiling spatialBox sourceFloor targetFloor sumFloor
  let power := Power.Coordinate.coordinatePositivePower 2
  2 * (Bounds.Box.denseEvalNormBound (GCD.derivative power) inverseBox * inverse +
    Bounds.Box.Taylor.denseEvalTaylorRemainderBound power inverseBox *
      (2 * (inverseSlopeCeiling spatialBox sourceFloor + inverse)) ^ 2)

/-- The original value-row scale and numerator box fold bound its retained scaled inverse-cache factor. -/
@[expose] def valueCeiling (coordinate : Fin 2) (spatialBox : Box)
    (sourceFloor targetFloor sumFloor : Fraction.Rational) : Fraction.Rational :=
  Norm.Basic.normSq (1 : Canonical) *
    Bounds.Box.denseEvalNormBound (Specification.valueNumerator coordinate) spatialBox *
      inverseCeiling spatialBox sourceFloor targetFloor sumFloor

/-- The original first-row scale and numerator box fold bound its retained scaled cubic-cache factor. -/
@[expose] def firstCeiling (coordinate : Fin 2) (spatialBox inverseBox : Box)
    (sourceFloor targetFloor sumFloor : Fraction.Rational) : Fraction.Rational :=
  Norm.Basic.normSq (Cast.LegendrePeriodJets.realGaussian (1 / 2)) *
    Bounds.Box.denseEvalNormBound (Specification.firstDerivativeNumerator coordinate) spatialBox *
      cubicCeiling spatialBox inverseBox sourceFloor targetFloor sumFloor

/-- Three positive actual margins give a nonnegative fixed-box inverse-cache factor ceiling. -/
theorem inverseCeiling_nonnegative (spatialBox : Box) {sourceFloor targetFloor sumFloor : Fraction.Rational}
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor) :
    0 ≤ inverseCeiling spatialBox sourceFloor targetFloor sumFloor :=
  Quadratic.SquareRoot.inverseCeiling_nonnegative
    (Bounds.Box.denseHornerNormBounds_nonneg Polynomials.basePolynomial spatialBox).1
    sourcePositive targetPositive sumPositive (by decide +kernel) (by decide +kernel)

/-- Three positive actual margins give a nonnegative fixed-box cubic-cache factor ceiling. -/
theorem cubicCeiling_nonnegative (spatialBox inverseBox : Box) {sourceFloor targetFloor sumFloor : Fraction.Rational}
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor) :
    0 ≤ cubicCeiling spatialBox inverseBox sourceFloor targetFloor sumFloor :=
  Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_nonneg_direct
        (Bounds.Box.denseHornerNormBounds_nonneg (GCD.derivative (Power.Coordinate.coordinatePositivePower 2))
          inverseBox).1
        (inverseCeiling_nonnegative spatialBox sourcePositive targetPositive sumPositive))
      (Arithmetic.mul_nonneg_direct
        (Bounds.Box.Taylor.denseHornerTaylorNormBounds_nonneg (Power.Coordinate.coordinatePositivePower 2)
          inverseBox).2.2
        (Arithmetic.sq_nonneg_direct _)))

/-- The original scale, numerator box fold and positive margins give a nonnegative scalar value-row ceiling. -/
theorem valueCeiling_nonnegative (coordinate : Fin 2) (spatialBox : Box)
    {sourceFloor targetFloor sumFloor : Fraction.Rational}
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor) :
    0 ≤ valueCeiling coordinate spatialBox sourceFloor targetFloor sumFloor :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Norm.Basic.normSq_nonneg (1 : Canonical))
      (Bounds.Box.denseHornerNormBounds_nonneg (Specification.valueNumerator coordinate) spatialBox).1)
    (inverseCeiling_nonnegative spatialBox sourcePositive targetPositive sumPositive)

/-- The original first-row scale, numerator fold and positive margins give a nonnegative scalar first-row ceiling. -/
theorem firstCeiling_nonnegative (coordinate : Fin 2) (spatialBox inverseBox : Box)
    {sourceFloor targetFloor sumFloor : Fraction.Rational}
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor) :
    0 ≤ firstCeiling coordinate spatialBox inverseBox sourceFloor targetFloor sumFloor :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Norm.Basic.normSq_nonneg (Cast.LegendrePeriodJets.realGaussian (1 / 2)))
      (Bounds.Box.denseHornerNormBounds_nonneg
        (Specification.firstDerivativeNumerator coordinate) spatialBox).1)
    (cubicCeiling_nonnegative spatialBox inverseBox sourcePositive targetPositive sumPositive)

/-- The complete original row coefficient obeys its retained scale and numerator box-fold bound. -/
private theorem row_coefficient_le {radicand : CoefficientPolynomial}
    (differential : OddPowerDifferential radicand) {spatialBox : Box} {point : Canonical}
    (inside : spatialBox.Contains point) :
    Norm.Basic.normSq (differential.scale * differential.numerator.eval point) ≤
      Norm.Basic.normSq differential.scale * Bounds.Box.denseEvalNormBound differential.numerator spatialBox := by
  rewrite [Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Bounds.Box.normSq_eval_le_denseEvalNormBound differential.numerator inside)
    (Norm.Basic.normSq_nonneg differential.scale)

namespace SampledJet

variable {parameter increment point : Canonical}
  {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
  {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
  {unit : Norm.Basic.normSq increment ≤ 1}

/-- The original inverse-cache factor obeys the fixed spatial box and three actual observation margins. -/
theorem inverse_factor_le (jet : SampledJet parameter increment point source target unit)
    {spatialBox : Box} (inside : spatialBox.Contains point) :
    jet.inverse.factor ≤ inverseCeiling spatialBox jet.clearance.sourceFloor jet.clearance.targetFloor
      jet.clearance.sumFloor := by
  have coefficientBound : Norm.Basic.normSq (Polynomials.baseValue point) ≤ coefficientCeiling spatialBox := by
    unfold Polynomials.baseValue
    rewrite [← Polynomials.basePolynomial_eval]
    exact Bounds.Box.normSq_eval_le_denseEvalNormBound Polynomials.basePolynomial inside
  rewrite [jet.inverse_eq]
  apply Quadratic.SquareRoot.inverseCertificate_factor_le
  · exact coefficientBound
  · exact jet.clearance.sourcePositive
  · exact jet.clearance.source_normSq_lower
  · exact jet.clearance.targetPositive
  · exact jet.clearance.target_normSq_lower
  · exact jet.clearance.sumPositive
  · exact jet.sum_lower

/-- The exact retained inverse-cache base is the reciprocal of the same actual source observation. -/
private theorem inverse_base (jet : SampledJet parameter increment point source target unit) :
    jet.inverse.base = jet.sourceSample.reading⁻¹ := by
  rewrite [jet.inverse_eq, Quadratic.SquareRoot.inverseCertificate_base]
  rfl

/-- The exact retained inverse-cache output is the reciprocal of the same actual target observation. -/
private theorem inverse_output (jet : SampledJet parameter increment point source target unit) :
    jet.inverse.output = jet.targetSample.reading⁻¹ := by
  rewrite [jet.inverse_eq, Quadratic.SquareRoot.inverseCertificate_output]
  rfl

/-- The retained inverse slope pays the original affine coefficient and actual source margin. -/
theorem inverse_slope_le (jet : SampledJet parameter increment point source target unit)
    {spatialBox : Box} (inside : spatialBox.Contains point) :
    Norm.Basic.normSq jet.inverse.slope ≤ inverseSlopeCeiling spatialBox jet.clearance.sourceFloor := by
  have coefficientBound : Norm.Basic.normSq (Polynomials.baseValue point) ≤ coefficientCeiling spatialBox := by
    unfold Polynomials.baseValue
    rewrite [← Polynomials.basePolynomial_eval]
    exact Bounds.Box.normSq_eval_le_denseEvalNormBound Polynomials.basePolynomial inside
  have numerator := Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientBound
    (Norm.Basic.normSq_nonneg Quadratic.SquareRoot.half)
  rewrite [jet.inverse_eq, Quadratic.SquareRoot.inverseCertificate_slope,
    Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_direct numerator
    (Norm.Reciprocal.power_normSq_le jet.clearance.sourcePositive jet.clearance.source_normSq_lower 3)
    (Norm.Basic.normSq_nonneg _)
    ((Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg Quadratic.SquareRoot.half)
      (Norm.Basic.normSq_nonneg (Polynomials.baseValue point))).trans numerator)

/-- The exact original cubic cache obeys the fixed boxes and same original source, target and sum margins. -/
theorem cubic_factor_le (jet : SampledJet parameter increment point source target unit)
    {spatialBox inverseBox : Box} (inside : spatialBox.Contains point)
    (sourceInverseInside : inverseBox.Contains jet.sourceSample.reading⁻¹)
    (targetInverseInside : inverseBox.Contains jet.targetSample.reading⁻¹) :
    jet.cubic.factor ≤ cubicCeiling spatialBox inverseBox jet.clearance.sourceFloor jet.clearance.targetFloor
      jet.clearance.sumFloor := by
  let power := Power.Coordinate.coordinatePositivePower 2
  let outer := Quadratic.Polynomial.certificate power jet.inverse.base jet.inverse.output
  have baseInside : inverseBox.Contains jet.inverse.base := by rewrite [jet.inverse_base]; exact sourceInverseInside
  have outputInside : inverseBox.Contains jet.inverse.output := by
    rewrite [jet.inverse_output]
    exact targetInverseInside
  have factorBound := jet.inverse_factor_le inside
  have slopeBound := jet.inverse_slope_le inside
  have sensitivityBound : jet.inverse.sensitivity ≤
      2 * (inverseSlopeCeiling spatialBox jet.clearance.sourceFloor +
        inverseCeiling spatialBox jet.clearance.sourceFloor jet.clearance.targetFloor jet.clearance.sumFloor) := by
    unfold Quadratic.Basic.Certificate.sensitivity
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct slopeBound factorBound)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  have outerSlope : Norm.Basic.normSq outer.slope ≤
      Bounds.Box.denseEvalNormBound (GCD.derivative power) inverseBox := by
    rewrite [Quadratic.Polynomial.certificate_slope]
    exact Bounds.Box.normSq_eval_le_denseEvalNormBound (GCD.derivative power) baseInside
  have outerFactor := Quadratic.Polynomial.certificate_factor_le_box power baseInside outputInside
  have firstTerm := Arithmetic.mul_le_mul_direct outerSlope factorBound jet.inverse.factor_nonneg
    ((Norm.Basic.normSq_nonneg outer.slope).trans outerSlope)
  have sensitivitySquare := Arithmetic.pow_le_pow_direct
    jet.inverse.sensitivity_nonneg sensitivityBound 2
  have lastTerm := Arithmetic.mul_le_mul_direct outerFactor sensitivitySquare
    (Arithmetic.pow_nonneg_direct jet.inverse.sensitivity_nonneg 2)
    (outer.factor_nonneg.trans outerFactor)
  rewrite [jet.cubic_eq]
  change 2 * (Canonical.normSq outer.slope * jet.inverse.factor + outer.factor * jet.inverse.sensitivity ^ 2) ≤ _
  rewrite [← Norm.Basic.normSq_eq_canonical]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct firstTerm lastTerm)
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)

/-- The original value-row factor retains its exact inverse cache and obeys the fixed spatial-box ceiling. -/
theorem value_factor_le (jet : SampledJet parameter increment point source target unit) (coordinate : Fin 2)
    {spatialBox : Box} (inside : spatialBox.Contains point) :
    (jet.value coordinate).factor ≤ valueCeiling coordinate spatialBox jet.clearance.sourceFloor
      jet.clearance.targetFloor
      jet.clearance.sumFloor := by
  have coefficientBound := row_coefficient_le (Specification.valueSpecification parameter coordinate) inside
  have inverseBound := jet.inverse_factor_le inside
  rewrite [jet.value_eq coordinate]
  change Canonical.normSq ((Specification.valueSpecification parameter coordinate).scale *
    (Specification.valueSpecification parameter coordinate).numerator.eval point) * jet.inverse.factor ≤ _
  rewrite [← Norm.Basic.normSq_eq_canonical]
  exact Arithmetic.mul_le_mul_direct coefficientBound inverseBound jet.inverse.factor_nonneg
    ((Norm.Basic.normSq_nonneg _).trans coefficientBound)

/-- The original first-row factor retains its exact cubic cache and obeys both fixed-box ceilings. -/
theorem first_factor_le (jet : SampledJet parameter increment point source target unit) (coordinate : Fin 2)
    {spatialBox inverseBox : Box} (inside : spatialBox.Contains point)
    (sourceInverseInside : inverseBox.Contains jet.sourceSample.reading⁻¹)
    (targetInverseInside : inverseBox.Contains jet.targetSample.reading⁻¹) :
    (jet.first coordinate).factor ≤ firstCeiling coordinate spatialBox inverseBox jet.clearance.sourceFloor
      jet.clearance.targetFloor jet.clearance.sumFloor := by
  have coefficientBound := row_coefficient_le (Specification.firstDerivativeSpecification parameter coordinate) inside
  have cubicBound := jet.cubic_factor_le inside sourceInverseInside targetInverseInside
  rewrite [jet.first_eq coordinate]
  change Canonical.normSq ((Specification.firstDerivativeSpecification parameter coordinate).scale *
    (Specification.firstDerivativeSpecification parameter coordinate).numerator.eval point) * jet.cubic.factor ≤ _
  rewrite [← Norm.Basic.normSq_eq_canonical]
  exact Arithmetic.mul_le_mul_direct coefficientBound cubicBound jet.cubic.factor_nonneg
    ((Norm.Basic.normSq_nonneg _).trans coefficientBound)

end SampledJet

end Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
