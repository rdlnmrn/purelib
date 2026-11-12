module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Bounds
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Uniform factors on actual original arithmetic parameter-variation rows

The original scalar inverse and cubic caches retain their fixed-box bounds.
Actual arithmetic observations retain source and target candidate margins,
which pay their fixed numerator-box sensitivities. Their exact perturbation
factors therefore have ceilings independent of the spatial mesh and parameter
step, while every original evaluator cache and selected witness is retained.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic

open Purelib.Data.Rat.Fraction

open Purelib
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation

/-- The original scalar value ceiling and three actual arithmetic allowance ceilings pay the exact value-row factor. -/
@[expose] def valueCeiling (parameter increment : Canonical) (coordinate : Fin 2) (spatialBox : Box)
    (sourceFloor targetFloor sumFloor : Fraction.Rational) : Fraction.Rational :=
  4 * (Sampling.valueCeiling coordinate spatialBox sourceFloor targetFloor sumFloor +
    Cache.allowanceCeiling (Specification.valueSpecification parameter coordinate) spatialBox sourceFloor +
    Cache.allowanceCeiling (Specification.valueSpecification (parameter + increment) coordinate)
      spatialBox targetFloor +
    Cache.allowanceCeiling (Specification.firstDerivativeSpecification parameter coordinate) spatialBox sourceFloor)

/-- The original scalar first ceiling and actual first/second arithmetic allowances pay the exact first-row factor. -/
@[expose] def firstCeiling (parameter increment : Canonical) (coordinate : Fin 2) (spatialBox inverseBox : Box)
    (sourceFloor targetFloor sumFloor : Fraction.Rational) : Fraction.Rational :=
  4 * (Sampling.firstCeiling coordinate spatialBox inverseBox sourceFloor targetFloor sumFloor +
    Cache.allowanceCeiling (Specification.firstDerivativeSpecification parameter coordinate) spatialBox sourceFloor +
    Cache.allowanceCeiling (Specification.firstDerivativeSpecification (parameter + increment) coordinate)
      spatialBox targetFloor +
    Cache.allowanceCeiling (Specification.secondDerivativeSpecification parameter coordinate) spatialBox sourceFloor)

/-- The original indexed forms give the same numerical valueCeiling at any parameter indices.

The two actual differential owners remain distinct. Only their retained
numerator, exponent and scalar readouts agree, so the original finite box
and observation margins give one parameter-independent numerical bound.
-/
theorem valueCeiling_parameters (firstParameter firstIncrement lastParameter lastIncrement : Canonical)
    (coordinate : Fin 2) (spatialBox : Box) (sourceFloor targetFloor sumFloor : Fraction.Rational) :
    valueCeiling firstParameter firstIncrement coordinate spatialBox sourceFloor targetFloor sumFloor =
      valueCeiling lastParameter lastIncrement coordinate spatialBox sourceFloor targetFloor sumFloor := (rfl)

/-- The original indexed forms give the same numerical firstCeiling at any parameter indices.

The two actual differential owners remain distinct. Only their retained
numerator, exponent and scalar readouts agree, so the original finite box
and observation margins give one parameter-independent numerical bound.
-/
theorem firstCeiling_parameters (firstParameter firstIncrement lastParameter lastIncrement : Canonical)
    (coordinate : Fin 2) (spatialBox inverseBox : Box) (sourceFloor targetFloor sumFloor : Fraction.Rational) :
    firstCeiling firstParameter firstIncrement coordinate spatialBox inverseBox sourceFloor targetFloor sumFloor =
      firstCeiling lastParameter lastIncrement coordinate spatialBox inverseBox sourceFloor targetFloor sumFloor :=
  (rfl)

/-- The same three positive actual margins give a nonnegative ceiling for both original arithmetic value rows. -/
theorem valueCeiling_nonnegative (parameter increment : Canonical) (coordinate : Fin 2) (spatialBox : Box)
    {sourceFloor targetFloor sumFloor : Fraction.Rational}
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor) :
    0 ≤ valueCeiling parameter increment coordinate spatialBox sourceFloor targetFloor sumFloor :=
  Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.add_le_add_direct
          (Sampling.valueCeiling_nonnegative coordinate spatialBox sourcePositive targetPositive sumPositive)
          (Cache.allowanceCeiling_nonnegative (Specification.valueSpecification parameter coordinate)
            spatialBox sourcePositive))
        (Cache.allowanceCeiling_nonnegative (Specification.valueSpecification (parameter + increment) coordinate)
          spatialBox targetPositive))
      (Cache.allowanceCeiling_nonnegative (Specification.firstDerivativeSpecification parameter coordinate) spatialBox
        sourcePositive))

/-- The same positive margins give a nonnegative ceiling for both arithmetic first rows and their second slopes. -/
theorem firstCeiling_nonnegative (parameter increment : Canonical) (coordinate : Fin 2) (spatialBox inverseBox : Box)
    {sourceFloor targetFloor sumFloor : Fraction.Rational}
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor) :
    0 ≤ firstCeiling parameter increment coordinate spatialBox inverseBox sourceFloor targetFloor sumFloor :=
  Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.add_le_add_direct
          (Sampling.firstCeiling_nonnegative coordinate spatialBox inverseBox sourcePositive targetPositive sumPositive)
          (Cache.allowanceCeiling_nonnegative (Specification.firstDerivativeSpecification parameter coordinate)
            spatialBox sourcePositive))
        (Cache.allowanceCeiling_nonnegative
          (Specification.firstDerivativeSpecification (parameter + increment) coordinate)
          spatialBox targetPositive))
      (Cache.allowanceCeiling_nonnegative (Specification.secondDerivativeSpecification parameter coordinate) spatialBox
        sourcePositive))

namespace Observations

variable {parameter increment point : Canonical}
  {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
  {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
  {unit : Norm.Basic.normSq increment ≤ 1}
  {jet : Sampling.SampledJet parameter increment point source target unit}

/-- The actual value-row factor is exactly the scalar factor plus its three separate arithmetic payments. -/
private theorem value_factor (observations : Observations jet) (coordinate : Fin 2) :
    (observations.valueCertificate coordinate).factor = 4 * ((jet.value coordinate).factor +
      Cache.allowanceFactor (Specification.valueSpecification parameter coordinate)
        point source jet.clearance.sourceFloor +
      Cache.allowanceFactor (Specification.valueSpecification (parameter + increment) coordinate)
        point target jet.clearance.targetFloor +
      Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor) := by
  unfold valueCertificate
  rewrite [Quadratic.Basic.Certificate.perturb_factor]
  rfl

/-- The actual first-row factor keeps the original scalar factor and independent first/second arithmetic payments. -/
private theorem first_factor (observations : Observations jet) (coordinate : Fin 2) :
    (observations.firstCertificate coordinate).factor = 4 * ((jet.first coordinate).factor +
      Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor +
      Cache.allowanceFactor (Specification.firstDerivativeSpecification (parameter + increment) coordinate) point target
        jet.clearance.targetFloor +
      Cache.allowanceFactor (Specification.secondDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor) := by
  unfold firstCertificate
  rewrite [Quadratic.Basic.Certificate.perturb_factor]
  rfl

/-- Both actual value rows have a fixed-box factor bound on the same retained source and target observations. -/
theorem value_factor_le (observations : Observations jet) (coordinate : Fin 2)
    {spatialBox : Box} (inside : spatialBox.Contains point) :
    (observations.valueCertificate coordinate).factor ≤ valueCeiling parameter increment coordinate spatialBox
      jet.clearance.sourceFloor jet.clearance.targetFloor jet.clearance.sumFloor := by
  rewrite [observations.value_factor coordinate]
  exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.add_le_add_direct (jet.value_factor_le coordinate inside)
          (Cache.allowanceFactor_le_ceiling (Specification.valueSpecification parameter coordinate) source inside
            jet.clearance.sourcePositive))
        (Cache.allowanceFactor_le_ceiling (Specification.valueSpecification (parameter + increment) coordinate)
          target inside
          jet.clearance.targetPositive))
      (Cache.allowanceFactor_le_ceiling (Specification.firstDerivativeSpecification parameter coordinate) source inside
        jet.clearance.sourcePositive)) (by decide +kernel : (0 : Fraction.Rational) ≤ 4)

/-- Both actual first rows retain their independently observed second slopes and have the fixed-box factor bound. -/
theorem first_factor_le (observations : Observations jet) (coordinate : Fin 2)
    {spatialBox inverseBox : Box} (inside : spatialBox.Contains point)
    (sourceInverseInside : inverseBox.Contains jet.sourceSample.reading⁻¹)
    (targetInverseInside : inverseBox.Contains jet.targetSample.reading⁻¹) :
    (observations.firstCertificate coordinate).factor ≤ firstCeiling parameter increment coordinate
      spatialBox inverseBox
      jet.clearance.sourceFloor jet.clearance.targetFloor jet.clearance.sumFloor := by
  rewrite [observations.first_factor coordinate]
  exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.add_le_add_direct
          (jet.first_factor_le coordinate inside sourceInverseInside targetInverseInside)
          (Cache.allowanceFactor_le_ceiling (Specification.firstDerivativeSpecification parameter coordinate)
            source inside
            jet.clearance.sourcePositive))
        (Cache.allowanceFactor_le_ceiling
          (Specification.firstDerivativeSpecification (parameter + increment) coordinate)
          target inside
          jet.clearance.targetPositive))
      (Cache.allowanceFactor_le_ceiling (Specification.secondDerivativeSpecification parameter coordinate) source inside
        jet.clearance.sourcePositive)) (by decide +kernel : (0 : Fraction.Rational) ≤ 4)

end Observations

end Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic
