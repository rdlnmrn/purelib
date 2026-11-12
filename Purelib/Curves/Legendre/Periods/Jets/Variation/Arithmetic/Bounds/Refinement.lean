module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Bounds
import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Bounds.Refinement
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache.Bounds.Refinement
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Curves.Legendre.Periods.Jets.Specification

/-! # Refinement of original jointly paid arithmetic row ceilings

The scalar inverse/cubic ceiling and all three independent arithmetic
allowance ceilings retain their original differential owners and formulas.
The same box and positive-floor comparisons bound their numerical sum.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)

/-- Refining the physical box and raising all positive margins decrease the original paid value-row ceiling. -/
theorem valueCeiling_mono (parameter increment : Canonical) (coordinate : Fin 2)
    {firstBox lastBox : Box} (refines : firstBox.Refines lastBox)
    {firstSource lastSource firstTarget lastTarget firstSum lastSum : Rational}
    (sourcePositive : 0 < lastSource) (sourceBound : lastSource ≤ firstSource)
    (targetPositive : 0 < lastTarget) (targetBound : lastTarget ≤ firstTarget)
    (sumPositive : 0 < lastSum) (sumBound : lastSum ≤ firstSum) :
    valueCeiling parameter increment coordinate firstBox firstSource firstTarget firstSum ≤
      valueCeiling parameter increment coordinate lastBox lastSource lastTarget lastSum :=
  Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.add_le_add_direct
          (Sampling.valueCeiling_mono parameter coordinate refines sourcePositive sourceBound
            targetPositive targetBound sumPositive sumBound)
          (Cache.allowanceCeiling_mono (Specification.valueSpecification parameter coordinate)
            refines sourcePositive sourceBound))
        (Cache.allowanceCeiling_mono (Specification.valueSpecification (parameter + increment) coordinate)
          refines targetPositive targetBound))
      (Cache.allowanceCeiling_mono (Specification.firstDerivativeSpecification parameter coordinate)
        refines sourcePositive sourceBound))
    (by decide +kernel : (0 : Rational) ≤ 4)

/-- Refining both boxes and raising positive margins decrease the same paid first-row ceiling. -/
theorem firstCeiling_mono (parameter increment : Canonical) (coordinate : Fin 2)
    {firstBox lastBox firstInverseBox lastInverseBox : Box}
    (refines : firstBox.Refines lastBox) (inverseRefines : firstInverseBox.Refines lastInverseBox)
    {firstSource lastSource firstTarget lastTarget firstSum lastSum : Rational}
    (sourcePositive : 0 < lastSource) (sourceBound : lastSource ≤ firstSource)
    (targetPositive : 0 < lastTarget) (targetBound : lastTarget ≤ firstTarget)
    (sumPositive : 0 < lastSum) (sumBound : lastSum ≤ firstSum) :
    firstCeiling parameter increment coordinate firstBox firstInverseBox firstSource firstTarget firstSum ≤
      firstCeiling parameter increment coordinate lastBox lastInverseBox lastSource lastTarget lastSum :=
  Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.add_le_add_direct
          (Sampling.firstCeiling_mono parameter coordinate refines inverseRefines sourcePositive sourceBound
            targetPositive targetBound sumPositive sumBound)
          (Cache.allowanceCeiling_mono (Specification.firstDerivativeSpecification parameter coordinate)
            refines sourcePositive sourceBound))
        (Cache.allowanceCeiling_mono (Specification.firstDerivativeSpecification (parameter + increment) coordinate)
          refines targetPositive targetBound))
      (Cache.allowanceCeiling_mono (Specification.secondDerivativeSpecification parameter coordinate)
        refines sourcePositive sourceBound))
    (by decide +kernel : (0 : Rational) ≤ 4)

end Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic

end
