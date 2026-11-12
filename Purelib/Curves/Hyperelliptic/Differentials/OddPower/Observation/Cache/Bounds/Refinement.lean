module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache.Bounds
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity
import Purelib.Data.Gaussian.Norm.Power.Order
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Refinement of original arithmetic sensitivity ceilings

The same differential numerator and exponent are retained. Refining its
physical box and raising its positive candidate floor decreases the original
sensitivity and allowance ceilings, without reobserving its root process.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)

/-- A refined numerator box and larger positive floor decrease the original arithmetic sensitivity ceiling.

Both computations retain the same differential, its scale and denominator
exponent. The original Horner refinement and finite power-difference law
compare every factor using reciprocal antitonicity on the positive floors.
-/
theorem sensitivityCeiling_mono {radicand : Coefficients} (differential : OddPowerDifferential radicand)
    {firstBox lastBox : Box} (refines : firstBox.Refines lastBox)
    {firstFloor lastFloor : Rational} (positive : 0 < lastFloor) (lower : lastFloor ≤ firstFloor) :
    sensitivityCeiling differential firstBox firstFloor ≤ sensitivityCeiling differential lastBox lastFloor := by
  have firstPositive := positive.trans_le lower
  have inverse := Order.Field.inv_le_inv_of_pos_direct positive lower
  have firstInverseNonnegative := (Order.Field.inv_pos_direct firstPositive).le
  have lastInverseNonnegative := (Order.Field.inv_pos_direct positive).le
  have numerator := (Bounds.Box.Monotonicity.denseHornerNormBounds_le_of_refines differential.numerator refines).1
  have lastNumeratorNonnegative := (Bounds.Box.denseHornerNormBounds_nonneg differential.numerator lastBox).1
  have coefficient := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct numerator
    (Norm.Basic.normSq_nonneg differential.scale)
  have lastCoefficientNonnegative := Order.Arithmetic.mul_nonneg_direct
    (Norm.Basic.normSq_nonneg differential.scale) lastNumeratorNonnegative
  have power := Norm.Power.differenceFactor_mono firstInverseNonnegative inverse differential.denominatorExponent
  have lastPowerNonnegative := Norm.Power.differenceFactor_nonnegative lastInverseNonnegative
    differential.denominatorExponent
  unfold sensitivityCeiling
  exact Order.Arithmetic.mul_le_mul_direct
    (Order.Arithmetic.mul_le_mul_direct coefficient power
      (Norm.Power.differenceFactor_nonnegative firstInverseNonnegative differential.denominatorExponent)
      lastCoefficientNonnegative)
    (Order.Arithmetic.mul_le_mul_direct inverse inverse firstInverseNonnegative lastInverseNonnegative)
    (Order.Arithmetic.mul_nonneg_direct firstInverseNonnegative firstInverseNonnegative)
    (Order.Arithmetic.mul_nonneg_direct lastCoefficientNonnegative lastPowerNonnegative)

/-- The same refined box and larger positive candidate floor decrease its original paid allowance ceiling. -/
theorem allowanceCeiling_mono {radicand : Coefficients} (differential : OddPowerDifferential radicand)
    {firstBox lastBox : Box} (refines : firstBox.Refines lastBox)
    {firstFloor lastFloor : Rational} (positive : 0 < lastFloor) (lower : lastFloor ≤ firstFloor) :
    allowanceCeiling differential firstBox firstFloor ≤ allowanceCeiling differential lastBox lastFloor :=
  Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _)
    (Order.Field.divide_mono (sensitivityCeiling_mono differential refines positive lower)
      (by decide +kernel : (0 : Rational) < 8))

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache

end
