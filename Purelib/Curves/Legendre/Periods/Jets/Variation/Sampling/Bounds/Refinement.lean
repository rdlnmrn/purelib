module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Bounds
import Purelib.Calculus.Jet.Quadratic.SquareRoot.Bounds.Order
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Refinement of the original sampled Taylor ceilings

The original coefficient tables and scalar inverse/cubic formulas are
unchanged. Actual refined physical and inverse boxes and positive floor
comparisons give numerical ceiling comparisons on those same formulas.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

open Purelib.Calculus.Jet
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian

/-- Refining the physical box and raising positive margins decrease the original sampled inverse ceiling. -/
theorem inverseCeiling_mono {firstBox lastBox : Box} (refines : firstBox.Refines lastBox)
    {firstSource lastSource firstTarget lastTarget firstSum lastSum : Rational}
    (sourcePositive : 0 < lastSource) (sourceBound : lastSource ≤ firstSource)
    (targetPositive : 0 < lastTarget) (targetBound : lastTarget ≤ firstTarget)
    (sumPositive : 0 < lastSum) (sumBound : lastSum ≤ firstSum) :
    inverseCeiling firstBox firstSource firstTarget firstSum ≤
      inverseCeiling lastBox lastSource lastTarget lastSum :=
  Quadratic.SquareRoot.inverseCeiling_mono
    (Bounds.Box.denseHornerNormBounds_nonneg Polynomials.basePolynomial firstBox).1
    (Bounds.Box.Monotonicity.denseHornerNormBounds_le_of_refines Polynomials.basePolynomial refines).1
    sourcePositive sourceBound targetPositive targetBound sumPositive sumBound
    (by decide +kernel) (by decide +kernel)

/-- The same physical-box refinement and positive source-floor comparison bound the original inverse slope ceiling. -/
theorem inverseSlopeCeiling_mono {firstBox lastBox : Box} (refines : firstBox.Refines lastBox)
    {firstSource lastSource : Rational} (positive : 0 < lastSource) (lower : lastSource ≤ firstSource) :
    inverseSlopeCeiling firstBox firstSource ≤ inverseSlopeCeiling lastBox lastSource :=
  Order.Arithmetic.mul_le_mul_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Bounds.Box.Monotonicity.denseHornerNormBounds_le_of_refines Polynomials.basePolynomial refines).1
      (Norm.Basic.normSq_nonneg Quadratic.SquareRoot.half))
    (Order.Arithmetic.pow_le_pow_direct (Order.Field.inv_pos_direct (positive.trans_le lower)).le
      (Order.Field.inv_le_inv_of_pos_direct positive lower) 3)
    (Order.Arithmetic.pow_nonneg_direct (Order.Field.inv_pos_direct (positive.trans_le lower)).le 3)
    (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg Quadratic.SquareRoot.half)
      (Bounds.Box.denseHornerNormBounds_nonneg Polynomials.basePolynomial lastBox).1)

/-- Refining both original boxes and increasing positive margins decrease the sampled cubic ceiling.

The same derivative and Taylor-remainder polynomials are folded on the
two retained inverse boxes. Their original monotonicity and inverse/slope
ceiling comparisons pay every factor of the unchanged cubic formula.
-/
theorem cubicCeiling_mono {firstBox lastBox firstInverseBox lastInverseBox : Box}
    (refines : firstBox.Refines lastBox) (inverseRefines : firstInverseBox.Refines lastInverseBox)
    {firstSource lastSource firstTarget lastTarget firstSum lastSum : Rational}
    (sourcePositive : 0 < lastSource) (sourceBound : lastSource ≤ firstSource)
    (targetPositive : 0 < lastTarget) (targetBound : lastTarget ≤ firstTarget)
    (sumPositive : 0 < lastSum) (sumBound : lastSum ≤ firstSum) :
    cubicCeiling firstBox firstInverseBox firstSource firstTarget firstSum ≤
      cubicCeiling lastBox lastInverseBox lastSource lastTarget lastSum := by
  have inverseBound := inverseCeiling_mono refines sourcePositive sourceBound targetPositive targetBound
    sumPositive sumBound
  have firstInverseNonnegative := inverseCeiling_nonnegative firstBox (sourcePositive.trans_le sourceBound)
    (targetPositive.trans_le targetBound) (sumPositive.trans_le sumBound)
  have slopeBound := inverseSlopeCeiling_mono refines sourcePositive sourceBound
  have firstSlopeNonnegative : 0 ≤ inverseSlopeCeiling firstBox firstSource :=
    Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg Quadratic.SquareRoot.half)
        (Bounds.Box.denseHornerNormBounds_nonneg Polynomials.basePolynomial firstBox).1)
      (Order.Arithmetic.pow_nonneg_direct (Order.Field.inv_pos_direct (sourcePositive.trans_le sourceBound)).le 3)
  have sensitivityBound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct slopeBound inverseBound) (by decide +kernel : (0 : Rational) ≤ 2)
  have sensitivityNonnegative := Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2)
    (Order.Arithmetic.add_le_add_direct firstSlopeNonnegative firstInverseNonnegative)
  have derivativeBound := (Bounds.Box.Monotonicity.denseHornerNormBounds_le_of_refines
    (GCD.derivative (Power.Coordinate.coordinatePositivePower 2)) inverseRefines).1
  have remainderBound := Bounds.Box.Monotonicity.denseEvalTaylorRemainderBound_le_of_refines
    (Power.Coordinate.coordinatePositivePower 2) inverseRefines
  unfold cubicCeiling
  exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.mul_le_mul_direct derivativeBound inverseBound firstInverseNonnegative
        (Bounds.Box.denseHornerNormBounds_nonneg
          (GCD.derivative (Power.Coordinate.coordinatePositivePower 2)) lastInverseBox).1)
      (Order.Arithmetic.mul_le_mul_direct remainderBound
        (Order.Arithmetic.pow_le_pow_direct sensitivityNonnegative sensitivityBound 2)
        (Order.Arithmetic.sq_nonneg_direct _)
        (Bounds.Box.Taylor.denseHornerTaylorNormBounds_nonneg
          (Power.Coordinate.coordinatePositivePower 2) lastInverseBox).2.2))
    (by decide +kernel : (0 : Rational) ≤ 2)

/-- The original value-row ceiling decreases under physical-box refinement and larger positive observation floors. -/
theorem valueCeiling_mono (parameter : Canonical) (coordinate : Fin 2)
    {firstBox lastBox : Box} (refines : firstBox.Refines lastBox)
    {firstSource lastSource firstTarget lastTarget firstSum lastSum : Rational}
    (sourcePositive : 0 < lastSource) (sourceBound : lastSource ≤ firstSource)
    (targetPositive : 0 < lastTarget) (targetBound : lastTarget ≤ firstTarget)
    (sumPositive : 0 < lastSum) (sumBound : lastSum ≤ firstSum) :
    valueCeiling coordinate firstBox firstSource firstTarget firstSum ≤
      valueCeiling coordinate lastBox lastSource lastTarget lastSum :=
  Order.Arithmetic.mul_le_mul_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Bounds.Box.Monotonicity.denseHornerNormBounds_le_of_refines
        (Specification.valueSpecification parameter coordinate).numerator refines).1
      (Norm.Basic.normSq_nonneg (Specification.valueSpecification parameter coordinate).scale))
    (inverseCeiling_mono refines sourcePositive sourceBound targetPositive targetBound sumPositive sumBound)
    (inverseCeiling_nonnegative firstBox (sourcePositive.trans_le sourceBound)
      (targetPositive.trans_le targetBound) (sumPositive.trans_le sumBound))
    (Order.Arithmetic.mul_nonneg_direct
      (Norm.Basic.normSq_nonneg (Specification.valueSpecification parameter coordinate).scale)
      (Bounds.Box.denseHornerNormBounds_nonneg (Specification.valueSpecification parameter coordinate).numerator
        lastBox).1)

/-- The original first-row ceiling decreases under both box refinements and larger positive observation floors. -/
theorem firstCeiling_mono (parameter : Canonical) (coordinate : Fin 2)
    {firstBox lastBox firstInverseBox lastInverseBox : Box}
    (refines : firstBox.Refines lastBox) (inverseRefines : firstInverseBox.Refines lastInverseBox)
    {firstSource lastSource firstTarget lastTarget firstSum lastSum : Rational}
    (sourcePositive : 0 < lastSource) (sourceBound : lastSource ≤ firstSource)
    (targetPositive : 0 < lastTarget) (targetBound : lastTarget ≤ firstTarget)
    (sumPositive : 0 < lastSum) (sumBound : lastSum ≤ firstSum) :
    firstCeiling coordinate firstBox firstInverseBox firstSource firstTarget firstSum ≤
      firstCeiling coordinate lastBox lastInverseBox lastSource lastTarget lastSum :=
  Order.Arithmetic.mul_le_mul_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Bounds.Box.Monotonicity.denseHornerNormBounds_le_of_refines
        (Specification.firstDerivativeSpecification parameter coordinate).numerator refines).1
      (Norm.Basic.normSq_nonneg (Specification.firstDerivativeSpecification parameter coordinate).scale))
    (cubicCeiling_mono refines inverseRefines sourcePositive sourceBound
      targetPositive targetBound sumPositive sumBound)
    (cubicCeiling_nonnegative firstBox firstInverseBox (sourcePositive.trans_le sourceBound)
      (targetPositive.trans_le targetBound) (sumPositive.trans_le sumBound))
    (Order.Arithmetic.mul_nonneg_direct
      (Norm.Basic.normSq_nonneg (Specification.firstDerivativeSpecification parameter coordinate).scale)
      (Bounds.Box.denseHornerNormBounds_nonneg (Specification.firstDerivativeSpecification parameter
        coordinate).numerator lastBox).1)

end Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

end
