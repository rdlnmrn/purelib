module

public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
public import Purelib.Polynomial.Dense.Power
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Power.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Tactic.Ring

/-! # Full-numerator power gaps on the same original inverse-model overlap

One original numerator/clearance cache bounds both actual model values at
their common point. The retained unflipped sign and original power-slope
law give separate inverse, cube and fifth gaps without changing a model,
root, power table or polynomial stage.
-/

public section

namespace Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Gaussian.Power.Bounds
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model Polynomial Box)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Approximation.Rational

variable {polynomial numerator : Polynomial} {leftBox rightBox : Box}
  {clearance : RegionClearance polynomial leftBox}

/-- The fixed full-numerator power-gap scale from the SAME retained clearance bounds. -/
def powerScale (bounds : PrimitiveOverlapBounds clearance numerator) (exponent : Nat) : Rational :=
  6 * (bounds.numeratorUpper * bounds.inverseUpper) *
    IntegrationQuotientVariation.powerSlope bounds.inverseUpper exponent

/-- The actual power-gap scale is nonnegative for every finite exponent. -/
theorem powerScale_nonnegative (bounds : PrimitiveOverlapBounds clearance numerator) (exponent : Nat) :
    0 ≤ bounds.powerScale exponent :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
    (IntegrationQuotientVariation.powerSlope_nonnegative bounds.inverseUpper_positive.le exponent)

/-- An actual unflipped overlap bounds full-numerator polynomial powers using both original residual budgets. -/
theorem coefficient_power_gap_le (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Canonical}
    (sample : OverlapSample left right point) (leftInside : leftBox.Contains point)
    (rightInside : rightBox.Contains point) (unflipped : sample.alignment.flip = false) (exponent : Nat) :
    normSq (numerator.eval point * (left.value.eval point) ^ exponent -
      numerator.eval point * (right.value.eval point) ^ exponent) ≤
      bounds.powerScale exponent * (left.bound + right.bound) := by
  have leftNorm := bounds.inverse_norm_le left leftInside
  have rightResidual : Canonical.normSq
      (1 - polynomial.eval point * (right.value.eval point) ^ 2) ≤ 1 / 16 := by
    rewrite [← right.residual_eq]
    exact (right.residualBound point rightInside).trans right.bound_small
  have rightNorm := bounds.inverse_norm_le_of_residual leftInside rightResidual
  have distance := sample.distance_le leftInside rightInside
  rewrite [sample.alignment.value_eq, unflipped, sample.leftValue_eq, sample.rightValue_eq] at distance
  change Canonical.normSq (left.value.eval point - right.value.eval point) ≤
    6 * (left.bound + right.bound) * Canonical.normSq (left.value.eval point) at distance
  have distanceBound : normSq (left.value.eval point - right.value.eval point) ≤
      6 * (left.bound + right.bound) * bounds.inverseUpper := by
    have scalar : normSq (left.value.eval point - right.value.eval point) ≤
        6 * (left.bound + right.bound) * normSq (left.value.eval point) := by
      simpa only [Norm.Basic.normSq_eq_canonical] using distance
    exact scalar.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (by simpa only [Norm.Basic.normSq_eq_canonical] using leftNorm)
      (Arithmetic.mul_nonneg_direct (by decide)
        (Arithmetic.add_le_add_direct left.bound_nonnegative right.bound_nonnegative)))
  have powered := IntegrationQuotientVariation.normSq_pow_sub_pow_le bounds.inverseUpper_positive.le exponent
    (by simpa only [Norm.Basic.normSq_eq_canonical] using leftNorm)
    (by simpa only [Norm.Basic.normSq_eq_canonical] using rightNorm)
  have numeratorBound := Bounds.Box.normSq_eval_le_denseEvalNormBound numerator leftInside
  have numeratorOrder : normSq (numerator.eval point) ≤ bounds.numeratorUpper :=
    numeratorBound.trans_eq bounds.numeratorUpper_eq.symm
  have difference : numerator.eval point * (left.value.eval point) ^ exponent -
      numerator.eval point * (right.value.eval point) ^ exponent =
      numerator.eval point * ((left.value.eval point) ^ exponent - (right.value.eval point) ^ exponent) := by ring1
  rewrite [difference, Norm.Basic.normSq_mul]
  have bound := Arithmetic.mul_le_mul_direct numeratorOrder
    (powered.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct distanceBound
      (IntegrationQuotientVariation.powerSlope_nonnegative bounds.inverseUpper_positive.le exponent)))
    (Norm.Basic.normSq_nonneg _) bounds.numeratorUpper_nonnegative
  exact bound.trans_eq (by unfold powerScale; ring1)

/-- The old inverse coefficient has the original exponent-one full-numerator bound. -/
theorem coefficient_inverse_gap_le (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Canonical}
    (sample : OverlapSample left right point) (leftInside : leftBox.Contains point)
    (rightInside : rightBox.Contains point) (unflipped : sample.alignment.flip = false) :
    normSq (numerator.eval point * left.value.eval point - numerator.eval point * right.value.eval point) ≤
      bounds.powerScale 1 * (left.bound + right.bound) := by
  simpa only [pow_one] using bounds.coefficient_power_gap_le sample leftInside rightInside unflipped 1

/-- The actual two original cube tables have the full-numerator exponent-three bound. -/
theorem coefficient_cube_gap_le (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Canonical}
    (sample : OverlapSample left right point) (leftPowers : OddPowers left.value) (rightPowers : OddPowers right.value)
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point)
    (unflipped : sample.alignment.flip = false) :
    normSq (numerator.eval point * leftPowers.cube.eval point - numerator.eval point * rightPowers.cube.eval point) ≤
      bounds.powerScale 3 * (left.bound + right.bound) := by
  simpa only [leftPowers.cube_eval, rightPowers.cube_eval] using
    bounds.coefficient_power_gap_le sample leftInside rightInside unflipped 3

/-- The actual two original fifth-power tables have the full-numerator exponent-five bound. -/
theorem coefficient_fifth_gap_le (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Canonical}
    (sample : OverlapSample left right point) (leftPowers : OddPowers left.value) (rightPowers : OddPowers right.value)
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point)
    (unflipped : sample.alignment.flip = false) :
    normSq (numerator.eval point * leftPowers.fifth.eval point - numerator.eval point * rightPowers.fifth.eval point) ≤
      bounds.powerScale 5 * (left.bound + right.bound) := by
  simpa only [leftPowers.fifth_eval, rightPowers.fifth_eval] using
    bounds.coefficient_power_gap_le sample leftInside rightInside unflipped 5

/-- Two independent original selections pay the power gap before either later model is constructed.

The scalar scale is retained once. Both whole original Selection factories
retain their distinct model-bound scales, starting floors and half-targets.
No model, power table, Point, stage cast or observation is constructed.
-/
abbrev PowerRequest (bounds : PrimitiveOverlapBounds clearance numerator)
    (left : Model polynomial leftBox) (right : Model polynomial rightBox) (exponent leftFloor rightFloor : Nat)
    (target : Rational) (positive : 0 < target) :=
  Σ scale : {value : Rational // value = bounds.powerScale exponent},
  {value : Geometric.Search.Selection (scale.val * left.bound) leftFloor (target / 2) //
    value = Geometric.Search.Selection.build (scale.val * left.bound)
      (Arithmetic.mul_nonneg_direct (scale.property.symm ▸ bounds.powerScale_nonnegative exponent)
        left.bound_nonnegative) leftFloor (target / 2) (Field.div_pos_direct positive (by decide))} ×
  {value : Geometric.Search.Selection (scale.val * right.bound) rightFloor (target / 2) //
    value = Geometric.Search.Selection.build (scale.val * right.bound)
      (Arithmetic.mul_nonneg_direct (scale.property.symm ▸ bounds.powerScale_nonnegative exponent)
        right.bound_nonnegative) rightFloor (target / 2) (Field.div_pos_direct positive (by decide))}

/-- Compute both actual future model floors once using the same original numerator/clearance scale. -/
def requestPowerGap (bounds : PrimitiveOverlapBounds clearance numerator)
    (left : Model polynomial leftBox) (right : Model polynomial rightBox) (exponent leftFloor rightFloor : Nat)
    (target : Rational) (positive : 0 < target) :
    PowerRequest bounds left right exponent leftFloor rightFloor target positive :=
  let scale := bounds.powerScale exponent
  let first := Geometric.Search.Selection.build (scale * left.bound)
    (Arithmetic.mul_nonneg_direct (bounds.powerScale_nonnegative exponent) left.bound_nonnegative)
    leftFloor (target / 2) (Field.div_pos_direct positive (by decide))
  let last := Geometric.Search.Selection.build (scale * right.bound)
    (Arithmetic.mul_nonneg_direct (bounds.powerScale_nonnegative exponent) right.bound_nonnegative)
    rightFloor (target / 2) (Field.div_pos_direct positive (by decide))
  ⟨⟨scale, rfl⟩, ⟨first, rfl⟩, ⟨last, rfl⟩⟩

namespace PowerRequest

variable {bounds : PrimitiveOverlapBounds clearance numerator}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox}
    {exponent leftFloor rightFloor : Nat} {target : Rational} {positive : 0 < target}
    (request : PowerRequest bounds left right exponent leftFloor rightFloor target positive)

/-- Read the same once-computed complete power-gap scale. -/
abbrev scale : Rational := request.1.val

/-- Read the actual first-model selection and its own original floor. -/
abbrev first := request.2.1.val

/-- Read the independent actual second-model selection and its own original floor. -/
abbrev last := request.2.2.val

/-- The retained scale is the original numerator/clearance power scale. -/
theorem scale_eq : request.scale = bounds.powerScale exponent := request.1.property

/-- Every actual later pair pays the requested gap using its SAME two original model indices. -/
theorem later_gap_lt {firstIndex lastIndex : Nat}
    (firstPaid : request.first.stage ≤ firstIndex) (lastPaid : request.last.stage ≤ lastIndex) :
    request.scale * ((left.refine firstIndex).bound + (right.refine lastIndex).bound) < target := by
  have first := request.first.later_accurate firstPaid
  have last := request.last.later_accurate lastPaid
  have sum := Arithmetic.add_lt_add_direct first last
  have scalar : request.scale * ((left.refine firstIndex).bound + (right.refine lastIndex).bound) =
      Geometric.Basic.quarterRadius (request.scale * left.bound) firstIndex +
        Geometric.Basic.quarterRadius (request.scale * right.bound) lastIndex := by
    rewrite [left.refine_bound, right.refine_bound]
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
    ring1
  exact scalar.trans_lt (sum.trans_eq (Data.Rat.Fraction.Field.two_halves target))

/-- The SAME actual later model overlap pays the requested full-numerator power gap.

Both independent refined models and their original overlap sample remain
explicit. The retained sign is genuine model-comparison evidence; the
strict numerical bound follows from the two original selected floors.
-/
theorem later_coefficient_gap_lt {firstIndex lastIndex : Nat} {point : Canonical}
    (sample : OverlapSample (left.refine firstIndex) (right.refine lastIndex) point)
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point)
    (unflipped : sample.alignment.flip = false)
    (firstPaid : request.first.stage ≤ firstIndex) (lastPaid : request.last.stage ≤ lastIndex) :
    normSq (numerator.eval point * ((left.refine firstIndex).value.eval point) ^ exponent -
      numerator.eval point * ((right.refine lastIndex).value.eval point) ^ exponent) < target := by
  have gap := bounds.coefficient_power_gap_le sample leftInside rightInside unflipped exponent
  have scale := congrArg (fun value : Rational =>
    value * ((left.refine firstIndex).bound + (right.refine lastIndex).bound)) request.scale_eq.symm
  exact gap.trans_lt (scale.trans_lt (request.later_gap_lt firstPaid lastPaid))

end PowerRequest

end Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds

end
