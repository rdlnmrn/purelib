module
import Purelib.Riemann.Normalization.InverseRootComparison
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

public import Purelib.Riemann.Normalization.InverseRootPrimitive
public import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Gaussian

@[expose] public section

/-!
# Local primitives and actual prepared constant-cell samples

The finite root in a prepared cell is not an exact square root, and its
persisted coefficient center need not equal a freshly chosen root quotient.
This bridge pays both discrepancies.  The geometric containment and relative
residual conditions are explicit internal obligations for a local prepared
subdivision; no conclusion about arbitrary coarse cells is asserted.
-/

namespace Purelib.Riemann.Readings.PreparedPrimitiveSamples

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Integration.PreparedConstantModels

open Purelib.Data.Rat in
/-- The exact rational carrier for prepared primitive error bounds. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier for primitive and root readings. -/
abbrev Gaussian := Basic.Canonical

open Purelib.Curves.Hyperelliptic in
open Purelib.Polynomial in
/-- The monomial numerator of the original hyperelliptic differential, retaining its exact exponent. -/
def differentialNumerator {genus : Nat} (differential : Differentials.Basic.Differential genus) : Polynomial :=
  Dense.Basic.DensePolynomial.shift differential.exponent
    (Dense.Basic.DensePolynomial.constant 1)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The retained differential numerator evaluates to the point raised to the original differential exponent. -/
theorem differentialNumerator_eval {genus : Nat} (differential : Differentials.Basic.Differential genus) (point :
  Gaussian) :
    (differentialNumerator differential).eval point = point ^ differential.exponent := by
  rw [differentialNumerator, Dense.Basic.DensePolynomial.eval_shift,
    Dense.Basic.DensePolynomial.eval_constant, Basic.one_mul]

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The canonical prepared edge integral sample equals its directed endpoint displacement times the numerator divided by
the retained residual root center. -/
theorem canonical_integralSample (prepared : PreparedEdge curve differential) :
    (prepared.centeredModel (PreparedEdge.CenterState.canonical prepared)).integralSample =
      (prepared.point 1 - prepared.point 0) *
        ((differentialNumerator differential).eval (prepared.point 0) / prepared.residualRootCenter) := by
  rw [Cell.Basic.CellModel.integralSample_constant
    (prepared.centeredModel (PreparedEdge.CenterState.canonical prepared))
      (PreparedEdge.CenterState.canonical prepared).value rfl,
    prepared.canonical_value_eq_residualCoefficientCenter]
  rw [differentialNumerator_eval]
  rfl

/-- The prepared root residual target divided by one quarter of the original neighborhood's retained denominator value.
-/
def relativeError (patch : ContinuedNeighborhood curve.polynomial count)
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.rootResidualTarget / (patch.base.site.denominatorValue / 4)

open Purelib.Data.Rat in
/-- The prepared edge's relative residual error is strictly positive. -/
theorem relativeError_positive (patch : ContinuedNeighborhood curve.polynomial count)
    (prepared : PreparedEdge curve differential) : 0 < relativeError patch prepared :=
  Fraction.Order.Field.div_pos_direct prepared.rootResidualTarget_positive
    (Fraction.Order.Field.div_pos_direct patch.base.site.denominatorValue_positive (by decide))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original residual root center satisfies the relative residual estimate at the retained edge start inside the
continued box. -/
private theorem root_residual_relative (patch : ContinuedNeighborhood curve.polynomial count)
    (prepared : PreparedEdge curve differential) (inside : patch.box.Contains (prepared.point 0)) :
    normSq (prepared.residualRootCenter ^ 2 - curve.polynomial.eval (prepared.point 0)) <=
      relativeError patch prepared * normSq (curve.polynomial.eval (prepared.point 0)) := by
  have residual := prepared.residualRootState_candidate_residual_lt 0 prepared.baseInside
    prepared.residualRootCenter_possible
  have lowerPositive : 0 < patch.base.site.denominatorValue / 4 :=
    Fraction.Order.Field.div_pos_direct patch.base.site.denominatorValue_positive (by decide)
  calc
    _ <= prepared.rootResidualTarget := by simpa only [pow_two, Norm.Basic.normSq_eq_canonical] using residual.le
    _ = relativeError patch prepared * (patch.base.site.denominatorValue / 4) :=
      (Fraction.Field.div_mul_cancel_of_ne _ _ lowerPositive.ne').symm
    _ <= _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (patch.parameter_lower inside) (relativeError_positive patch prepared).le

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Normalization in
/-- Bound the indexed inverse-root model's error against the reciprocal of the retained prepared residual root center.

The original prepared-owner box refines the seed-owner box and relative residual error is at most one
four-thousand-ninety-sixth. The estimate keeps the geometric alignment term and cached positive root lower bound. -/
theorem root_inverse_error (patch : ContinuedNeighborhood curve.polynomial count)
    (prepared : PreparedEdge curve differential) (inside : patch.box.Contains (prepared.point 0))
    (rootBox : prepared.cached.preparedOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (small : relativeError patch prepared <= 1 / 4096) (index : Nat) :
    normSq ((patch.base.refine index).value.eval (prepared.point 0) - inv prepared.residualRootCenter) <=
      (Geometric.Basic.quarterRadius (1 / 256) index + 16 * relativeError patch prepared) / patch.rootLower := by
  have rootInside := rootBox.contains prepared.residualRootCenter_in_cachedBox
  have rootLower := patch.root_lower rootInside
  have rootPositive := patch.rootLower_positive.trans_le rootLower
  have nonzero : prepared.residualRootCenter ≠ 0 := by
    intro zero
    rw [zero, Basic.Canonical.normSq_zero] at rootPositive
    exact (lt_irrefl _ rootPositive)
  have initial : normSq (1 - prepared.residualRootCenter * patch.base.model.value.eval (prepared.point 0)) <= 1 / 256 :=
    by
    rw [patch.base.model_value_eq, Dense.Basic.DensePolynomial.eval_constant]
    exact patch.aligned _ rootInside
  have budgetSmall : (1 / 256 : Coordinate) + 16 * relativeError patch prepared <= 1 / 64 := by
    calc
      _ <= (1 / 256 : Coordinate) + 16 * (1 / 4096) := add_le_add le_rfl
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by decide))
      _ <= 1 / 64 := by decide +kernel
  have bound := (InverseRootComparison.Model.refine_inverse_error patch.base.model) (prepared.point 0)
    (patch.box_refines.contains inside)
    prepared.residualRootCenter nonzero (relativeError_positive patch prepared).le
    (by simpa only [Norm.Basic.normSq_eq_canonical] using root_residual_relative patch prepared inside)
    (by simpa only [Norm.Basic.normSq_eq_canonical] using initial) budgetSmall index
  simp only [Norm.Basic.normSq_eq_canonical] at bound
  have inverse_eq : Data.Gaussian.Field.inv prepared.residualRootCenter = Basic.Canonical.inv
    prepared.residualRootCenter :=
    by
    with_unfolding_all exact (Field.inv_eq prepared.residualRootCenter).symm
  rw [inverse_eq] at bound
  exact bound.trans (Fraction.Order.Field.div_le_div_of_nonneg_left_direct
    (add_nonneg (Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (relativeError_positive patch prepared).le))
    patch.rootLower_positive rootLower)

open Purelib.Approximation.Rational in
/-- The exact primitive remainder and root-reading error allowance for the canonical prepared edge sample.

The formula retains the original primitive, refinement index, numerator start reading, relative residual error and
squared endpoint movement. -/
def canonicalError {patch : ContinuedNeighborhood curve.polynomial count} {index : Nat}
    (model : PrimitiveModel patch index (differentialNumerator differential))
    (prepared : PreparedEdge curve differential) : Coordinate :=
  2 * (model.primitive.remainderBound * prepared.pointMovement ^ 2 +
    normSq ((differentialNumerator differential).eval (prepared.point 0)) *
      ((Geometric.Basic.quarterRadius (1 / 256) index + 16 * relativeError patch prepared) / patch.rootLower) *
      prepared.pointMovement)

open Purelib.Data.Gaussian in
/-- The canonical prepared edge sample differs from the original primitive increment by at most the retained canonical
error.

Both endpoints remain in the original continued box, the prepared root owner refines the original seed owner and the
relative residual error satisfies the stated smallness bound. -/
theorem canonical_integral_error {patch : ContinuedNeighborhood curve.polynomial count} {index : Nat}
    (model : PrimitiveModel patch index (differentialNumerator differential))
    (prepared : PreparedEdge curve differential)
    (startInside : patch.box.Contains (prepared.point 0)) (finishInside : patch.box.Contains (prepared.point 1))
    (rootBox : prepared.cached.preparedOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (small : relativeError patch prepared <= 1 / 4096) :
    normSq (model.primitive.value.eval (prepared.point 1) - model.primitive.value.eval (prepared.point 0) -
        (prepared.centeredModel (PreparedEdge.CenterState.canonical prepared)).integralSample) <=
      canonicalError model prepared := by
  have bound := model.increment_bound_of_inverse_error startInside finishInside
    (root_inverse_error patch prepared startInside rootBox small index)
  rw [canonical_integralSample]
  simpa only [canonicalError, PreparedEdge.pointMovement, Norm.Basic.normSq_eq_canonical, Basic.mul_comm] using bound

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Any retained center state differs from the original residual coefficient center by squared norm at most four times
the model error allowance. -/
theorem center_sub_canonical_le (prepared : PreparedEdge curve differential)
    (center : PreparedEdge.CenterState prepared) :
    normSq (center.value - prepared.residualCoefficientCenter) <= 4 * prepared.modelErrorAllowance := by
  have canonical := prepared.residualCoefficientCenter_sub_baseReading_le
  rw [Norm.Basic.normSq_eq_canonical] at canonical
  have centerClose := center.value_sub_baseReading_lt
  rw [Norm.Basic.normSq_eq_canonical] at centerClose
  have triangle := Norm.Bounds.normSq_sub_le_via center.value prepared.baseReading prepared.residualCoefficientCenter
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  have reversed : normSq (prepared.baseReading - prepared.residualCoefficientCenter) <= prepared.rawVariation := by
    have identity : prepared.baseReading - prepared.residualCoefficientCenter =
      -(prepared.residualCoefficientCenter - prepared.baseReading) := by ring1
    rw [identity, Basic.Canonical.normSq_neg]; exact canonical
  have rawLe : prepared.rawVariation <= prepared.modelErrorAllowance :=
    le_add_of_nonneg_right prepared.preparedRootDiameter_positive.le
  calc
    _ <= 2 * (normSq (center.value - prepared.baseReading) +
        normSq (prepared.baseReading - prepared.residualCoefficientCenter)) := triangle
    _ <= 2 * (prepared.modelErrorAllowance + prepared.modelErrorAllowance) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add centerClose.le (reversed.trans rawLe)) (by decide)
    _ = _ := by ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained centered and canonical edge integral samples differ by squared norm at most four times the model
allowance times the original point movement. -/
theorem centered_integral_sub_canonical_le (prepared : PreparedEdge curve differential)
    (center : PreparedEdge.CenterState prepared) :
    normSq ((prepared.centeredModel center).integralSample -
        (prepared.centeredModel (PreparedEdge.CenterState.canonical prepared)).integralSample) <=
      4 * prepared.modelErrorAllowance * prepared.pointMovement := by
  rw [Cell.Basic.CellModel.integralSample_constant
      (prepared.centeredModel center) center.value rfl,
    Cell.Basic.CellModel.integralSample_constant
      (prepared.centeredModel (PreparedEdge.CenterState.canonical prepared))
        (PreparedEdge.CenterState.canonical prepared).value rfl,
    prepared.canonical_value_eq_residualCoefficientCenter]
  change normSq ((prepared.point 1 - prepared.point 0) * center.value -
      (prepared.point 1 - prepared.point 0) * prepared.residualCoefficientCenter) <= _
  have identity : (prepared.point 1 - prepared.point 0) * center.value -
      (prepared.point 1 - prepared.point 0) * prepared.residualCoefficientCenter =
        (center.value - prepared.residualCoefficientCenter) * (prepared.point 1 - prepared.point 0) := by ring1
  rw [identity, Basic.Canonical.normSq_mul]
  simp only [PreparedEdge.pointMovement, Norm.Basic.normSq_eq_canonical]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (center_sub_canonical_le prepared center) (Basic.Canonical.normSq_nonneg _)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Bound the discrepancy between the original primitive increment and an arbitrary retained centered prepared edge
sample.

The estimate combines twice the canonical error with the retained center-rebasing allowance, preserving both endpoint
containments and the original root-owner refinement. -/
theorem centered_integral_error {patch : ContinuedNeighborhood curve.polynomial count} {index : Nat}
    (model : PrimitiveModel patch index (differentialNumerator differential))
    (prepared : PreparedEdge curve differential) (center : PreparedEdge.CenterState prepared)
    (startInside : patch.box.Contains (prepared.point 0)) (finishInside : patch.box.Contains (prepared.point 1))
    (rootBox : prepared.cached.preparedOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (small : relativeError patch prepared <= 1 / 4096) :
    normSq (model.primitive.value.eval (prepared.point 1) - model.primitive.value.eval (prepared.point 0) -
        (prepared.centeredModel center).integralSample) <=
      2 * (canonicalError model prepared + 4 * prepared.modelErrorAllowance * prepared.pointMovement) := by
  have canonical := canonical_integral_error model prepared startInside finishInside rootBox small
  have rebasing := centered_integral_sub_canonical_le prepared center
  have reverse : normSq ((prepared.centeredModel (PreparedEdge.CenterState.canonical prepared)).integralSample -
      (prepared.centeredModel center).integralSample) <= 4 * prepared.modelErrorAllowance * prepared.pointMovement := by
    have identity : (prepared.centeredModel (PreparedEdge.CenterState.canonical prepared)).integralSample -
        (prepared.centeredModel center).integralSample = -((prepared.centeredModel center).integralSample -
          (prepared.centeredModel (PreparedEdge.CenterState.canonical prepared)).integralSample) := by ring1
    rw [identity, Basic.Canonical.normSq_neg]; exact rebasing
  have triangle := Norm.Bounds.normSq_sub_le_via
    (model.primitive.value.eval (prepared.point 1) - model.primitive.value.eval (prepared.point 0))
    ((prepared.centeredModel (PreparedEdge.CenterState.canonical prepared)).integralSample)
    ((prepared.centeredModel center).integralSample)
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  exact triangle.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add canonical reverse) (by decide))

open Purelib.Data.Rat in
/-- A bound on the original model allowance also bounds relative residual error after division by the retained positive
denominator lower bound. -/
theorem relativeError_le (patch : ContinuedNeighborhood curve.polynomial count)
    (prepared : PreparedEdge curve differential) {error : Coordinate}
    (bounded : prepared.modelErrorAllowance ≤ error) :
    relativeError patch prepared ≤ error / (patch.base.site.denominatorValue / 4) := by
  have residual : prepared.rootResidualTarget ≤ error :=
    prepared.rootResidualTarget_le_modelErrorAllowance.trans bounded
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct residual
    (Fraction.Order.Field.inv_pos_direct
      (Fraction.Order.Field.div_pos_direct patch.base.site.denominatorValue_positive (by decide))).le

open Purelib.Approximation.Rational in
/-- The retained linear movement-error coefficient for the indexed inverse-root model and supplied numerator and
model-allowance majorants.

It includes four times the numerator majorant times the geometric inverse-error estimate and eight times the model
allowance majorant. -/
def coefficientError (patch : ContinuedNeighborhood curve.polynomial count)
    (index : Nat) (numeratorBound error : Coordinate) : Coordinate :=
  4 * numeratorBound *
    ((Geometric.Basic.quarterRadius (1 / 256) index +
      16 * (error / (patch.base.site.denominatorValue / 4))) / patch.rootLower) + 8 * error

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The retained coefficient error is nonnegative whenever the supplied numerator and model-allowance majorants are
nonnegative. -/
theorem coefficientError_nonnegative (patch : ContinuedNeighborhood curve.polynomial count)
    (index : Nat) {numeratorBound error : Coordinate}
    (numeratorNonnegative : 0 ≤ numeratorBound) (errorNonnegative : 0 ≤ error) :
    0 ≤ coefficientError patch index numeratorBound error := by
  exact add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) numeratorNonnegative)
      (Fraction.Order.Field.div_nonneg_direct
        (add_nonneg (Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (Fraction.Order.Field.div_nonneg_direct errorNonnegative
              (Fraction.Order.Field.div_pos_direct patch.base.site.denominatorValue_positive (by decide)).le)))
        patch.rootLower_positive.le))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) errorNonnegative)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Bound a retained centered edge sample's primitive discrepancy using supplied uniform numerator, model-error and
movement majorants.

The original prepared root box refines the seed box, both endpoints lie in the continued box and the relative majorant
meets the smallness threshold. The estimate separates quadratic movement remainder from linear coefficient error. -/
theorem centered_integral_error_uniform {patch : ContinuedNeighborhood curve.polynomial count} {index : Nat}
    (model : PrimitiveModel patch index (differentialNumerator differential))
    (prepared : PreparedEdge curve differential) (center : PreparedEdge.CenterState prepared)
    (startInside : patch.box.Contains (prepared.point 0)) (finishInside : patch.box.Contains (prepared.point 1))
    (rootBox : prepared.cached.preparedOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    {numeratorBound error movement : Coordinate}
    (numeratorLe : normSq ((differentialNumerator differential).eval (prepared.point 0)) ≤ numeratorBound)
    (errorLe : prepared.modelErrorAllowance ≤ error)
    (small : error / (patch.base.site.denominatorValue / 4) ≤ 1 / 4096)
    (movementLe : prepared.pointMovement ≤ movement) :
    normSq (model.primitive.value.eval (prepared.point 1) - model.primitive.value.eval (prepared.point 0) -
        (prepared.centeredModel center).integralSample) ≤
      4 * model.primitive.remainderBound * movement ^ 2 + coefficientError patch index numeratorBound error * movement
        := by
  have relativeLe := relativeError_le patch prepared errorLe
  have numeratorNonnegative := (Basic.Canonical.normSq_nonneg _).trans numeratorLe
  have errorNonnegative := prepared.modelErrorAllowance_positive.le.trans errorLe
  have movementNonnegative : 0 ≤ prepared.pointMovement := Norm.Basic.normSq_nonneg _
  have inverseLe :
      (Geometric.Basic.quarterRadius (1 / 256) index + 16 * relativeError patch prepared) / patch.rootLower ≤
        (Geometric.Basic.quarterRadius (1 / 256) index +
          16 * (error / (patch.base.site.denominatorValue / 4))) / patch.rootLower :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct relativeLe (by decide)))
      (Fraction.Order.Field.inv_pos_direct patch.rootLower_positive).le
  have inverseNonnegative : 0 ≤
      (Geometric.Basic.quarterRadius (1 / 256) index + 16 * relativeError patch prepared) / patch.rootLower :=
    Fraction.Order.Field.div_nonneg_direct
      (add_nonneg (Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (relativeError_positive patch prepared).le))
      patch.rootLower_positive.le
  have numeratorTerm := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_direct numeratorLe inverseLe inverseNonnegative numeratorNonnegative)
    movementNonnegative
  have rebasingTerm : 4 * prepared.modelErrorAllowance * prepared.pointMovement ≤
      4 * error * prepared.pointMovement := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by decide)) movementNonnegative
  have localBound := centered_integral_error model prepared center startInside finishInside rootBox (relativeLe.trans
    small)
  calc
    _ ≤ 2 * (canonicalError model prepared + 4 * prepared.modelErrorAllowance * prepared.pointMovement) := localBound
    _ ≤ 2 * (2 * (model.primitive.remainderBound * prepared.pointMovement ^ 2 +
        numeratorBound * ((Geometric.Basic.quarterRadius (1 / 256) index +
          16 * (error / (patch.base.site.denominatorValue / 4))) / patch.rootLower) * prepared.pointMovement) +
        4 * error * prepared.pointMovement) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add le_rfl numeratorTerm) (by decide)) rebasingTerm) (by decide)
    _ = 4 * model.primitive.remainderBound * prepared.pointMovement ^ 2 +
        coefficientError patch index numeratorBound error * prepared.pointMovement := by unfold coefficientError; ring1
    _ ≤ _ := add_le_add
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.pow_le_pow_direct movementNonnegative movementLe 2)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) model.primitive.remainderBound_nonnegative))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movementLe
        (coefficientError_nonnegative patch index numeratorNonnegative errorNonnegative))

end Purelib.Riemann.Readings.PreparedPrimitiveSamples
