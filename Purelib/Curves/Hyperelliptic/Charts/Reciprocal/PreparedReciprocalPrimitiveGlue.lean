module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Semiring.Normalization
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Segment.Increment
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSheets
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational.Box
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Primitive
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPrimitive

/-!
# Finite primitive substitution on a sheet-matched reciprocal arc

Compare the source primitive with the negative reciprocal primitive on the
actual inverted path. Finite subdivision removes both Taylor remainders and
the non-affine inversion remainder. Only the two inverse-model residuals
remain; no prepared-center allowance or fixed error floor is introduced.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue

open Purelib.Riemann.Paths
open Purelib.Riemann.Readings
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Riemann.Branches.PreparedPrimitiveSheets (CompatiblePatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives (Patch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples (Attachment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSheets (CommonPrefix)
open PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus leftCount rightCount : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {boundary :
    ParentOnBoundary parent (Purelib.Curves.Hyperelliptic.Branches.Cuts.Ambient curve)}
  {attached : Attachment parent boundary} {source : Purelib.Riemann.Branches.PreparedPrimitiveSheets.CompatiblePatch
    parent leftCount}
  {reciprocal : Patch parent boundary attached rightCount} {leftIndex rightIndex : Nat}

/-- The original differential numerator and reciprocal coordinate factor satisfy the exact reversed-differential
substitution identity at a nonzero point. -/
theorem numerator_factor (differential : Differentials.Basic.Differential genus) (point : Data.Gaussian.Basic.Canonical)
  (nonzero : point ≠ 0) :
    (differentialNumerator differential).eval point * ReciprocalRootNames.factor genus point =
      (point⁻¹) ^ 2 * (differentialNumerator (HyperellipticReciprocal.reversedDifferential differential)).eval point⁻¹
        := by
  rw [PreparedPrimitiveSamples.differentialNumerator_eval, PreparedPrimitiveSamples.differentialNumerator_eval,
    ReciprocalRootNames.factor]
  have balance : genus + 1 = differential.exponent + (2 + (HyperellipticReciprocal.reversedDifferential
    differential).exponent) := by
    have equation := HyperellipticReciprocal.differential_balance differential
    omega
  rw [balance, pow_add]
  calc
    _ = (point ^ differential.exponent * (point⁻¹) ^ differential.exponent) *
        (point⁻¹) ^ (2 + (HyperellipticReciprocal.reversedDifferential differential).exponent) := by ring1
    _ = _ := by
      rw [← Algebra.Semiring.Normalization.product_pow, Algebra.Field.ExplicitField.mul_inv_cancel point nonzero,
        one_pow, Data.Gaussian.Basic.one_mul, pow_add]

/-- A fixed, coefficient-computed density ceiling, independent of either inverse-model refinement index and of the
chosen point of the common arc. -/
@[expose] def density (source : PreparedPrimitiveSheets.CompatiblePatch parent leftCount) : Fraction.Rational :=
  6 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant (differentialNumerator differential) source.neighborhood.base.box
    *
    (SeededPrimitiveBounds.derivativeBounds source.neighborhood.base).inverseUpper

/-- The retained coefficient-computed source density ceiling is strictly positive. -/
theorem density_positive (source : PreparedPrimitiveSheets.CompatiblePatch parent leftCount) : 0 <
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.density source :=
  Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _))
    (SeededPrimitiveBounds.derivativeBounds source.neighborhood.base).inverseUpper_positive

/-- The retained source density times the sum of the original source and reciprocal inverse-model residual bounds. -/
@[expose] def coefficientError (source : PreparedPrimitiveSheets.CompatiblePatch parent leftCount) (reciprocal : Patch
  parent boundary attached rightCount)
    (leftIndex rightIndex : Nat) : Fraction.Rational :=
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.density source *
    ((source.neighborhood.base.refine leftIndex).bound + (reciprocal.patch.base.refine rightIndex).bound)

/-- The retained two-model coefficient error allowance is nonnegative. -/
theorem coefficientError_nonnegative : 0 ≤
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.coefficientError source reciprocal leftIndex
  rightIndex :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.density_positive source).le
    (add_nonneg (source.neighborhood.base.refine leftIndex).bound_nonnegative (reciprocal.patch.base.refine
      rightIndex).bound_nonnegative)

/-- The derivative substitution is valid on the whole covered source arc, using the sign selected by its original
operational root occurrence. -/
theorem coefficient_distance_le (covered : CommonPrefix source reciprocal)
    (left : InverseRootPrimitive.PrimitiveModel source.neighborhood leftIndex (differentialNumerator differential))
    (right : InverseRootPrimitive.PrimitiveModel reciprocal.patch rightIndex
      (differentialNumerator (HyperellipticReciprocal.reversedDifferential differential)))
    (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ covered.fraction) :
    Data.Gaussian.Norm.Basic.normSq (left.coefficient.eval (parent.edge.point parameter) - (parent.edge.point
      parameter)⁻¹ ^ 2 *
      right.coefficient.eval (parent.edge.point parameter)⁻¹) ≤
        Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.coefficientError source reciprocal
        leftIndex rightIndex := by
  let point := parent.edge.point parameter
  have nonzero := PreparedExteriorReciprocal.parent_point_nonzero boundary ⟨inside.1, inside.2.trans covered.upper⟩
  have identity : left.coefficient.eval point - point⁻¹ ^ 2 * right.coefficient.eval point⁻¹ =
      (differentialNumerator differential).eval point *
        ((source.neighborhood.base.refine leftIndex).value.eval point -
          ReciprocalInverseModelOverlap.value curve (reciprocal.patch.base.refine rightIndex) point) := by
    rw [left.coefficient_eq, right.coefficient_eq]
    dsimp only [ReciprocalInverseModelOverlap.value]
    have transport := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.numerator_factor
      differential point nonzero
    calc
      _ = (differentialNumerator differential).eval point * (source.neighborhood.base.refine leftIndex).value.eval point
        -
          ((differentialNumerator differential).eval point * ReciprocalRootNames.factor genus point) *
            (reciprocal.patch.base.refine rightIndex).value.eval point⁻¹ := by rw [transport]; ring1
      _ = _ := by ring1
  have pointInside := source.neighborhood.box_refines.contains (covered.source_contains parameter inside)
  have numeratorBound := Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant (differentialNumerator
    differential) pointInside
  have inverseBound := (SeededPrimitiveBounds.derivativeBounds source.neighborhood.base).value_le
    (source.neighborhood.base.refine leftIndex) pointInside
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at inverseBound
  have sumNonnegative := add_nonneg (source.neighborhood.base.refine leftIndex).bound_nonnegative
    (reciprocal.patch.base.refine rightIndex).bound_nonnegative
  rw [identity, Data.Gaussian.Norm.Basic.normSq_mul]
  calc
    _ ≤ Data.Gaussian.Norm.Basic.normSq ((differentialNumerator differential).eval point) *
        (6 * ((source.neighborhood.base.refine leftIndex).bound + (reciprocal.patch.base.refine rightIndex).bound) *
          Data.Gaussian.Norm.Basic.normSq ((source.neighborhood.base.refine leftIndex).value.eval point)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (covered.distance_le leftIndex rightIndex parameter
        inside) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ = (6 * ((source.neighborhood.base.refine leftIndex).bound + (reciprocal.patch.base.refine rightIndex).bound)) *
        (Data.Gaussian.Norm.Basic.normSq ((differentialNumerator differential).eval point) *
          Data.Gaussian.Norm.Basic.normSq ((source.neighborhood.base.refine leftIndex).value.eval point)) := by
          ring1
    _ ≤ (6 * ((source.neighborhood.base.refine leftIndex).bound + (reciprocal.patch.base.refine rightIndex).bound)) *
        (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant (differentialNumerator differential)
          source.neighborhood.base.box *
          (SeededPrimitiveBounds.derivativeBounds source.neighborhood.base).inverseUpper) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_direct numeratorBound inverseBound (Data.Gaussian.Norm.Basic.normSq_nonneg
          _)
          (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _).le)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) sumNonnegative)
    _ = _ := by
      dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.coefficientError,
        Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.density];
      ring1

/-- Between original ambient-boundary points, inversion's nonlinear remainder squared norm is bounded by the fourth
power of the source movement. -/
private theorem inversion_remainder {first last : Data.Gaussian.Basic.Canonical}
    (firstBoundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) first)
    (lastBoundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) last) :
    Data.Gaussian.Norm.Basic.normSq (last⁻¹ - first⁻¹ + (first⁻¹) ^ 2 * (last - first)) ≤
      Data.Gaussian.Norm.Basic.normSq (last - first) ^ 2 := by
  have firstNonzero := PreparedExteriorReciprocal.boundary_nonzero firstBoundary
  have lastNonzero := PreparedExteriorReciprocal.boundary_nonzero lastBoundary
  have denominatorNonzero := Data.Gaussian.Field.mul_ne_zero_direct (Power.pow_ne_zero_direct _ firstNonzero 2)
    lastNonzero
  have identity : last⁻¹ - first⁻¹ + (first⁻¹) ^ 2 * (last - first) = (last - first) ^ 2 / (first ^ 2 * last) := by
    apply Data.Gaussian.Field.mul_right_cancel_of_ne denominatorNonzero
    rw [Algebra.Field.ExplicitField.div_mul_cancel _ denominatorNonzero]
    calc
      _ = first ^ 2 * (last * last⁻¹) - first * last * (first * first⁻¹) +
          (last - first) * last * (first * first⁻¹) ^ 2 := by ring1
      _ = _ := by rw [Algebra.Field.ExplicitField.mul_inv_cancel first firstNonzero,
        Algebra.Field.ExplicitField.mul_inv_cancel last lastNonzero]; ring1
  have denominatorLower : (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (first ^ 2 * last) := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : Fraction.Rational) ≤ 1)
      (PreparedExteriorReciprocal.boundary_norm_lower firstBoundary) 2
    rw [one_pow] at square
    simpa only [Fraction.Field.one_mul, -eq_self, -iff_self] using Fraction.Order.Arithmetic.mul_le_mul_direct
      square (PreparedExteriorReciprocal.boundary_norm_lower lastBoundary) (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  rw [identity, Data.Gaussian.Field.normSq_div _ _ denominatorNonzero, Power.normSq_pow]
  apply (Fraction.Order.Field.div_le_iff_pos (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)).mpr
  simpa only [Fraction.Field.mul_one_direct, -eq_self, -iff_self] using
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct denominatorLower
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/- The finite substitution estimate works for arbitrary checked polynomial
primitives. Both the owner-based local arc and the uniform complete cover
consume this same proof. -/
namespace Comparison

variable {leftCoefficient rightCoefficient : Purelib.Riemann.Normalization.InverseRootPolynomial.Polynomial}
  {leftBox rightBox : Purelib.Riemann.Normalization.InverseRootPolynomial.Box}

/-- The retained combined Taylor and inversion remainder ceiling of the original source and reciprocal polynomial
primitives. -/
private def remainderCeiling
    (left : Certificate.DensePrimitive leftCoefficient leftBox)
    (right : Certificate.DensePrimitive rightCoefficient rightBox) : Fraction.Rational :=
  4 * left.remainderBound + 8 * right.remainderBound +
    8 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant rightCoefficient rightBox

/-- The original combined Taylor and inversion remainder ceiling is nonnegative. -/
private theorem remainderCeiling_nonnegative
    (left : Certificate.DensePrimitive leftCoefficient leftBox)
    (right : Certificate.DensePrimitive rightCoefficient rightBox) : 0 ≤
      Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.remainderCeiling left right :=
  add_nonneg (add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) left.remainderBound_nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) right.remainderBound_nonnegative))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _
      _).le)

/-- The difference between the source primitive and the correctly oriented reciprocal primitive, at an actual source
parameter. -/
@[expose] def comparisonValue (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (left : Certificate.DensePrimitive leftCoefficient leftBox)
    (right : Certificate.DensePrimitive rightCoefficient rightBox) (parameter : Fraction.Rational) : Gaussian :=
  left.value.eval (parent.edge.point parameter) + right.value.eval (parent.edge.point parameter)⁻¹

/-- The original two-primitive comparison increment is bounded by its coefficient discrepancy and the retained quartic
Taylor and inversion remainder. -/
private theorem local_increment_bound (boundary : ParentOnBoundary parent (Cuts.Ambient curve))
    (interval : Data.Rat.Interval.Bounds)
    (within : ∀ parameter, interval.Contains parameter → 0 ≤ parameter ∧ parameter ≤ 1)
    (left : Certificate.DensePrimitive leftCoefficient leftBox)
    (right : Certificate.DensePrimitive rightCoefficient rightBox)
    (sourceContains : ∀ parameter, interval.Contains parameter → leftBox.Contains (parent.edge.point parameter))
    (reciprocalContains : ∀ parameter, interval.Contains parameter → rightBox.Contains (parent.edge.point parameter)⁻¹)
    (error : Fraction.Rational)
    (coefficientBound : ∀ parameter, interval.Contains parameter →
      Data.Gaussian.Norm.Basic.normSq (leftCoefficient.eval (parent.edge.point parameter) -
        (parent.edge.point parameter)⁻¹ ^ 2 * rightCoefficient.eval (parent.edge.point parameter)⁻¹) ≤ error)
    {first last : Fraction.Rational} (firstInside : interval.Contains first)
    (lastInside : interval.Contains last) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.comparisonValue parent left
      right last - Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.comparisonValue
      parent left right first) ≤
      2 * error * Data.Gaussian.Norm.Basic.normSq (parent.edge.point last - parent.edge.point first) +
        Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.remainderCeiling left right *
          Data.Gaussian.Norm.Basic.normSq (parent.edge.point last - parent.edge.point first) ^ 2 := by
  let start := parent.edge.point first
  let finish := parent.edge.point last
  let delta := finish - start
  let inverseDelta := finish⁻¹ - start⁻¹
  let firstCoefficient := leftCoefficient.eval start
  let lastCoefficient := rightCoefficient.eval start⁻¹
  let sourceError := left.value.eval finish - left.value.eval start - firstCoefficient * delta
  let reciprocalError := right.value.eval finish⁻¹ - right.value.eval start⁻¹ - lastCoefficient * inverseDelta
  let inversionError := inverseDelta + start⁻¹ ^ 2 * delta
  let sourceBoundary := boundary.point (within first firstInside)
  let finishBoundary := boundary.point (within last lastInside)
  have sourceTaylor : Data.Gaussian.Norm.Basic.normSq sourceError ≤ left.remainderBound *
    Data.Gaussian.Norm.Basic.normSq delta ^ 2 :=
    left.increment_bound (sourceContains first firstInside) (sourceContains last lastInside)
  have inverseDistance : Data.Gaussian.Norm.Basic.normSq inverseDelta ≤
    Data.Gaussian.Norm.Basic.normSq delta :=
    PreparedReciprocalSamples.inverse_movement_between sourceBoundary finishBoundary
  have reciprocalTaylor : Data.Gaussian.Norm.Basic.normSq reciprocalError ≤ right.remainderBound *
    Data.Gaussian.Norm.Basic.normSq delta ^ 2 :=
    (right.increment_bound (reciprocalContains first firstInside) (reciprocalContains last lastInside)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _) inverseDistance 2)
          right.remainderBound_nonnegative)
  have inversionBound : Data.Gaussian.Norm.Basic.normSq (lastCoefficient * inversionError) ≤
      Dense.Gaussian.Bounds.Box.denseEvalNormMajorant rightCoefficient rightBox *
        Data.Gaussian.Norm.Basic.normSq delta ^ 2 := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant rightCoefficient (reciprocalContains first
        firstInside))
      (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.inversion_remainder sourceBoundary
        finishBoundary) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _).le
  have linearBound : Data.Gaussian.Norm.Basic.normSq ((firstCoefficient - start⁻¹ ^ 2 * lastCoefficient) *
    delta) ≤
      error * Data.Gaussian.Norm.Basic.normSq delta := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (coefficientBound first firstInside) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
  have remainderBound : Data.Gaussian.Norm.Basic.normSq (sourceError + (reciprocalError + lastCoefficient *
    inversionError)) ≤
      2 * (left.remainderBound + 2 * (right.remainderBound +
        Dense.Gaussian.Bounds.Box.denseEvalNormMajorant rightCoefficient rightBox)) *
          Data.Gaussian.Norm.Basic.normSq delta ^ 2 := by
    have inner := (Data.Gaussian.Norm.Bounds.normSq_add_le_two reciprocalError (lastCoefficient * inversionError)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add reciprocalTaylor inversionBound) (by
        decide))
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two sourceError _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add sourceTaylor inner) (by decide)).trans_eq
        (by ring1))
  have identity : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.comparisonValue
    parent left right last -
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.comparisonValue parent left right
    first =
      (sourceError + (reciprocalError + lastCoefficient * inversionError)) +
        (firstCoefficient - start⁻¹ ^ 2 * lastCoefficient) * delta := by
    dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.comparisonValue,
      sourceError, reciprocalError, inversionError, inverseDelta, delta, start, finish]
    ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add remainderBound linearBound) (by
      decide)).trans_eq
      (by dsimp only
        [Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.remainderCeiling, delta,
        start, finish]; ring1))

/-- Finite subdivision removes all Taylor and inversion remainder terms. The resulting whole-arc estimate pays only the
supplied coefficient error; the two consumers below and in `UniformReciprocalPrimitives` derive that error from their
checked inverse models. -/
theorem increment_difference_le (boundary : ParentOnBoundary parent (Cuts.Ambient curve))
    (interval : Data.Rat.Interval.Bounds)
    (within : ∀ parameter, interval.Contains parameter → 0 ≤ parameter ∧ parameter ≤ 1)
    (left : Certificate.DensePrimitive leftCoefficient leftBox)
    (right : Certificate.DensePrimitive rightCoefficient rightBox)
    (sourceContains : ∀ parameter, interval.Contains parameter → leftBox.Contains (parent.edge.point parameter))
    (reciprocalContains : ∀ parameter, interval.Contains parameter → rightBox.Contains (parent.edge.point parameter)⁻¹)
    (error : Fraction.Rational)
    (coefficientBound : ∀ parameter, interval.Contains parameter →
      Data.Gaussian.Norm.Basic.normSq (leftCoefficient.eval (parent.edge.point parameter) -
        (parent.edge.point parameter)⁻¹ ^ 2 * rightCoefficient.eval (parent.edge.point parameter)⁻¹) ≤ error)
    {first last : Fraction.Rational} (firstInside : interval.Contains first)
    (lastInside : interval.Contains last) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.comparisonValue parent left
      right last - Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.comparisonValue
      parent left right first) ≤
      2 * error * Data.Gaussian.Norm.Basic.normSq parent.model.displacement * (last - first) ^ 2 := by
  let quartic := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.remainderCeiling left
    right * Data.Gaussian.Norm.Basic.normSq parent.model.displacement ^ 2
  have quarticNonnegative : 0 ≤ quartic := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.remainderCeiling_nonnegative left
      right) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  apply Gaussian.Segment.Increment.remove_quartic
    (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.comparisonValue parent left
    right) interval
    (2 * error * Data.Gaussian.Norm.Basic.normSq parent.model.displacement)
    quartic quarticNonnegative ?_ lastInside firstInside
  intro last first lastInside firstInside
  have movement : Data.Gaussian.Norm.Basic.normSq (parent.edge.point last - parent.edge.point first) =
      (last - first) ^ 2 * Data.Gaussian.Norm.Basic.normSq parent.model.displacement := by
    change Data.Gaussian.Norm.Basic.normSq (parent.edge.localSegment.pointAt last -
      parent.edge.localSegment.pointAt first) =
      (last - first) ^ 2 * Data.Gaussian.Norm.Basic.normSq (parent.edge.localSegment.pointAt 1 -
        parent.edge.localSegment.pointAt 0)
    rw [parent.edge.localSegment.normSq_pointAt_sub_pointAt last first,
      parent.edge.localSegment.normSq_pointAt_sub_pointAt 1 0]
    ring1
  exact (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.local_increment_bound
    boundary interval within left right sourceContains reciprocalContains error coefficientBound firstInside
    lastInside).trans_eq (by rw [movement]; dsimp only [quartic]; ring1)

end Comparison

/-- The difference between the source primitive and the correctly oriented reciprocal primitive, at an actual source
parameter. -/
@[expose] def comparisonValue
    (left : InverseRootPrimitive.PrimitiveModel source.neighborhood leftIndex (differentialNumerator differential))
    (right : InverseRootPrimitive.PrimitiveModel reciprocal.patch rightIndex
      (differentialNumerator (HyperellipticReciprocal.reversedDifferential differential))) (parameter :
        Fraction.Rational) : Gaussian :=
  left.primitive.value.eval (parent.edge.point parameter) + right.primitive.value.eval (parent.edge.point parameter)⁻¹

/-- Finite subdivision removes all Taylor and inversion remainder terms. The resulting whole-arc primitive comparison
pays only the two shrinking inverse-model residuals, with no caller transport equality or exact root. -/
theorem increment_difference_le (covered : CommonPrefix source reciprocal)
    (left : InverseRootPrimitive.PrimitiveModel source.neighborhood leftIndex (differentialNumerator differential))
    (right : InverseRootPrimitive.PrimitiveModel reciprocal.patch rightIndex
      (differentialNumerator (HyperellipticReciprocal.reversedDifferential differential)))
    {first last : Fraction.Rational} (firstInside : 0 ≤ first ∧ first ≤ covered.fraction)
    (lastInside : 0 ≤ last ∧ last ≤ covered.fraction) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.comparisonValue left right last -
      Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.comparisonValue left right first) ≤
      2 * Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.coefficientError source reciprocal
        leftIndex rightIndex * Data.Gaussian.Norm.Basic.normSq parent.model.displacement * (last - first) ^ 2
        := by
  exact Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Comparison.increment_difference_le
    boundary ⟨0, covered.fraction, covered.positive.le⟩
    (fun _ inside => ⟨inside.1, inside.2.trans covered.upper⟩) left.primitive right.primitive
    covered.source_contains covered.reciprocal_contains
      (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.coefficientError source reciprocal
      leftIndex rightIndex)
    (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.coefficient_distance_le covered left right)
      firstInside lastInside

set_option genInjectivity false in
/-- Requested primitive matching on one fixed covered arc. Both increments and the checked numerical bound are retained,
so downstream sewing need not evaluate the primitive polynomials again. The arc is independent of target. -/
structure Request (covered : CommonPrefix source reciprocal) (target : Fraction.Rational) where
  /-- The retained source inverse-model refinement index for the original comparison target. -/ leftIndex : Nat
  /-- The retained reciprocal inverse-model refinement index for the original comparison target. -/ rightIndex : Nat
  /-- The cached source primitive model at its retained refinement index. -/ left : InverseRootPrimitive.PrimitiveModel
    source.neighborhood leftIndex (differentialNumerator differential)
  /-- The cached reciprocal primitive model at its retained refinement index. -/ right :
    InverseRootPrimitive.PrimitiveModel reciprocal.patch rightIndex
    (differentialNumerator (HyperellipticReciprocal.reversedDifferential differential))
  /-- The cached original source primitive increment over the fixed common prefix. -/ sourceIncrement :
    Data.Gaussian.Basic.Canonical
  /-- The cached source increment is exactly the retained source polynomial's endpoint difference. -/ sourceIncrement_eq
    : sourceIncrement = left.primitive.value.eval (parent.edge.point covered.fraction) -
    left.primitive.value.eval (parent.edge.point 0)
  /-- The cached negatively oriented reciprocal primitive increment over the actual inverted prefix. -/
    reciprocalIncrement : Data.Gaussian.Basic.Canonical
  /-- The reciprocal increment is exactly the negative retained polynomial difference at the original inverted
    endpoints. -/ reciprocalIncrement_eq : reciprocalIncrement = -(right.primitive.value.eval (parent.edge.point
    covered.fraction)⁻¹ -
    right.primitive.value.eval (parent.edge.point 0)⁻¹)
  /-- The cached two-model comparison allowance on the original common source arc. -/ error : Fraction.Rational
  /-- The retained allowance is exactly twice the coefficient-error bound times the original source displacement squared
    norm and prefix fraction squared. -/ error_eq : error = 2 *
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.coefficientError source reciprocal leftIndex
    rightIndex *
    Data.Gaussian.Norm.Basic.normSq parent.model.displacement * covered.fraction ^ 2
  /-- The cached comparison allowance is strictly below the original requested target. -/ error_lt : error < target
  /-- The cached original source and reciprocal increments differ within the retained squared-norm allowance. -/ close :
    Data.Gaussian.Norm.Basic.normSq (sourceIncrement - reciprocalIncrement) ≤ error

constructive_injectivity Request

namespace Request

/-- Select independent source and reciprocal refinement stages for the positive target and cache both original primitive
increments with their exact comparison bound. -/
@[expose] def build (covered : CommonPrefix source reciprocal) (target : Fraction.Rational) (positive : 0 < target) :
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Request covered target := by
  let weight := 2 * Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.density source *
    Data.Gaussian.Norm.Basic.normSq parent.model.displacement * covered.fraction ^ 2
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.density_positive source).le)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have weightPositive : 0 < weight + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct weightNonnegative
    (by decide)
  let denominator := 2 * (weight + 1)
  have denominatorPositive : 0 < denominator := Fraction.Order.Arithmetic.mul_pos_direct (by decide) weightPositive
  let tolerance := target / denominator
  have tolerancePositive : 0 < tolerance := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  let leftIndex := Search.firstQuarterBelow source.neighborhood.base.model.bound 0 tolerance
  let rightIndex := Search.firstQuarterBelow reciprocal.patch.base.model.bound 0 tolerance
  have leftSmall : (source.neighborhood.base.refine leftIndex).bound < tolerance := by
    change (source.neighborhood.base.model.refine leftIndex).bound < tolerance
    rw [InverseRootPolynomial.Model.refine_bound]
    exact Search.firstQuarterBelow_accurate _ source.neighborhood.base.model.bound_nonnegative 0 _ tolerancePositive
  have rightSmall : (reciprocal.patch.base.refine rightIndex).bound < tolerance := by
    change (reciprocal.patch.base.model.refine rightIndex).bound < tolerance
    rw [InverseRootPolynomial.Model.refine_bound]
    exact Search.firstQuarterBelow_accurate _ reciprocal.patch.base.model.bound_nonnegative 0 _ tolerancePositive
  let left := PrimitiveModel.ofIndex source.neighborhood leftIndex (differentialNumerator differential)
  let right := PrimitiveModel.ofIndex reciprocal.patch rightIndex
    (differentialNumerator (HyperellipticReciprocal.reversedDifferential differential))
  let error := 2 * Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.coefficientError source
    reciprocal leftIndex rightIndex * Data.Gaussian.Norm.Basic.normSq parent.model.displacement *
    covered.fraction ^ 2
  have errorSmall : error < target := by
    have errorIdentity : error = weight *
        ((source.neighborhood.base.refine leftIndex).bound + (reciprocal.patch.base.refine rightIndex).bound) := by
      dsimp only [error, weight,
        Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.coefficientError]
      ring1
    rw [errorIdentity]
    calc
      _ ≤ (weight + 1) * ((source.neighborhood.base.refine leftIndex).bound + (reciprocal.patch.base.refine
        rightIndex).bound) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (le_add_of_nonneg_right (by decide : (0 : Fraction.Rational) ≤ 1))
          (add_nonneg (source.neighborhood.base.refine leftIndex).bound_nonnegative
            (reciprocal.patch.base.refine rightIndex).bound_nonnegative)
      _ < (weight + 1) * (tolerance + tolerance) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct weightPositive
          (Fraction.Order.Arithmetic.add_lt_add_direct leftSmall rightSmall)
      _ = tolerance * denominator := by dsimp only [denominator]; ring1
      _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  refine
    { leftIndex := leftIndex
      rightIndex := rightIndex
      left := left
      right := right
      sourceIncrement := left.primitive.value.eval (parent.edge.point covered.fraction) - left.primitive.value.eval
        (parent.edge.point 0)
      sourceIncrement_eq := rfl
      reciprocalIncrement := -(right.primitive.value.eval (parent.edge.point covered.fraction)⁻¹ -
        right.primitive.value.eval (parent.edge.point 0)⁻¹)
      reciprocalIncrement_eq := rfl
      error := error
      error_eq := rfl
      error_lt := errorSmall
      close := ?_ }
  have identity : left.primitive.value.eval (parent.edge.point covered.fraction) - left.primitive.value.eval
    (parent.edge.point 0) -
      -(right.primitive.value.eval (parent.edge.point covered.fraction)⁻¹ - right.primitive.value.eval
        (parent.edge.point 0)⁻¹) =
        Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.comparisonValue left right
          covered.fraction - Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.comparisonValue left
          right 0 := by
    dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.comparisonValue]
    ring1
  rw [identity]
  have bound := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.increment_difference_le covered
    left right (first := 0) (last := covered.fraction)
    ⟨le_rfl, covered.positive.le⟩ ⟨covered.positive.le, le_rfl⟩
  exact bound.trans_eq (by dsimp only [error]; ring1)

end Request

/-- Start with the reciprocal reading already owned by the original period bank. The source occurrence, reciprocal
occurrence, fixed common arc, both primitive models, requested indices and matching increments are constructed
internally. This is local gluing, not yet a full-boundary subdivision. -/
@[expose] def acquire {readingTarget : Fraction.Rational} (reading : PreparedReciprocalSamples.Reading parent boundary
  readingTarget)
    (target : Fraction.Rational) (positive : 0 < target) :
    (source : PreparedPrimitiveSheets.CompatiblePatch parent genus) × (reciprocal : Patch parent boundary reading.1
      genus) ×
      (covered : CommonPrefix source reciprocal) ×
        Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Request covered target :=
  let patches := PreparedReciprocalSheets.acquire reading
  ⟨patches.1, patches.2.1, patches.2.2,
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue.Request.build patches.2.2 target positive⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue
