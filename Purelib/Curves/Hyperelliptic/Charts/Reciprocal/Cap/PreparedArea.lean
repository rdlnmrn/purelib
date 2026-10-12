module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
public import Purelib.Riemann.Paths.PreparedPrimitivePathArea
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FactorBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Cap polynomial areas on the actual prepared children

Use the retained child endpoints for both the cap polynomial and the local
primitive. Their derivative discrepancy and the operational integration
error each carry the child's squared width. Finite area comparison cancels
all four powers of the child count, retaining every intermediate excursion.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Rational
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Integration.Polynomial.Gaussian.Path.Basic
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
open Purelib.Polynomial.Geometry
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPrimitivePathArea
open Purelib.Riemann.Readings
open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent ParentData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives (Request Sample)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg quarterRadius_eq_mul_pow)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement movement_nonnegative)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Path.IncrementArea (pathArea Summary)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Differential genus} {count : Nat}
  {parent : Parent curve differential} {data :
    ParentData cap differential count parent}

/-- The retained parent movement is the squared distance between its actual endpoint coordinates. -/
private theorem movement_eq (parent : PathCover.Parent curve differential) :
    PreparedPrimitiveRequests.movement parent = Data.Gaussian.Norm.Basic.normSq (parent.edge.point 1 -
      parent.edge.point 0) := by
  rw [parent.edge.point_one, parent.edge.point_zero]
  rfl

/-- The fixed coefficient ceiling comes from the original cap numerator box and the retained local inverse clearance. It
precedes model refinement. -/
@[expose] public def areaSlope (data : PathCover.ParentData cap differential count parent) : Coordinate :=
  2 * data.comparison.bounds.factor.base.numeratorUpper * data.comparison.bounds.reciprocal.inverseUpper *
    PreparedPrimitiveRequests.movement parent

/-- The retained cap numerator ceiling, inverse bound and parent movement give a nonnegative area slope. -/
theorem areaSlope_nonnegative (data : PathCover.ParentData cap differential count parent) : 0 ≤
  areaSlope data :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        data.comparison.bounds.factor.base.numeratorUpper_nonnegative)
      data.comparison.bounds.reciprocal.inverseUpper_positive.le) (PreparedPrimitiveRequests.movement_nonnegative
        parent)

namespace Sample

variable {target : Coordinate} {floor : Nat} {request :
  Request data target floor}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Reuse the existing spatial request and original uniform patch. -/
@[expose] public def localRequest (sample : PreparedPrimitives.Sample request capSample) :
  UniformPreparedRequests.LocalRequest parent count request.budget :=
  ⟨data.patch, data.terminal.neighborhood.patch, data.patch_eq, sample.integration,
    data.last_eq ▸ data.segment.lastInside⟩

/-- Each retained integration child has both endpoints inside the original local patch and cap collar. -/
private theorem child_inside (sample : PreparedPrimitives.Sample request capSample) {child : PathCover.Parent curve
  differential}
    (member : child ∈ sample.integration.block.children) :
    (data.terminal.neighborhood.patch.box.Contains (child.edge.point 0) ∧
      data.terminal.neighborhood.patch.box.Contains (child.edge.point 1)) ∧
    (collar.box.Contains (child.edge.point 0) ∧ collar.box.Contains (child.edge.point 1)) := by
  constructor
  · exact ⟨PreparedPrimitivePaths.block_starts_inside sample.integration.block _
      (data.first_eq ▸ data.segment.firstInside) (data.last_eq ▸ data.segment.lastInside) child member,
      PreparedPrimitivePaths.block_finishes_inside sample.integration.block _
      (data.first_eq ▸ data.segment.firstInside) (data.last_eq ▸ data.segment.lastInside) child member⟩
  · exact ⟨PreparedPrimitivePaths.block_starts_inside sample.integration.block _
      (data.first_eq ▸ data.segment.comparison.firstCap) (data.last_eq ▸ data.segment.comparison.lastCap) child member,
      PreparedPrimitivePaths.block_finishes_inside sample.integration.block _
      (data.first_eq ▸ data.segment.comparison.firstCap) (data.last_eq ▸ data.segment.comparison.lastCap) child member⟩

/-- The retained local primitive coefficient satisfies the original cap numerator and inverse ceiling. -/
private theorem coefficient_le (sample : PreparedPrimitives.Sample request capSample) {point :
  InverseRootPolynomial.Gaussian}
    (inside : data.terminal.neighborhood.patch.box.Contains point) (capInside : collar.box.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (sample.retained.retained.primitive.coefficient.eval point) ≤
      data.comparison.bounds.factor.base.numeratorUpper * data.comparison.bounds.reciprocal.inverseUpper := by
  rw [sample.retained.retained.coefficient_eq, sample.retained.retained.comparison.coefficient_eq,
    Data.Gaussian.Norm.Basic.normSq_neg, Data.Gaussian.Norm.Basic.normSq_mul]
  have numerator : Data.Gaussian.Norm.Basic.normSq (point ^ (HyperellipticReciprocal.reversedDifferential
    differential).exponent) ≤
      data.comparison.bounds.factor.base.numeratorUpper := by
    rw [← data.comparison.bounds.factor.numerator_eq, data.comparison.bounds.factor.base.numeratorUpper_eq]
    exact Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound _ capInside
  have scalar := data.comparison.bounds.reciprocal.inverse_norm_le sample.retained.retained.comparison.reciprocal
    (data.terminal.neighborhood.patch.box_refines.contains inside)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact Fraction.Order.Arithmetic.mul_le_mul_direct numerator scalar (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    data.comparison.bounds.factor.base.numeratorUpper_nonnegative

/-- A retained child's local primitive increment satisfies the parent slope bound scaled by its dyadic depth. -/
private theorem primitive_child_bound (sample : PreparedPrimitives.Sample request capSample) {child : PathCover.Parent
  curve differential}
    (member : child ∈ sample.integration.block.children) :
    Data.Gaussian.Norm.Basic.normSq (sample.integration.model.primitive.value.eval (child.edge.point 1) -
      sample.integration.model.primitive.value.eval (child.edge.point 0)) ≤ Geometric.Basic.quarterRadius
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data)
        sample.integration.block.depth := by
  have contained :=
    (child_inside sample)
    member
  let first := child.edge.point 0
  let last := child.edge.point 1
  let direction := last - first
  have startEq : Affine.line first direction 0 = first := by change first + 0 * direction = first; ring1
  have finishEq : Affine.line first direction 1 = last := by
    change first + 1 * direction = last; dsimp only [direction]; ring1
  have estimate := DensePrimitive.segment_increment_le sample.retained.retained.primitive.primitive first direction
    (⟨0, 1, by decide⟩ : Data.Rat.Interval.Bounds)
    (fun _ inside => Rational.Box.contains_line contained.1.1 contained.1.2 inside) _
    (fun _ inside =>
      (coefficient_le
      sample)
      (Rational.Box.contains_line contained.1.1 contained.1.2 inside)
      (Rational.Box.contains_line contained.2.1 contained.2.2 inside))
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  rw [startEq, finishEq, show (1 : Fraction.Rational) - 0 = 1 by decide,
    _root_.one_pow, Fraction.Field.mul_one_direct] at estimate
  rw [sample.sign, sample.sign, show -sample.retained.retained.primitive.primitive.value.eval (child.edge.point 1) -
    -sample.retained.retained.primitive.primitive.value.eval (child.edge.point 0) =
      -(sample.retained.retained.primitive.primitive.value.eval (child.edge.point 1) -
        sample.retained.retained.primitive.primitive.value.eval (child.edge.point 0)) by ring1,
          Data.Gaussian.Norm.Basic.normSq_neg]
  apply estimate.trans
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (PreparedPrimitivePaths.block_movement_le sample.integration.block member)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (Fraction.Order.Arithmetic.mul_nonneg_direct data.comparison.bounds.factor.base.numeratorUpper_nonnegative
        data.comparison.bounds.reciprocal.inverseUpper_positive.le))
  exact scaled.trans_eq (by simp only [Geometric.Basic.quarterRadius_eq_mul_pow,
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope,
    PreparedPrimitiveRequests.movement]; ring1)

/-- Evaluate the signed original cap comparison polynomial between the actual retained child endpoints. -/
@[expose] public def polynomialIncrement (sample : PreparedPrimitives.Sample request capSample) (child :
  PathCover.Parent curve differential) : Gaussian :=
  -(sample.retained.retained.comparison.value.eval (child.edge.point 1) -
    sample.retained.retained.comparison.value.eval (child.edge.point 0))

/-- The cap polynomial and local primitive increments differ by the retained geometric error times the child's squared
width. -/
private theorem polynomial_child_error (sample : PreparedPrimitives.Sample request capSample) {child : PathCover.Parent
  curve differential}
    (member : child ∈ sample.integration.block.children) :
    Data.Gaussian.Norm.Basic.normSq
      ((polynomialIncrement
      sample) child -
      (sample.integration.model.primitive.value.eval (child.edge.point 1) -
        sample.integration.model.primitive.value.eval (child.edge.point 0))) ≤
        Geometric.Basic.quarterRadius (Geometric.Basic.quarterRadius data.segment.comparison.scale index)
          sample.integration.block.depth := by
  have contained :=
    (child_inside sample)
    member
  let segment := Segment.build data.comparison.bounds (child.edge.point 0) (child.edge.point 1)
    (data.terminal.neighborhood.patch.box_refines.contains contained.1.1)
    (data.terminal.neighborhood.patch.box_refines.contains contained.1.2) contained.2.1 contained.2.2
  have estimate := segment.comparison_le sample.retained.retained.comparison
    sample.retained.retained.primitive.primitive sample.retained.retained.coefficient_eq
  rw
    [polynomialIncrement,
    sample.sign, sample.sign, show
    -(sample.retained.retained.comparison.value.eval (child.edge.point 1) -
      sample.retained.retained.comparison.value.eval (child.edge.point 0)) -
      (-sample.retained.retained.primitive.primitive.value.eval (child.edge.point 1) -
        -sample.retained.retained.primitive.primitive.value.eval (child.edge.point 0)) =
    -((sample.retained.retained.comparison.value.eval (child.edge.point 1) -
      sample.retained.retained.comparison.value.eval (child.edge.point 0)) -
      (sample.retained.retained.primitive.primitive.value.eval (child.edge.point 1) -
        sample.retained.retained.primitive.primitive.value.eval (child.edge.point 0))) by ring1,
    Data.Gaussian.Norm.Basic.normSq_neg]
  apply estimate.trans
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (PreparedPrimitivePaths.block_movement_le sample.integration.block member)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (Geometric.Basic.quarterRadius_nonneg data.comparison.bounds.scale_nonnegative index))
  have direction : Data.Gaussian.Norm.Basic.normSq data.segment.comparison.direction =
    PreparedPrimitiveRequests.movement parent := by
    rw [data.segment.comparison.direction_eq, data.first_eq, data.last_eq,
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.movement_eq]
  have equal : Geometric.Basic.quarterRadius segment.scale index =
      (2 * Geometric.Basic.quarterRadius data.comparison.bounds.scale index) * child.edge.pointMovement := by
    simp only [segment, Segment.build, Geometric.Basic.quarterRadius_eq_mul_pow,
      PreparedConstantModels.PreparedEdge.pointMovement]
    ring1
  rw [equal]
  exact scaled.trans_eq (by
    rw [data.segment.comparison.scale_eq, direction]
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow, PreparedPrimitiveRequests.movement]
    ring1)

/-- Pair the cap polynomial with the actual integrator cell by cell. -/
@[expose] public def areaPairs (sample : PreparedPrimitives.Sample request capSample) : List
  (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) :=
  sample.integration.block.children.map fun child =>
    ((polynomialIncrement
    sample) child, child.model.integralSample)

/-- Combine the cap comparison error and the original integration error into the common child-area discrepancy scale. -/
@[expose] public def areaError (sample : PreparedPrimitives.Sample request capSample) : Coordinate :=
  2 * (Geometric.Basic.quarterRadius data.segment.comparison.scale index + (LocalRequest.areaComparisonError
    (localRequest
    sample)))

/-- The retained cap comparison and integration error scales give a nonnegative area error. -/
theorem areaError_nonnegative (sample : PreparedPrimitives.Sample request capSample) : 0 ≤
  (areaError sample) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Geometric.Basic.quarterRadius_nonneg data.segment.comparison.scale_nonnegative index)
      (LocalRequest.areaComparisonError_nonnegative
      (localRequest
      sample)))

/-- Every original child pair satisfies the common discrepancy scale at its retained dyadic depth. -/
theorem areaPairs_errors (sample : PreparedPrimitives.Sample request capSample) : ∀ pair ∈
  (areaPairs sample),
    Data.Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ Geometric.Basic.quarterRadius
      (areaError sample)
      sample.integration.block.depth := by
  intro pair member
  obtain ⟨child, inChildren, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  have operational := (LocalRequest.areaPairs_errors
    (localRequest
    sample)) _ (Map.mem_map.mpr ⟨child, inChildren, rfl⟩)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at operational
  change Data.Gaussian.Norm.Basic.normSq (_ - _) ≤ Geometric.Basic.quarterRadius
    (LocalRequest.areaComparisonError
    (localRequest
    sample)) sample.integration.block.depth at operational
  let increment := sample.integration.model.primitive.value.eval (child.edge.point 1) -
    sample.integration.model.primitive.value.eval (child.edge.point 0)
  change Data.Gaussian.Norm.Basic.normSq
    ((polynomialIncrement
    sample) child - child.model.integralSample) ≤ _
  rw [show
    (polynomialIncrement
    sample) child - child.model.integralSample =
    ((polynomialIncrement
      sample) child - increment) + (increment - child.model.integralSample) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add
      ((polynomial_child_error
      sample) inChildren) operational) (by decide)).trans_eq (by
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow,
        areaError];
        ring1))

/-- Each retained child's actual integration sample satisfies the parent slope and operational error bound. -/
theorem areaPairs_integral_bound (sample : PreparedPrimitives.Sample request capSample) : ∀ pair ∈
  (areaPairs sample),
    Data.Gaussian.Norm.Basic.normSq pair.2 ≤ Geometric.Basic.quarterRadius (2 *
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data +
      (LocalRequest.areaComparisonError
      (localRequest
      sample)))) sample.integration.block.depth := by
  intro pair member
  obtain ⟨child, inChildren, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  have operational := (LocalRequest.areaPairs_errors
    (localRequest
    sample)) _ (Map.mem_map.mpr ⟨child, inChildren, rfl⟩)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at operational
  change Data.Gaussian.Norm.Basic.normSq (_ - _) ≤ Geometric.Basic.quarterRadius
    (LocalRequest.areaComparisonError
    (localRequest
    sample)) sample.integration.block.depth at operational
  let increment := sample.integration.model.primitive.value.eval (child.edge.point 1) -
    sample.integration.model.primitive.value.eval (child.edge.point 0)
  change Data.Gaussian.Norm.Basic.normSq child.model.integralSample ≤ _
  rw [show child.model.integralSample = increment - (increment - child.model.integralSample) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add
      ((primitive_child_bound
      sample) inChildren) operational) (by decide)).trans_eq (by
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow]; ring1))

/-- Bound the full paired child-path area discrepancy using the retained common error and slope, with all child counts
cancelled. -/
theorem area_error (sample : PreparedPrimitives.Sample request capSample) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea
      ((areaPairs
      sample).map Prod.fst) - IncrementArea.pathArea
      ((areaPairs
      sample).map Prod.snd)) ≤
      32 * (areaError
        sample) * (2 *
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data +
        (LocalRequest.areaComparisonError
        (localRequest
        sample))) +
        (areaError
        sample)) := by
  have scalar := PathArea.dyadic_comparison_bound
    (areaPairs sample)
    sample.integration.block.depth
    (error := areaError
      sample)
    (bound := 2 * (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope
      data + LocalRequest.areaComparisonError
      (localRequest
      sample)))
    ((Purelib.Data.List.Map.length_map ..).trans sample.integration.block.childCount)
      (areaError_nonnegative
      sample)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope_nonnegative
        data) (LocalRequest.areaComparisonError_nonnegative
        (localRequest
        sample))))
    (fun pair member => by
      have certificate :=
        areaPairs_errors
        sample pair member
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at certificate
      exact certificate) (fun pair member => by
      have certificate :=
        areaPairs_integral_bound
        sample pair member
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at certificate
      exact certificate)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

/-- A quarter of a positive rational budget is strictly below that budget. -/
private theorem quarter_lt {value : InverseRootPolynomial.Coordinate} (positive : 0 < value) : value / 4 < value := by
  apply (Fraction.Order.Field.div_lt_iff_pos (by decide)).mpr
  simpa only [Fraction.Field.mul_one_direct] using
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive (by
        decide : (1 : InverseRootPolynomial.Coordinate) < 4)

/-- Every later common stage pays the retained cap polynomial comparison target. -/
private theorem comparison_error_lt (_sample : PreparedPrimitives.Sample request capSample) (later : request.index ≤
  index) :
    Geometric.Basic.quarterRadius data.segment.comparison.scale index < target := by
  have retainedLater : request.capRequest.index ≤ index := (Purelib.Data.Nat.Order.le_max_left _ _).trans
    (request.index_eq ▸ later)
  have interiorLater : request.capRequest.interior.index ≤ index :=
    (Purelib.Data.Nat.Order.le_max_right _ _).trans (request.capRequest.index_eq ▸ retainedLater)
  have estimate := (quarterRadius_antitone data.segment.comparison.scale_nonnegative interiorLater).trans_lt
    (request.capRequest.interior.error_eq ▸ request.capRequest.interior.error_lt)
  have first : request.capRequest.budget < request.budget := by
    rw [request.capRequest.budget_eq]
    exact quarter_lt
      request.budget_positive
  have second : request.budget < target := by
    rw [request.budget_eq];
    exact quarter_lt
      request.positive
  exact estimate.trans (first.trans second)

/-- The retained integration request pays its original operational error target. -/
private theorem operational_error_lt (sample : PreparedPrimitives.Sample request capSample) :
  (LocalRequest.areaComparisonError
  (localRequest sample))
  < target :=
  (LocalRequest.areaComparisonError_lt
    (localRequest sample)
    request.budget_positive).trans (by
    rw [request.budget_eq]; exact
      quarter_lt
      request.positive)

/-- At every later shared stage the combined child-area error is less than four times the original target. -/
theorem areaError_lt (sample : PreparedPrimitives.Sample request capSample) (later : request.index ≤ index) :
  (areaError sample) < 4
  * target :=
  (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_direct
      ((comparison_error_lt
      sample) later)
      (operational_error_lt
      sample))).trans_eq (by ring1)

/-- The preflight target controls the full actual area, independently of every child depth and polynomial degree. -/
theorem area_error_lt (sample : PreparedPrimitives.Sample request capSample) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea
      ((areaPairs
      sample).map Prod.fst) - IncrementArea.pathArea
      ((areaPairs
      sample).map Prod.snd)) <
      256 * target * (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope
        data + 3 * target) := by
  have errorLt :=
    (areaError_lt sample)
    later
  have totalLe : 2 * (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope
    data + (LocalRequest.areaComparisonError
    (localRequest
    sample))) +
    (areaError sample) ≤
      2 * Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data + 6 *
        target :=
    (add_le_add (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl
        (operational_error_lt
        sample).le) (by decide)) errorLt.le).trans_eq (by ring1)
  have factorPositive : 0 < 32 * (2 *
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data + 6 * target)
    :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide)
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope_nonnegative
        data))
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) request.positive))
  apply (area_error
    sample).trans_lt
  calc
    _ ≤ 32 * (areaError
      sample) * (2 * Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope
      data + 6 * target) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalLe
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
          (areaError_nonnegative
          sample))
    _ = (32 * (2 * Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope
      data + 6 * target)) *
      (areaError sample)
      := by
      ring1
    _ < (32 * (2 * Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope
      data + 6 * target)) * (4 * target) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct factorPositive errorLt
    _ = _ := by ring1

/-- A dyadic list of increments with matching quarter-radius bounds has a total bounded by the original scale. -/
private theorem dyadic_sum_bound (values : List InverseRootPolynomial.Gaussian) (depth : Nat) (count : values.length = 2
  ^ depth)
    (bound : InverseRootPolynomial.Coordinate) (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq
      value ≤ Geometric.Basic.quarterRadius bound depth) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values) ≤ bound := by
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le values (Geometric.Basic.quarterRadius bound depth)
    bounded
  rw [count, DyadicCount.dyadic_count_cancel] at estimate
  exact estimate

/-- The finite sum of paired differences equals the difference of the two original component sums. -/
private theorem sum_differences (pairs : List (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => pair.1 - pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.fst) - Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (pairs.map Prod.snd) := by
  induction pairs with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons pair pairs previous =>
    simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, previous]; ring1

/-- These four bounds control concatenation: internal areas, total errors, and both polygons of parent totals. Every
child count has already cancelled. -/
theorem area_bounds (sample : PreparedPrimitives.Sample request capSample) (later : request.index ≤ index) :
    let left :=
      (areaPairs
      sample).map Prod.fst
    let right :=
      (areaPairs
      sample).map Prod.snd
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea left - IncrementArea.pathArea right) ≤ 256 * target
      * (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data + 3 *
      target) ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum left -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum right) ≤ 4 * target ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum left) ≤ 4 *
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data + 3 *
      target) ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum right) ≤ 4 *
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data + 3 *
      target) := by
  have count : (areaPairs
    sample).length = 2 ^ sample.integration.block.depth :=
    (Purelib.Data.List.Map.length_map ..).trans sample.integration.block.childCount
  have errors :=
    dyadic_sum_bound
    ((areaPairs
    sample).map (fun pair => pair.1 - pair.2)) sample.integration.block.depth
    ((Purelib.Data.List.Map.length_map ..).trans count)
      (areaError sample)
      (by
      intro value member
      obtain ⟨pair, inPairs, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact
        (areaPairs_errors
        sample) pair inPairs)
  rw [sum_differences] at errors
  have rightBound :=
    dyadic_sum_bound
    ((areaPairs
    sample).map Prod.snd) sample.integration.block.depth
    ((Purelib.Data.List.Map.length_map ..).trans count) (2 *
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data +
      (LocalRequest.areaComparisonError
      (localRequest
      sample)))) (by
      intro value member
      obtain ⟨pair, inPairs, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact
        (areaPairs_integral_bound
        sample) pair inPairs)
  have rightLe : Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
    ((areaPairs
    sample).map Prod.snd)) ≤ 2 *
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data + target) :=
    rightBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl
        (operational_error_lt
        sample).le) (by decide))
  have errorLe := errors.trans
    ((areaError_lt
    sample) later).le
  refine ⟨((area_error_lt
    sample) later).le, errorLe, ?_, ?_⟩
  · have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        ((areaPairs
        sample).map Prod.fst) - Data.Gaussian.Norm.Sum.Basic.gaussianSum
        ((areaPairs
        sample).map Prod.snd))
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        ((areaPairs
        sample).map Prod.snd))
    rw [sub_add_cancel] at estimate
    exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add errorLe rightLe) (by
      decide)).trans_eq (by ring1))
  · exact rightLe.trans ((Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope_nonnegative
        data))
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 10)
          request.positive.le))).trans_eq (by ring1))

/-- Every retained child's cap polynomial increment satisfies the same finite parent slope bound. -/
theorem polynomial_child_bound (sample : PreparedPrimitives.Sample request capSample) (later : request.index ≤ index)
    {child : PathCover.Parent curve differential} (member : child ∈ sample.integration.block.children) :
    Data.Gaussian.Norm.Basic.normSq
      ((polynomialIncrement
      sample) child) ≤ 4 *
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data + 3 *
      target) := by
  have inPairs :
    ((polynomialIncrement
    sample) child, child.model.integralSample) ∈
    (areaPairs sample) :=
    Map.mem_map.mpr ⟨child, member, rfl⟩
  have error :=
    ((areaPairs_errors
    sample) _ inPairs).trans
    ((Geometric.Basic.quarterRadius_le_scale
      (areaError_nonnegative
      sample) _).trans
      ((areaError_lt
      sample) later).le)
  have integral :=
    ((areaPairs_integral_bound
    sample) _ inPairs).trans
    ((Geometric.Basic.quarterRadius_le_scale
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        (add_nonneg
          (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope_nonnegative
          data) (LocalRequest.areaComparisonError_nonnegative
          (localRequest
          sample)))) _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl
          (operational_error_lt
          sample).le) (by decide)))
  have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two
    ((polynomialIncrement
    sample) child - child.model.integralSample) child.model.integralSample
  rw [sub_add_cancel] at estimate
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add error integral) (by
    decide)).trans_eq (by ring1))

/-- The right components of the retained pairs are exactly the original integrator path increments. -/
theorem areaPairs_integral (sample : PreparedPrimitives.Sample request capSample) :
    (areaPairs
      sample).map Prod.snd = PathArea.increments
      (PathModel.mk (sample.integration.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model)) := by
  rewrite [areaPairs,
    Purelib.Data.List.Map.map_map, PathArea.increments]
  rewrite [Purelib.Data.List.Map.map_map]
  dsimp only [Function.comp_def]

/-- Differences of one value function telescope over the original retained child chain. -/
private theorem child_increment_sum (block : PreparedDirectDyadicRefinements.DirectParentBlock parent) (value :
  InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (block.children.map (fun child => value (child.edge.point 1) - value
      (child.edge.point 0))) =
      value (parent.edge.point 1) - value (parent.edge.point 0) := by
  have sumEq (children : List (PathCover.Parent curve differential)) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (children.map (fun child => value (child.edge.point 1) - value
        (child.edge.point 0))) =
        Primitive.incrementSum value (children.map PreparedSubdivisionModelCore.CenteredEdge.model) := by
    induction children with
    | nil => rfl
    | cons child children previous =>
      exact congrArg (fun tail => value (child.edge.point 1) - value (child.edge.point 0) + tail) previous
  have telescope := (sumEq block.children).trans (PreparedPrimitivePaths.incrementSum_eq value block.chain)
  rw [← parent.edge.point_one, ← parent.edge.point_zero] at telescope
  exact telescope

/-- The retained cap polynomial child increments telescope to the original whole-parent polynomial increment. -/
theorem areaPairs_polynomial_total (sample : PreparedPrimitives.Sample request capSample) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((areaPairs
      sample).map Prod.fst) =
      (polynomialIncrement
      sample) parent := by
  let value := fun point => -sample.retained.retained.comparison.value.eval point
  have rows : (areaPairs
    sample).map Prod.fst = sample.integration.block.children.map
      (fun child => value (child.edge.point 1) - value (child.edge.point 0)) := by
    rewrite [areaPairs,
      Purelib.Data.List.Map.map_map]
    dsimp only [Function.comp_def]
    apply Map.map_congr_left
    intro child _
    dsimp only
      [polynomialIncrement,
      value]
    ring1
  rw [rows,
    child_increment_sum]
  dsimp only [value,
    polynomialIncrement]
  ring1

end Sample

set_option genInjectivity false in
/-- Choose the integration tolerance from the requested full area error. The fixed slope is retained before selecting or
building a model stage. -/
structure AreaRequest (data : PathCover.ParentData cap differential count parent) (target :
  InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original full-area error target is strictly positive. -/ positive : 0 < target
  /-- The cached original cap coefficient and parent-movement ceiling. -/ slope : InverseRootPolynomial.Coordinate
  /-- The cached slope equals the original retained parent area slope. -/ slope_eq : slope =
    areaSlope data
  /-- The positive local integration tolerance selected before model refinement. -/ tolerance :
    InverseRootPolynomial.Coordinate
  /-- The tolerance is the smaller of one and the original target divided by its slope-adjusted cost. -/ tolerance_eq :
    tolerance = min 1 (target / (512 * (slope + 3)))
  /-- The original parent primitive request paid at this exact retained tolerance. -/ request :
    PreparedPrimitives.Request data tolerance floor

constructive_injectivity AreaRequest

namespace AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.Sample

/-- Pay the full requested area target by retaining its original slope, positive tolerance and proper-parent primitive
request. -/
@[expose] public def build (data : PathCover.ParentData cap differential count parent) (target :
  InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.AreaRequest data target
      floor :=
  let slope := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data
  let tolerance := min 1 (target / (512 * (slope + 3)))
  have tolerancePositive : 0 < tolerance := Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct positive
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel)
        (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
          (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope_nonnegative
          data) (by decide))))
  ⟨positive, slope, rfl, tolerance, rfl, PreparedPrimitives.Request.build data tolerance tolerancePositive floor proper⟩

variable {target : Coordinate} {floor : Nat}

/-- The retained integration tolerance pays the complete original area discrepancy target. -/
theorem paid (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.AreaRequest data target floor)
  :
    256 * request.tolerance *
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data + 3 *
      request.tolerance) < target := by
  have nonnegative : 0 ≤ request.slope := request.slope_eq ▸
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope_nonnegative data
  have shifted : 0 < request.slope + 3 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by
    decide)
  have denominator : 0 < 512 * (request.slope + 3) := Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel)
    shifted
  have small : request.tolerance ≤ 1 := by rw [request.tolerance_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have selected : request.tolerance ≤ target / (512 * (request.slope + 3)) := by
    rw [request.tolerance_eq]; exact Fraction.Order.Basic.min_le_right _ _
  have factor : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.areaSlope data +
    3 * request.tolerance ≤ request.slope + 3 := by
    rw [← request.slope_eq]
    simpa only [Fraction.Field.mul_one_direct] using
      add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 3))
  calc
    _ ≤ 256 * request.tolerance * (request.slope + 3) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factor
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) request.request.positive.le)
    _ = (256 * (request.slope + 3)) * request.tolerance := by ring1
    _ < (512 * (request.slope + 3)) * request.tolerance :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by
            decide +kernel : (256 : InverseRootPolynomial.Coordinate) < 512) shifted)
        request.request.positive
    _ ≤ (512 * (request.slope + 3)) * (target / (512 * (request.slope + 3))) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct selected denominator.le
    _ = target := by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ denominator.ne'

set_option genInjectivity false in
/-- Cache both literal paths and their finite total/area summaries. -/
structure Evaluation (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.AreaRequest data target floor)
  {index : Nat} {box : Rational.Box}
    (capSample : Primitives.Sample cap differential index box) where
  /-- The evaluated original primitive request and its retained integration block. -/ sample : PreparedPrimitives.Sample
    request.request capSample
  /-- The cached ordered cap-polynomial and integrator increments on the original children. -/ pairs : List
    (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)
  /-- The cached pairs are exactly the evaluated sample's original child pairs. -/ pairs_eq : pairs =
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.Sample.areaPairs sample)
  /-- The cached finite total and area summary of the cap polynomial increments. -/ left : IncrementArea.Summary
    (pairs.map Prod.fst)
  /-- The cached finite total and area summary of the actual integration increments. -/ right : IncrementArea.Summary
    (pairs.map Prod.snd)
  /-- The cached cap total equals the original whole-parent polynomial increment. -/ left_total : left.total =
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.Sample.polynomialIncrement
    sample) parent
  /-- The cached integration total equals the retained original integration sample. -/ right_total : right.total =
    sample.integral
  /-- The cached right path is exactly the path of the original integration children. -/ right_path : pairs.map Prod.snd
    = PathArea.increments
    (PathModel.mk (sample.integration.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model))
  /-- The cached two path areas differ by less than the original full-area target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (left.area - right.area) < target

constructive_injectivity Evaluation

/-- Evaluate the retained area request once and cache both exact child paths, totals, areas and the requested
discrepancy certificate. -/
@[expose] public def evaluate (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.AreaRequest data target floor)
  {index : Nat} {box : Rational.Box}
    (capSample : Primitives.Sample cap differential index box) (later : request.request.index ≤ index) :
      Evaluation
      request capSample :=
  let sample := PreparedPrimitives.Sample.build request.request capSample later
  let pairs := (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.Sample.areaPairs
    sample)
  let left := IncrementArea.Summary.build (pairs.map Prod.fst)
  let right := IncrementArea.Summary.build (pairs.map Prod.snd)
  ⟨sample, pairs, rfl, left, right, left.total_eq.trans
    (Sample.areaPairs_polynomial_total
    sample),
    (by rw [right.total_eq,
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.Sample.areaPairs_integral
      sample), PathArea.increments_sum, sample.integral_eq]),
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.Sample.areaPairs_integral
      sample), (by
      rw [left.area_eq, right.area_eq]
      exact
        ((Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.Sample.area_error_lt
        sample) later).trans request.paid)⟩

end AreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.Data

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Rational
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Integration.Polynomial.Gaussian.Path.Basic
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
open Purelib.Polynomial.Geometry
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPrimitivePathArea
open Purelib.Riemann.Readings
open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Data Parent)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

/-- Each indexed parent in an all-proper retained list has a strictly ordered original parameter interval. -/
private theorem proper_get : {parents : List (PathCover.Parent curve differential)} →
    PreparedDyadicRefinements.AllParentsProper parents → (position : Fin parents.length) →
    (parents[position]).edge.left.parameter < (parents[position]).edge.request.endpoint.parameter
  | [], _, position => Fin.elim0 position
  | _ :: _, proper, ⟨0, _⟩ => proper.1
  | _ :: _, proper, ⟨position + 1, inside⟩ =>
    proper_get proper.2 ⟨position,
    Nat.lt_of_succ_lt_succ inside⟩

/-- Every retained occurrence supplies the nondegeneracy premise for its actual area request, directly from the complete
path cache. -/
theorem parent_proper {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {first last : InverseRootPolynomial.Gaussian} {path : Polynomial.Geometry.ClearPath
      (HyperellipticReciprocal.polynomial curve)
      collar.box first last}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval first)}
    (data : PathCover.Data cap path owner differential) (position : Fin data.cache.parents.length) :
    (data.cache.parents[position]).edge.left.parameter < (data.cache.parents[position]).edge.request.endpoint.parameter
      :=
  proper_get data.cache.proper position

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.Data
