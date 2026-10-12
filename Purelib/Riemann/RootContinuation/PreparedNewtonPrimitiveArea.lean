module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandBank
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Paths.PathArea
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveComparison
public import Purelib.Riemann.Readings.PreparedPrimitiveSideArea
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Vanishing area of the retained Newton-boundary polynomial bank

The area comparison uses the actual resampled children, whose prepared
integral area is already controlled. The resampling certificate retains the
whole original polynomial bank, not just an equal endpoint sum.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveArea

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained area bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the original area summaries. -/
private abbrev Gaussian := Basic.Canonical

open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandBank (RefinedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveComparison (PrimitiveSample)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (PrimitiveSumRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples.Sample
  (preparedDensity preparedDensity_nonnegative preparedDensity_movement_le)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Integration.Path.IncrementArea (Summary pathArea)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target accuracy : Purelib.Data.Rat.Fraction.Rational} {band : PreparedBandRequest fixed target}

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Every original refined boundary child satisfies its retained prepared-density bound.

The child's actual starting point and certified model error determine the same original integral sample and movement
factor. -/
theorem RefinedBoundaryParents.child_density_bound {parents : List (CenteredEdge curve differential)}
    (bank : RefinedBoundaryParents band parents) :
    ∀ child ∈ bank.blocks.children,
      Data.Gaussian.Norm.Basic.normSq child.model.integralSample ≤ PreparedNewtonBandSamples.Sample.preparedDensity
        band.sample fixed band.error * child.edge.pointMovement := by
  induction bank with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      intro child member
      rcases Purelib.Data.List.Membership.mem_append.mp member with member | member
      · rw [Norm.Basic.normSq_eq_canonical]
        exact PreparedNewtonBandSamples.Sample.prepared_integral_bound band.sample fixed child
          (head.boundary.child_starts head.refinement.block child member)
          (head.refinement.child_error member) band.error_accurate
      · exact ih child member

namespace PrimitiveSample

variable {parents : List (CenteredEdge curve differential)} {primitive : PrimitiveSumRequest parents count accuracy}

open Purelib.Integration.Path in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
set_option genInjectivity false in
/-- Cached original primitive and prepared-increment area summaries with exact total readbacks.

Both summaries are indexed by the actual ordered increment lists, retaining the original primitive request sum and
prepared integral sample. -/
structure AreaSample (result : PrimitiveSample band primitive) where
  /-- The cached summary of the original flattened primitive source increments. -/ source : IncrementArea.Summary
    ((PreparedPrimitiveSideArea.areaBlocks result.sample.requests).map Prod.fst).flatten
  /-- The cached summary of the original prepared child-model increments. -/ prepared : IncrementArea.Summary
    (PathArea.increments (Basic.PathModel.mk (result.sample.blocks.children.map CenteredEdge.model)))
  /-- The source summary total is exactly the retained original primitive sum. -/ source_total : source.total =
    primitive.primitiveSum
  /-- The prepared summary total is exactly the original integral sample. -/ prepared_total : prepared.total =
    result.sample.integralSample

constructive_injectivity AreaSample

open Purelib.Integration.Path in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
/-- Cache the original source and prepared increment summaries with their exact totals.

The source uses the retained primitive area blocks, while the prepared summary uses the original child models in their
stored order. -/
@[expose] def areaSample (result : PrimitiveSample band primitive) : AreaSample result := by
  let source := IncrementArea.Summary.build ((PreparedPrimitiveSideArea.areaBlocks result.sample.requests).map
    Prod.fst).flatten
  let prepared := PathArea.sample (Basic.PathModel.mk (result.sample.blocks.children.map CenteredEdge.model))
  refine ⟨source, prepared, ?_, ?_⟩
  · rw [source.total_eq, PreparedPrimitiveSideArea.areaBlocks_left_total result.sample.requests, ←
      result.sample.increments_eq,
      ← result.sample.primitiveSum_eq, result.sum_eq]
  · exact (PathArea.sample_total _).trans result.sample.integralSample_eq.symm

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings
open Purelib.Riemann.RootContinuation
/-- Bound the area difference of the original primitive and prepared paths at a retained dyadic depth.

The exact parent count and quarter-radius movement bounds give 128 times accuracy times prepared density times distance
plus accuracy. -/
theorem area_comparison_bound (result : PrimitiveSample band primitive) (distance : Fraction.Rational) (depth : Nat)
    (distanceNonnegative : 0 ≤ distance) (countEq : parents.length = 2 ^ depth)
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ Geometric.Basic.quarterRadius distance
      depth) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea ((PreparedPrimitiveSideArea.areaBlocks
      result.sample.requests).map Prod.fst).flatten -
      IncrementArea.pathArea (PathArea.increments (Basic.PathModel.mk (result.sample.blocks.children.map
        CenteredEdge.model)))) ≤
        128 * accuracy * (PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed band.error * distance +
          accuracy) := by
  rw [result.sample.blocks_eq]
  have targetLe : result.sample.localTarget ≤ accuracy := by
    rw [result.sample.localTarget_eq]
    exact Budget.Aggregate.perTerm_le result.sample.target_positive.le _
  have countPaid : (parents.length : Fraction.Rational) ^ 2 * result.sample.localTarget ≤ accuracy := by
    rw [result.sample.localTarget_eq]
    simpa only [pow_two, Fraction.Field.mul_assoc, -eq_self, -iff_self] using
      (Budget.Aggregate.count_mul_perTerm_lt result.sample.target_positive parents.length).le
  rw [Norm.Basic.normSq_eq_canonical]
  apply PreparedPrimitiveSideArea.dyadic_area_error result.sample.requests result.sample.localTarget_positive
    result.sample.target_positive
    (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative band.sample fixed band.errorPositive.le)
      distanceNonnegative depth countEq targetLe countPaid movements
  intro child member
  rw [← Norm.Basic.normSq_eq_canonical]
  apply PreparedNewtonPrimitiveArea.RefinedBoundaryParents.child_density_bound result.boundary child
  rw [result.blocks_eq, result.sample.blocks_eq]
  exact member

/-- Bound the original primitive path area using its paid density and retained movement radius.

The same dyadic parent count and movement bounds yield 256 times accuracy times accuracy plus target, plus 32 times
target squared. -/
theorem primitive_area_bound (result : PrimitiveSample band primitive) (distance : Fraction.Rational) (depth : Nat)
    (distanceNonnegative : 0 ≤ distance) (countEq : parents.length = 2 ^ depth)
    (movementLe : distance ≤ 32 * band.sample.output.radius ^ 2)
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ Geometric.Basic.quarterRadius distance
      depth) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea ((PreparedPrimitiveSideArea.areaBlocks
      result.sample.requests).map Prod.fst).flatten) ≤
      256 * accuracy * (accuracy + target) + 32 * target ^ 2 := by
  have densityNonnegative := PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative band.sample fixed
    band.errorPositive.le
  have densityPaid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movementLe densityNonnegative).trans
    ((PreparedNewtonBandSamples.Sample.preparedDensity_movement_le band.sample fixed band.error_le_one
      band.radius_le_one).trans band.paid)
  have comparison := (PreparedNewtonPrimitiveArea.PrimitiveSample.area_comparison_bound result distance depth
    distanceNonnegative countEq movements).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add densityPaid le_rfl)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) result.sample.target_positive.le))
  have prepared := (result.area_density_bound distance depth distanceNonnegative countEq movements).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.pow_le_pow_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative distanceNonnegative) densityPaid 2) (by decide))
  have estimate := Norm.Bounds.normSq_add_le_two
    (IncrementArea.pathArea ((PreparedPrimitiveSideArea.areaBlocks result.sample.requests).map Prod.fst).flatten -
      IncrementArea.pathArea (PathArea.increments (Basic.PathModel.mk (result.sample.blocks.children.map
        CenteredEdge.model))))
    (IncrementArea.pathArea (PathArea.increments (Basic.PathModel.mk (result.sample.blocks.children.map
      CenteredEdge.model))))
  rw [sub_add_cancel] at estimate
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add comparison prepared) (by decide)).trans_eq (by ring1))

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- The cached original source area satisfies the retained primitive-area payment. -/
theorem AreaSample.paid {result : PrimitiveSample band primitive} (sample : AreaSample result) (distance :
  Fraction.Rational) (depth : Nat)
    (distanceNonnegative : 0 ≤ distance) (countEq : parents.length = 2 ^ depth)
    (movementLe : distance ≤ 32 * band.sample.output.radius ^ 2)
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ Geometric.Basic.quarterRadius distance
      depth) :
    Data.Gaussian.Norm.Basic.normSq sample.source.area ≤ 256 * accuracy * (accuracy + target) + 32 * target ^ 2 := by
  rw [sample.source.area_eq]
  exact PreparedNewtonPrimitiveArea.PrimitiveSample.primitive_area_bound result distance depth distanceNonnegative
    countEq movementLe movements

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
/-- The original anchored trace area splits into its cached source area and endpoint ribbon. -/
theorem AreaSample.trace_eq {result : PrimitiveSample band primitive} (sample : AreaSample result) (anchor :
  Basic.Canonical) :
    IncrementArea.traceArea anchor ((PreparedPrimitiveSideArea.areaBlocks result.sample.requests).map Prod.fst).flatten
      =
      sample.source.area + BoundaryRibbon.area anchor sample.source.total := by
  rw [IncrementArea.traceArea_eq, ← sample.source.area_eq, ← sample.source.total_eq]

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
/-- Bound the original anchored trace area with separate area and endpoint payments.

The retained dyadic count and movement bounds give the original 512/64 area factors and the anchor-norm endpoint term
with factor 16. -/
theorem AreaSample.trace_bound {result : PrimitiveSample band primitive} (sample : AreaSample result) (anchor :
  Basic.Canonical)
    (distance : Fraction.Rational) (depth : Nat) (distanceNonnegative : 0 ≤ distance) (countEq : parents.length = 2 ^
      depth)
    (movementLe : distance ≤ 32 * band.sample.output.radius ^ 2)
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ Geometric.Basic.quarterRadius distance
      depth) :
    Data.Gaussian.Norm.Basic.normSq (sample.source.area + BoundaryRibbon.area anchor sample.source.total) ≤
      512 * accuracy * (accuracy + target) + 64 * target ^ 2 + 16 * Data.Gaussian.Norm.Basic.normSq anchor * (accuracy +
        target) := by
  have totalBound : Data.Gaussian.Norm.Basic.normSq sample.source.total ≤ 2 * (accuracy + target) := by
    rw [sample.source_total]
    exact result.primitive_bound distance depth countEq movementLe movements
  have endpoint := (BoundaryRibbon.area_bound anchor sample.source.total).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalBound
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg anchor)))
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (sample.paid distance depth distanceNonnegative countEq movementLe movements) endpoint) (by
        decide)).trans_eq (by ring1))

end PrimitiveSample
end Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveArea
