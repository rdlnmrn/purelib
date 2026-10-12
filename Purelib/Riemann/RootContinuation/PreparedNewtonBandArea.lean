module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandRefinement
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSides
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandBank
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
public import Purelib.Riemann.Paths.PathArea
import Purelib.Tactic.Ring

public section

/-!
# Full primitive area of actual prepared Newton boundaries

Both refinement counts are paid before the four sides are assembled. The
result controls the complete cumulative path of actual cell integral samples,
not merely the final sum. It requires no equality between independently
prepared roots and does not yet identify these primitive values with the
global punctured-grid primitive bank.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNewtonBandArea

open Purelib.RootIsolation.Newton.Band
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Riemann.Paths.PathArea (increments)
open Purelib.Integration.Path.IncrementArea (pathArea)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandBank (RefinedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandRefinement (RefinedBoundaryParent)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSides (RefinedBoundarySide)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
  (PreparedBoundaryTraversal RequestedPreparedBoundary)
open Purelib.Data in
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational
open Purelib.Geometry in
/-- The rational rectangular ambient-box type. -/
private abbrev Box := Rational.Box

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

namespace RefinedBoundaryParent

variable {request : PreparedBandRequest fixed target} {parent : CenteredEdge curve differential}

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Bound a refined parent's full child-integral path area by its density and movement.

The squared area is at most four times the square of their product, using the actual dyadic child list. -/
theorem area_density_bound (refined : RefinedBoundaryParent request parent) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (increments
      (Polynomial.Gaussian.Path.Basic.PathModel.mk (refined.refinement.block.children.map CenteredEdge.model)))) ≤
      4 * ((RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error) *
        Readings.PreparedPrimitiveRequests.movement parent) ^ 2 := by
  apply Paths.PathArea.dyadic_area_bound _ refined.refinement.block.depth
    (by
        simpa only [increments, Purelib.Data.List.Map.length_map, -eq_self, -iff_self]
          using refined.refinement.block.childCount)
    (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed
      request.errorPositive.le)
    (Readings.PreparedPrimitiveRequests.movement_nonnegative parent)
  intro value member
  obtain ⟨cell, inModels, rfl⟩ := List.Map.mem_map.mp member
  obtain ⟨child, inChildren, rfl⟩ := List.Map.mem_map.mp inModels
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (RootContinuation.PreparedNewtonBandSamples.Sample.prepared_integral_bound request.sample fixed child
    (refined.boundary.child_starts refined.refinement.block child inChildren)
    (refined.refinement.child_error inChildren) request.error_accurate).trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Paths.PreparedPrimitivePaths.block_movement_le refined.refinement.block inChildren)
        (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed
          request.errorPositive.le))

end RefinedBoundaryParent

namespace RefinedBoundaryParents

variable {request : PreparedBandRequest fixed target}

open Purelib.Integration in
open Purelib.Data in
/-- Read the actual child-integral lists grouped by their retained prepared parents. -/
@[expose] def incrementBlocks : {parents : List (CenteredEdge curve differential)} →
    RefinedBoundaryParents request parents → List (List Gaussian.Basic.Canonical)
  | _, .nil => []
  | _, .cons head tail =>
      increments (Polynomial.Gaussian.Path.Basic.PathModel.mk (head.refinement.block.children.map CenteredEdge.model))
        :: (incrementBlocks tail)

/-- There is exactly one retained increment block per original parent. -/
theorem incrementBlocks_length {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents request
  parents) :
    (incrementBlocks bank).length = parents.length := by
  induction bank with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

open Purelib.Riemann in
open Purelib.Integration in
/-- Flattening the retained increment blocks gives the actual combined child path increments. -/
theorem incrementBlocks_flatten {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents
  request parents) :
    (incrementBlocks bank).flatten = increments (Polynomial.Gaussian.Path.Basic.PathModel.mk (bank.blocks.children.map
      CenteredEdge.model)) := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
      simp only [incrementBlocks, List.flatten_cons, ih,
        RootContinuation.PreparedNewtonBandBank.RefinedBoundaryParents.blocks,
        DirectBlockRefinement.children,
        Purelib.Data.List.Map.map_append, increments, -eq_self, -iff_self]
      rfl

open Purelib.Riemann in
open Purelib.Data in
/-- The retained block totals are exactly the cached parent samples. -/
theorem incrementBlocks_totals {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents request
  parents) :
    (incrementBlocks bank).map Data.Gaussian.Norm.Sum.Basic.gaussianSum = bank.samples := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
      simp only [incrementBlocks, List.map_cons,
      Paths.PathArea.increments_sum,
      RootContinuation.PreparedNewtonBandBank.RefinedBoundaryParents.samples, ih, -eq_self, -iff_self]
      rfl

open Purelib.Riemann
open Purelib.Integration
open Purelib.Approximation
open Purelib.Data
/-- Every retained increment block satisfies the common dyadic movement area bound.

The hypothesis bounds each original parent's movement at the same depth and uses the retained request's density. -/
theorem incrementBlocks_areas {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents request
  parents)
    (movement : Rat.Fraction.Rational) (depth : Nat)
    (movements : ∀ parent ∈ parents, Readings.PreparedPrimitiveRequests.movement parent ≤
      Rational.Geometric.Basic.quarterRadius movement depth) :
    ∀ block ∈ (incrementBlocks bank),
      Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea block) ≤ 4 *
        ((RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error) *
        Rational.Geometric.Basic.quarterRadius movement depth) ^ 2 := by
  induction bank with
  | nil => intro block member; cases member
  | cons head tail ih =>
      intro block member
      rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
      · have densityNonnegative := RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative
          request.sample fixed request.errorPositive.le
        have productLe := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (movements _ (List.mem_cons_self ..)) densityNonnegative
        have squared := Rat.Fraction.Order.Arithmetic.pow_le_pow_direct
          (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative
            (Readings.PreparedPrimitiveRequests.movement_nonnegative _)) productLe 2
        exact (RootContinuation.PreparedNewtonBandArea.RefinedBoundaryParent.area_density_bound head).trans
          (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squared (by decide))
      · exact ih (fun other inTail => movements other (List.mem_cons_of_mem _ inTail)) block member

/-- Bound the complete grouped child path area using the dyadic parent movement budget.

With exactly two to the depth parents, the squared area is at most sixteen times the squared density-movement product.
-/
theorem area_density_bound {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents request
  parents)
    (movement : Rat.Fraction.Rational) (depth : Nat) (movementNonnegative : 0 ≤ movement) (count : parents.length = 2 ^
      depth)
    (movements : ∀ parent ∈ parents, Readings.PreparedPrimitiveRequests.movement parent ≤
      Rational.Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (increments
      (Polynomial.Gaussian.Path.Basic.PathModel.mk (bank.blocks.children.map CenteredEdge.model)))) ≤
      16 * ((RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error) *
        movement) ^ 2 := by
  rw [← incrementBlocks_flatten bank]
  apply Paths.PathArea.dyadic_blocks_area_bound _ depth
    ((incrementBlocks_length bank).trans count)
    (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed
      request.errorPositive.le) movementNonnegative
    (incrementBlocks_areas bank movement depth movements)
  intro block member
  have inSamples : Data.Gaussian.Norm.Sum.Basic.gaussianSum block ∈ bank.samples := by
    rw [← incrementBlocks_totals bank]
    exact List.Map.mem_map_of_mem member
  exact bank.samples_bounded movement depth movements _ inSamples

end RefinedBoundaryParents

namespace RefinedBoundarySide

open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (Owner)

variable {request : PreparedBandRequest fixed target} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment curve.polynomial request.sample.output.box start finish}
  {within : segment.WithinAmbient} {owner :
    Owner (curve.polynomial.eval start)} {sheet
    : Fin 2}

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Bound a retained side's full primitive path area by density and endpoint displacement.

The estimate uses its actual nested child model and the original dyadic parent grouping. -/
theorem area_density_bound (side : RefinedBoundarySide request segment within owner sheet) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (increments side.model)) ≤
      16 * ((RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error) *
        Data.Gaussian.Norm.Basic.normSq (finish - start)) ^ 2 := by
  rw [side.model_eq]
  exact RootContinuation.PreparedNewtonBandArea.RefinedBoundaryParents.area_density_bound side.refined
    (Data.Gaussian.Norm.Basic.normSq (finish - start)) side.covered.mesh.depth (Gaussian.Norm.Basic.normSq_nonneg _)
    (side.covered.parents_length.trans side.covered.mesh.edgeCount_eq)
    (by
      intro parent member
      rw [Gaussian.Norm.Basic.normSq_eq_canonical (finish - start)]
      exact (Paths.UniformPreparedBoundarySegments.CoveredSegment.parent_movement
        side.covered member).le)

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
open Purelib.Polynomial in
/-- The retained side request bounds squared primitive path area by sixteen times target squared. -/
theorem area_bound (side : RefinedBoundarySide request segment within owner sheet) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (increments side.model)) ≤ 16 * target ^ 2 := by
  have densityNonnegative := RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative
    request.sample fixed request.errorPositive.le
  have first : request.sample.output.box.Contains start := by
    simpa only [Geometry.ClearPath.ClearSegment.pointAt_zero, -eq_self, -iff_self] using segment.pointAt_contains within
      0 (by decide)
  have last : request.sample.output.box.Contains finish := by
    simpa only [Geometry.ClearPath.ClearSegment.pointAt_one, -eq_self, -iff_self] using segment.pointAt_contains within
      1 (by decide)
  have movementLe := (request.sample.output.box.normSq_sub_le_diagonalSq last first).trans
    (request.sample.output.band.diagonalSq_le request.sample.output.radiusPositive)
  have paid := (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movementLe densityNonnegative).trans
    ((RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_movement_le request.sample fixed
      request.error_le_one request.radius_le_one).trans request.paid)
  have squared := Rat.Fraction.Order.Arithmetic.pow_le_pow_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative (Gaussian.Norm.Basic.normSq_nonneg (finish -
      start))) paid 2
  exact (RootContinuation.PreparedNewtonBandArea.RefinedBoundarySide.area_density_bound side).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squared (by decide))

end RefinedBoundarySide

namespace PreparedBoundaryTraversal

open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (Owner)

variable {request : PreparedBandRequest fixed target}
  {owner : Owner (curve.polynomial.eval
    request.sample.output.box.anchor)} {sheet : Fin 2}

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- The four actual prepared sides bound squared boundary path area by 2560 times target squared.

The estimate retains both the individual side areas and their total-integral joining terms. -/
theorem area_bound (boundary : PreparedBoundaryTraversal request owner sheet) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (increments boundary.model)) ≤ 2560 * target ^ 2 :=
      by
  let blocks := [increments boundary.bottom.model, increments boundary.right.model,
    increments boundary.top.model, increments boundary.left.model]
  have flatten : blocks.flatten = increments boundary.model := by
    rw [boundary.model_eq]
    simp only [blocks, List.flatten_cons, List.flatten_nil, Purelib.Data.List.Append.append_nil,
      Paths.PathArea.increments_append, -eq_self, -iff_self]
    rfl
  have nonnegative : 0 ≤ target := (Gaussian.Basic.Canonical.normSq_nonneg _).trans boundary.bottom.bound
  have areas : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea block) ≤ 16 * target ^
    2 := by
    intro block member
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact RootContinuation.PreparedNewtonBandArea.RefinedBoundarySide.area_bound boundary.bottom
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact RootContinuation.PreparedNewtonBandArea.RefinedBoundarySide.area_bound boundary.right
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact RootContinuation.PreparedNewtonBandArea.RefinedBoundarySide.area_bound boundary.top
    have same := Purelib.Data.List.Membership.mem_singleton.mp member
    subst block
    exact RootContinuation.PreparedNewtonBandArea.RefinedBoundarySide.area_bound boundary.left
  have totals : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum block) ≤
    target := by
    intro block member
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · rw [Paths.PathArea.increments_sum, Gaussian.Norm.Basic.normSq_eq_canonical]
      exact boundary.bottom.bound
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · rw [Paths.PathArea.increments_sum, Gaussian.Norm.Basic.normSq_eq_canonical]
      exact boundary.right.bound
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · rw [Paths.PathArea.increments_sum, Gaussian.Norm.Basic.normSq_eq_canonical]
      exact boundary.top.bound
    have same := Purelib.Data.List.Membership.mem_singleton.mp member
    subst block
    rw [Paths.PathArea.increments_sum, Gaussian.Norm.Basic.normSq_eq_canonical]
    exact boundary.left.bound
  have estimate := Paths.PathArea.blocks_area_bound blocks nonnegative areas totals
  rw [flatten] at estimate
  apply estimate.trans_eq
  change 2 * ((4 : Rat.Fraction.Rational) ^ 2 * (16 * target ^ 2) + 4 * ((4 : Rat.Fraction.Rational) ^ 2 * target) ^ 2)
    = _
  ring1

end PreparedBoundaryTraversal

namespace RequestedPreparedBoundary

variable {sheet : Fin 2}

section
open Purelib.Riemann
open Purelib.Integration
open Purelib.Data
/-- The whole-integral request bounds full fine-path area quadratically.

The squared path area is at most ten times the squared requested integral bound. -/
theorem area_bound (boundary : RequestedPreparedBoundary fixed target sheet) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (increments boundary.traversal.model)) ≤ 10 *
      target ^ 2 := by
  apply (RootContinuation.PreparedNewtonBandArea.PreparedBoundaryTraversal.area_bound
    boundary.traversal).trans_eq
  rw [Rat.Fraction.Field.div_eq_mul_inv_direct]
  calc
    _ = (2560 * (16 : Rat.Fraction.Rational)⁻¹ ^ 2) * target ^ 2 := by ring1
    _ = _ := congrArg (· * target ^ 2) (by decide +kernel : (2560 : Rat.Fraction.Rational) * 16⁻¹ ^ 2 = 10)

/-- Bound the fine trace area while retaining an arbitrary primitive starting anchor.

The bound adds the actual total-integral endpoint term to the quadratic unanchored area estimate. -/
theorem traceArea_bound (boundary : RequestedPreparedBoundary fixed target sheet) (start : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea start (increments boundary.traversal.model)) ≤
      20 * target ^ 2 + 8 * Data.Gaussian.Norm.Basic.normSq start * target := by
  rw [Path.IncrementArea.traceArea_eq, Paths.PathArea.increments_sum]
  have paidScalar : Data.Gaussian.Norm.Basic.normSq boundary.traversal.model.integralSample ≤ target := by
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact boundary.paid
  have endpoint : Data.Gaussian.Norm.Basic.normSq (Path.BoundaryRibbon.area start
    boundary.traversal.model.integralSample) ≤
      4 * Data.Gaussian.Norm.Basic.normSq start * target :=
    (Path.BoundaryRibbon.area_bound start boundary.traversal.model.integralSample).trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paidScalar
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Gaussian.Norm.Basic.normSq_nonneg start)))
  have sum := add_le_add
    (RootContinuation.PreparedNewtonBandArea.RequestedPreparedBoundary.area_bound boundary)
    endpoint
  calc
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (increments boundary.traversal.model)) +
        Data.Gaussian.Norm.Basic.normSq (Path.BoundaryRibbon.area start boundary.traversal.model.integralSample)) :=
      Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (10 * target ^ 2 + 4 * Data.Gaussian.Norm.Basic.normSq start * target) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sum (by decide)
    _ = _ := by ring1

end

open Purelib.Riemann in
open Purelib.Integration in
/-- Cache the actual boundary integral and primitive area in one exact summary.

Both readings use the retained traversal model and require no new root preparation. -/
@[expose] def areaSample (boundary : RequestedPreparedBoundary fixed target sheet) :
    Path.IncrementArea.Summary (increments boundary.traversal.model) :=
  Paths.PathArea.sample boundary.traversal.model

open Purelib.Riemann in
open Purelib.Data in
/-- The cached summary satisfies both the requested integral bound and the quadratic area bound. -/
theorem areaSample_paid (boundary : RequestedPreparedBoundary fixed target sheet) :
    Data.Gaussian.Norm.Basic.normSq (areaSample boundary).total ≤ target ∧
      Data.Gaussian.Norm.Basic.normSq (areaSample boundary).area ≤ 10 * target ^ 2 := by
  rw [(areaSample boundary).total_eq, Paths.PathArea.increments_sum,
    (areaSample boundary).area_eq]
  constructor
  · rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact boundary.paid
  · exact RootContinuation.PreparedNewtonBandArea.RequestedPreparedBoundary.area_bound boundary

end RequestedPreparedBoundary
end Purelib.Riemann.RootContinuation.PreparedNewtonBandArea
