module
import Purelib.Algebra.Group.Negation
import Purelib.Data.List.Membership
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive.Dyadic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

public import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

@[expose] public section

/-!
# Local primitives along connected prepared paths

The actual dependent path chain supplies endpoint cancellation.  Local
primitive estimates are transferred to the existing centered path samples,
not to a replacement integration program.  Containment and sheet alignment
remain explicit internal geometric obligations.
-/

namespace Purelib.Riemann.Paths.PreparedPrimitivePaths

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)

open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator canonicalError)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The exact rational carrier for prepared path error estimates. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier for path and primitive readings. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
/-- Primitive increments over an original direct prepared path chain telescope to its retained endpoint difference. -/
theorem incrementSum_eq (primitive : Gaussian → Gaussian)
    {parents : List (CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain parents (start := start) (finish := finish)) :
    Primitive.incrementSum primitive
        (parents.map PreparedSubdivisionModelCore.CenteredEdge.model) =
      primitive finish.coordinate - primitive start.coordinate := by
  induction chain with
  | nil point => change (0 : Gaussian) = primitive point.coordinate - primitive point.coordinate; ring1
  | cons parent tail ih =>
      change primitive (parent.edge.point 1) - primitive (parent.edge.point 0) +
        Primitive.incrementSum primitive
          (List.map PreparedSubdivisionModelCore.CenteredEdge.model _) = _
      rw [ih, parent.edge.point_one, parent.edge.point_zero]
      ring1

open Purelib.Data.Rat in
/-- A unit-interval affine combination of two points in the same rational interval remains in that interval.

Both endpoints satisfy the original lower and upper bounds, and the unit-interval parameter makes each affine weight
nonnegative. Direct scalar multiplication and addition preserve those two bounds. -/
private theorem affine_between {lower upper left right fraction : Coordinate}
    (leftInside : lower ≤ left ∧ left ≤ upper) (rightInside : lower ≤ right ∧ right ≤ upper)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    lower ≤ (1 - fraction) * left + fraction * right ∧ (1 - fraction) * left + fraction * right ≤ upper := by
  have complementary : 0 ≤ 1 - fraction := Fraction.Order.Arithmetic.sub_nonneg_direct inside.2
  constructor
  · calc
      lower = (1 - fraction) * lower + fraction * lower := by ring1
      _ ≤ _ := Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct leftInside.1 complementary)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightInside.1 inside.1)
  · calc
      _ ≤ (1 - fraction) * upper + fraction * upper := Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct leftInside.2 complementary)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightInside.2 inside.1)
      _ = upper := by ring1

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Every unit-interval point of an original prepared edge lies in a box containing both of its endpoints. -/
theorem point_inside_of_endpoints (parent : CenteredEdge curve differential) (box : Box)
    (startInside : box.Contains (parent.edge.point 0)) (finishInside : box.Contains (parent.edge.point 1))
    {fraction : Coordinate} (inside : 0 ≤ fraction ∧ fraction ≤ 1) : box.Contains (parent.edge.point fraction) := by
  have first := startInside
  have last := finishInside
  change box.Contains (parent.edge.localSegment.pointAt 0) at first
  change box.Contains (parent.edge.localSegment.pointAt 1) at last
  rw [Geometry.ClearPath.ClearSegment.pointAt_zero] at first
  rw [Geometry.ClearPath.ClearSegment.pointAt_one] at last
  have realBounds := affine_between ⟨first.1, first.2.1⟩ ⟨last.1, last.2.1⟩ inside
  have imaginaryBounds := affine_between ⟨first.2.2.1, first.2.2.2⟩ ⟨last.2.2.1, last.2.2.2⟩ inside
  change box.Contains (parent.edge.localSegment.pointAt fraction)
  unfold Geometry.ClearPath.ClearSegment.pointAt Box.Contains
  simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Scale.scale_re, Scale.scale_im]
  have affine (left right : Coordinate) : left + fraction * (right - left) = (1 - fraction) * left + fraction * right :=
    by ring1
  rw [affine, affine]
  exact ⟨realBounds.1, realBounds.2, imaginaryBounds.1, imaginaryBounds.2⟩

open Purelib.Geometry.Path.Gaussian in
open Purelib.Geometry.Rational in
/-- An original direct prepared chain starts in the box if all retained edge starts and its final endpoint lie there. -/
private theorem chain_start_inside (box : Box)
    {parents : List (CenteredEdge curve differential)} {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain parents (start := start) (finish := finish))
    (starts : ∀ parent ∈ parents, box.Contains (parent.edge.point 0))
    (last : box.Contains finish.coordinate) : box.Contains start.coordinate := by
  cases chain with
  | nil point => exact last
  | cons parent tail =>
      have first := starts parent (List.mem_cons_self ..)
      rw [parent.edge.point_zero] at first
      exact first

open Purelib.Geometry.Path.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Data.List in
/-- Every retained edge finish lies in the box when all original edge starts and the chain's final endpoint do. -/
theorem chain_finishes_inside (box : Box)
    {parents : List (CenteredEdge curve differential)} {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain parents (start := start) (finish := finish))
    (starts : ∀ parent ∈ parents, box.Contains (parent.edge.point 0))
    (last : box.Contains finish.coordinate) : ∀ parent ∈ parents, box.Contains (parent.edge.point 1) := by
  induction chain with
  | nil point => intro parent member; cases member
  | cons parent tail ih =>
      have tailStarts := fun child member => starts child (List.mem_cons_of_mem parent member)
      have next := chain_start_inside box tail tailStarts last
      intro child member
      rcases Membership.mem_cons.mp member with rfl | member
      · rw [child.edge.point_one]; exact next
      · exact ih tailStarts last child member

open Purelib.Data.List in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
/-- A common squared error bound on each retained prepared cell gives the square-of-length error bound for the original
path integral sample.

The direct path chain identifies the exact telescoping endpoint difference, and the mapped cell list retains the
original parent order and cardinality. -/
theorem integral_error_le_uniform (primitive : Gaussian → Gaussian)
    {parents : List (CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain parents (start := start) (finish := finish))
    (budget : Coordinate)
    (bounded : ∀ parent ∈ parents,
      normSq (primitive (parent.edge.point 1) - primitive (parent.edge.point 0) -
        parent.model.integralSample) ≤ budget) :
    normSq (primitive finish.coordinate - primitive start.coordinate -
      (Basic.PathModel.mk (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample) ≤
        (parents.length : Coordinate) * ((parents.length : Coordinate) * budget) := by
  have bound := Primitive.integral_error_le_uniform primitive _ (incrementSum_eq primitive chain) budget
    (by
      intro cell member
      obtain ⟨parent, inParents, rfl⟩ := Map.mem_map.mp member
      exact bounded parent inParents)
  rewrite [Map.length_map] at bound
  exact bound

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
/-- Sum the original primitive comparison errors over a retained direct prepared path chain.

Each cell keeps both endpoint containments, prepared-root refinement, small relative residual and the supplied common
local budget; the total bound is the squared cell count times that budget. -/
theorem integral_error_le {patch : ContinuedNeighborhood curve.polynomial count} {index : Nat}
    (model : PrimitiveModel patch index (differentialNumerator differential))
    {parents : List (CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain parents (start := start) (finish := finish))
    (startInside : ∀ parent ∈ parents, patch.box.Contains (parent.edge.point 0))
    (finishInside : ∀ parent ∈ parents, patch.box.Contains (parent.edge.point 1))
    (rootBoxes : ∀ parent ∈ parents,
      parent.edge.cached.preparedOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (small : ∀ parent ∈ parents, PreparedPrimitiveSamples.relativeError patch parent.edge ≤ 1 / 4096)
    (budget : Coordinate)
    (budgets : ∀ parent ∈ parents,
      2 * (canonicalError model parent.edge + 4 * parent.edge.modelErrorAllowance * parent.edge.pointMovement) ≤ budget)
        :
    normSq (model.primitive.value.eval finish.coordinate - model.primitive.value.eval start.coordinate -
      (Basic.PathModel.mk (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample) ≤
        (parents.length : Coordinate) * ((parents.length : Coordinate) * budget) := by
  apply integral_error_le_uniform _ chain budget
  intro parent member
  exact (PreparedPrimitiveSamples.centered_integral_error model parent.edge parent.center
    (startInside parent member) (finishInside parent member) (rootBoxes parent member) (small parent member)).trans
    (budgets parent member)

open Purelib.Approximation.Rational in
open Purelib.Data.List in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
/-- Bound the original prepared path integral discrepancy using a power-of-two cell count and geometric movement bounds.

The retained cells share numerator and model-error majorants, small relative residual and root-owner refinements. The
bound separates the geometrically contracting primitive remainder from the coefficient-error term. -/
theorem dyadic_integral_error_le {patch : ContinuedNeighborhood curve.polynomial count} {index : Nat}
    (model : PrimitiveModel patch index (differentialNumerator differential))
    {parents : List (CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain parents (start := start) (finish := finish))
    (depth : Nat) (childCount : parents.length = 2 ^ depth)
    (movement numeratorBound error : Coordinate)
    (startInside : ∀ parent ∈ parents, patch.box.Contains (parent.edge.point 0))
    (finishInside : ∀ parent ∈ parents, patch.box.Contains (parent.edge.point 1))
    (rootBoxes : ∀ parent ∈ parents,
      parent.edge.cached.preparedOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (numerators : ∀ parent ∈ parents,
      normSq ((differentialNumerator differential).eval (parent.edge.point 0)) ≤ numeratorBound)
    (errors : ∀ parent ∈ parents, parent.edge.modelErrorAllowance ≤ error)
    (small : error / (patch.base.site.denominatorValue / 4) ≤ 1 / 4096)
    (movements : ∀ parent ∈ parents,
      parent.edge.pointMovement ≤ Geometric.Basic.quarterRadius movement depth) :
    normSq (model.primitive.value.eval finish.coordinate - model.primitive.value.eval start.coordinate -
      (Basic.PathModel.mk (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample) ≤
        4 * model.primitive.remainderBound * movement * Geometric.Basic.quarterRadius movement depth +
          PreparedPrimitiveSamples.coefficientError patch index numeratorBound error * movement := by
  apply Primitive.Dyadic.dyadic_integral_error_le _ _ (incrementSum_eq _ chain) depth
    (by rw [Map.length_map, childCount]) movement (4 * model.primitive.remainderBound)
    (PreparedPrimitiveSamples.coefficientError patch index numeratorBound error)
  intro cell member
  obtain ⟨parent, inParents, rfl⟩ := Map.mem_map.mp member
  exact PreparedPrimitiveSamples.centered_integral_error_uniform model parent.edge parent.center
    (startInside parent inParents) (finishInside parent inParents) (rootBoxes parent inParents)
    (numerators parent inParents) (errors parent inParents) small (movements parent inParents)

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectParentBlock geometricMovement
  localModelErrorBound)

open Purelib.Geometry.Rational in
open Purelib.Data.List in
/-- Every child start in the retained direct parent block lies in a box containing both original parent endpoints. -/
theorem block_starts_inside {parent : CenteredEdge curve differential} (block : DirectParentBlock parent)
    (box : Box)
    (startInside : box.Contains (parent.edge.point 0)) (finishInside : box.Contains (parent.edge.point 1)) :
    ∀ child ∈ block.children, box.Contains (child.edge.point 0) := by
  have roots := block.roots
  generalize block.children = children at roots ⊢
  induction roots with
  | nil => intro child member; cases member
  | cons head tail ih =>
      intro child member
      rcases Membership.mem_cons.mp member with rfl | member
      · rw [← head.point_eq]
        exact point_inside_of_endpoints parent box startInside finishInside head.inside
      · exact ih child member

open Purelib.Geometry.Rational in
/-- Every child finish in the retained direct parent block lies in a box containing both original parent endpoints. -/
theorem block_finishes_inside {parent : CenteredEdge curve differential} (block : DirectParentBlock parent)
    (box : Box)
    (startInside : box.Contains (parent.edge.point 0)) (finishInside : box.Contains (parent.edge.point 1)) :
    ∀ child ∈ block.children, box.Contains (child.edge.point 1) := by
  apply chain_finishes_inside box block.chain (block_starts_inside block box startInside finishInside)
  rw [parent.edge.point_one] at finishInside
  exact finishInside

open Purelib.Approximation.Rational in
open Purelib.Data.List in
/-- A retained child in a direct parent block satisfies the original geometric movement bound at the block depth. -/
theorem block_movement_le {parent : CenteredEdge curve differential} (block : DirectParentBlock parent)
    {child : CenteredEdge curve differential} (member : child ∈ block.children) :
    child.edge.pointMovement ≤ Geometric.Basic.quarterRadius
      (geometricMovement parent.edge.segment parent.edge.left.parameter parent.edge.request.endpoint.parameter)
        block.depth := by
  have bounded : ∀ child ∈ block.children, child.edge.pointMovement ≤ Geometric.Basic.quarterRadius
      (geometricMovement parent.edge.segment parent.edge.left.parameter parent.edge.request.endpoint.parameter)
        block.depth := by
    have evidence := block.movements
    generalize block.children = children at evidence ⊢
    induction evidence with
    | nil => intro child member; cases member
    | cons head tail ih =>
        intro child member
        rcases Membership.mem_cons.mp member with rfl | member
        · exact head
        · exact ih child member
  exact bounded child member

open Purelib.Data.List in
/-- A retained child in a direct parent block satisfies the original local model error bound using its cached root
diameter and depth. -/
theorem block_modelError_le {parent : CenteredEdge curve differential} (block : DirectParentBlock parent)
    {child : CenteredEdge curve differential} (member : child ∈ block.children) :
    child.edge.modelErrorAllowance ≤ localModelErrorBound differential parent.edge.segment block.rootDiameter
      block.depth parent.edge.left.parameter parent.edge.request.endpoint.parameter := by
  have bounded : ∀ child ∈ block.children, child.edge.modelErrorAllowance ≤
      localModelErrorBound differential parent.edge.segment block.rootDiameter
        block.depth parent.edge.left.parameter parent.edge.request.endpoint.parameter := by
    have evidence := block.errors
    generalize block.children = children at evidence ⊢
    induction evidence with
    | nil => intro child member; cases member
    | cons head tail ih =>
        intro child member
        rcases Membership.mem_cons.mp member with rfl | member
        · exact head
        · exact ih child member
  exact bounded child member

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
/-- Compare the retained direct parent block's integral sample with the original primitive increment across its parent
endpoints.

The original child endpoint containments and root-box refinements remain explicit. Cached block depth, root diameter,
numerator box majorant and local error bound determine the two quantitative error terms. -/
theorem block_integral_error_le {patch : ContinuedNeighborhood curve.polynomial count} {index : Nat}
    (model : PrimitiveModel patch index (differentialNumerator differential))
    {parent : CenteredEdge curve differential} (block : DirectParentBlock parent)
    (startInside : ∀ child ∈ block.children, patch.box.Contains (child.edge.point 0))
    (finishInside : ∀ child ∈ block.children, patch.box.Contains (child.edge.point 1))
    (rootBoxes : ∀ child ∈ block.children,
      child.edge.cached.preparedOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (small : localModelErrorBound differential parent.edge.segment block.rootDiameter block.depth
        parent.edge.left.parameter parent.edge.request.endpoint.parameter /
          (patch.base.site.denominatorValue / 4) ≤ 1 / 4096) :
    let movement := geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter
    normSq (model.primitive.value.eval (parent.edge.point 1) - model.primitive.value.eval (parent.edge.point 0) -
      (Basic.PathModel.mk (block.children.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample) ≤
        4 * model.primitive.remainderBound * movement * Geometric.Basic.quarterRadius movement block.depth +
          PreparedPrimitiveSamples.coefficientError patch index
            (Bounds.Box.denseEvalNormBound (differentialNumerator differential) patch.box)
            (localModelErrorBound differential parent.edge.segment block.rootDiameter block.depth
              parent.edge.left.parameter parent.edge.request.endpoint.parameter) * movement := by
  dsimp only
  rw [parent.edge.point_one, parent.edge.point_zero]
  have numeratorBounds : ∀ child ∈ block.children,
      normSq ((differentialNumerator differential).eval (child.edge.point 0)) ≤
        Bounds.Box.denseEvalNormBound
          (differentialNumerator differential) patch.box := by
    intro child member
    have scalar := Bounds.Box.normSq_eval_le_denseEvalNormBound
      (differentialNumerator differential) (startInside child member)
    simpa only [Norm.Basic.normSq_eq_canonical] using scalar
  exact dyadic_integral_error_le model block.chain block.depth block.childCount
    (geometricMovement parent.edge.segment parent.edge.left.parameter parent.edge.request.endpoint.parameter)
    (Bounds.Box.denseEvalNormBound
      (differentialNumerator differential) patch.box)
    (localModelErrorBound differential parent.edge.segment block.rootDiameter block.depth
      parent.edge.left.parameter parent.edge.request.endpoint.parameter)
    startInside finishInside rootBoxes numeratorBounds
    (fun _ member => block_modelError_le block member) small (fun _ member => block_movement_le block member)

end Purelib.Riemann.Paths.PreparedPrimitivePaths
