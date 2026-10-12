module
import Purelib.Data.List.Membership
import Purelib.Riemann.Paths.PreparedPrimitivePaths
public import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive.Dyadic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

public import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
import Purelib.Riemann.Integration.PreparedPrimitiveErrorBudget
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Requested prepared primitives with constructed sheet compatibility

The parent supplies a compatible local patch.  Its root-child records identify
all actual subdivision occurrences with that patch, including recentered
children.  A fixed additional accuracy factor pays the finite equivalence
comparison.  Only endpoint containment in the local coordinate patch remains;
there is no per-child root-box or sheet-equivalence input to the request law.
-/

open Purelib.Data

namespace Purelib.Riemann.Integration.PreparedCompatiblePrimitives

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Branches.PreparedPrimitiveSheets (CompatiblePatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge RootChildBlock)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement rootScale errorWeight)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the primitive error requests. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the primitive samples. -/
abbrev Gaussian := Basic.Canonical

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Riemann.Readings in
/-- The original primitive approximation request for the retained parent and continued neighborhood. -/
abbrev ApproximationRequest (parent : CenteredEdge curve differential)
    (patch : ContinuedNeighborhood curve.polynomial count) (target : Coordinate) :=
  PreparedPrimitiveRequests.Request parent patch target

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
/-- Bound each retained child integral error using the original compatible parent patch.

The child root witness is composed with the patch's exact continued-root equivalence; endpoint containment, numerator,
model-error and movement bounds control that child's primitive increment. -/
private theorem children_bounded {parent : CenteredEdge curve differential} (patch : CompatiblePatch parent count)
    {index : Nat} (model : PrimitiveModel patch.neighborhood index (differentialNumerator differential))
    {children : List (CenteredEdge curve differential)} (roots : RootChildBlock parent children)
    (numeratorBound error distance : Coordinate) :
    ∀ child ∈ children,
      patch.neighborhood.box.Contains (child.edge.point 0) → patch.neighborhood.box.Contains (child.edge.point 1) →
      normSq ((differentialNumerator differential).eval (child.edge.point 0)) ≤ numeratorBound →
      child.edge.modelErrorAllowance ≤ error → child.edge.pointMovement ≤ distance →
      normSq (model.primitive.value.eval (child.edge.point 1) - model.primitive.value.eval (child.edge.point 0) -
        child.model.integralSample) ≤
        2 * model.primitive.remainderBound * distance ^ 2 +
          (4 * numeratorBound * Geometric.Basic.quarterRadius patch.neighborhood.inverseErrorScale index + 40 * error) *
            distance := by
  induction roots with
  | nil => intro child member; cases member
  | cons head tail ih =>
      intro child member
      rcases List.Membership.mem_cons.mp member with rfl | member
      · intro startInside finishInside numeratorLe errorLe movementLe
        let sample := ContinuedNeighborhood.Point.acquire patch.neighborhood (child.edge.point 0) startInside
        have parentEquivalent := patch.point_equivalent_at head.fraction head.inside head.point_eq sample
        have childEquivalent := Equivalence.NamedEquivalent.trans head.rootEquivalent.symm parentEquivalent
        exact PreparedPrimitiveEquivalence.integral_error_le_uniform model child.edge child.center sample
          startInside finishInside childEquivalent numeratorLe errorLe movementLe
      · exact ih child member

open Purelib.Approximation.Rational in
open Purelib.Data.List in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The retained dyadic child block approximates the compatible primitive increment within eight times the target.

The same child's numerator and movement bounds enter the finite dyadic sum estimate; the original request depth and
operational budget provide the strict payment. -/
theorem block_integral_error_lt {parent : CenteredEdge curve differential} (patch : CompatiblePatch parent count)
    {target : Coordinate} (request : ApproximationRequest parent patch.neighborhood target) (positive : 0 < target)
    (finishInside : patch.neighborhood.box.Contains (parent.edge.point 1)) :
    normSq (request.model.primitive.value.eval (parent.edge.point 1) - request.model.primitive.value.eval
      (parent.edge.point 0) -
      (Basic.PathModel.mk (request.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample)
        < 8 * target := by
  have starts := PreparedPrimitivePaths.block_starts_inside request.block patch.neighborhood.box patch.start_inside
    finishInside
  have finishes := PreparedPrimitivePaths.block_finishes_inside request.block patch.neighborhood.box patch.start_inside
    finishInside
  have errors : ∀ child ∈ request.block.children, child.edge.modelErrorAllowance ≤ request.budget.error := by
    intro child member
    exact request.child_modelError_le member
  have bounded := children_bounded patch request.model request.block.roots request.numeratorBound request.budget.error
    (Geometric.Basic.quarterRadius (movement parent) request.block.depth)
  have pathBound := Primitive.Dyadic.dyadic_integral_error_le request.model.primitive.value.eval
    (Basic.PathModel.mk (request.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model))
    (PreparedPrimitivePaths.incrementSum_eq _ request.block.chain) request.block.depth
    (by rw [List.Map.length_map, request.block.childCount]) (movement parent) (2 *
      request.model.primitive.remainderBound)
    (4 * request.numeratorBound * Geometric.Basic.quarterRadius patch.neighborhood.inverseErrorScale request.index + 40
      * request.budget.error)
    (by
      intro cell member
      obtain ⟨child, inChildren, rfl⟩ := Map.mem_map.mp member
      exact bounded child inChildren (starts child inChildren) (finishes child inChildren)
        (request.numerator_le _ (starts child inChildren)) (errors child inChildren)
        (PreparedPrimitivePaths.block_movement_le request.block inChildren))
  rw [request.block_depth] at pathBound
  rw [parent.edge.point_one, parent.edge.point_zero]
  exact pathBound.trans_lt (PreparedPrimitiveErrorBudget.Request.operational_bound_lt request positive)

set_option genInjectivity false in
/-- A positive error request with its exact compatible patch and one-eighth-target approximation.

The patch is indexed by the original centered parent, while the approximation retains that neighborhood and the divided
target used to pay the block's factor-eight bound. -/
structure Request (parent : CenteredEdge curve differential) (count : Nat) (target : Coordinate) where
  /-- Strict positivity of the original requested error target. -/ target_positive : 0 < target
  /-- The original compatible continued-neighborhood patch of this centered parent. -/ patch : CompatiblePatch parent
    count
  /-- The retained primitive approximation at exactly one-eighth of that target. -/ approximation : ApproximationRequest
    parent patch.neighborhood (target / 8)

constructive_injectivity Request

namespace Request

open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
/-- Acquire the original primitive approximation on a supplied compatible patch at one-eighth of the positive target. -/
def ofPatch {parent : CenteredEdge curve differential} (patch : CompatiblePatch parent count)
    (target : Coordinate) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) : Request parent count target where
  target_positive := positive
  patch := patch
  approximation := PreparedPrimitiveRequests.Request.acquire parent patch.neighborhood (target / 8)
    (Fraction.Order.Field.div_pos_direct positive (by decide)) proper

/-- Acquire a compatible patch and its primitive request for the original proper parent edge. -/
def acquire (parent : CenteredEdge curve differential) (count : Nat) (target : Coordinate) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) : Request parent count target :=
  ofPatch (CompatiblePatch.acquire parent count) target positive proper

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
/-- The retained primitive request's child-block integral error is strictly below its original target.

The parent finish must lie in the retained patch; the block estimate is paid by the exact one-eighth target stored in
the request. -/
theorem accurate {parent : CenteredEdge curve differential} {target : Coordinate}
    (request : Request parent count target)
    (finishInside : request.patch.neighborhood.box.Contains (parent.edge.point 1)) :
    normSq (request.approximation.model.primitive.value.eval (parent.edge.point 1) -
      request.approximation.model.primitive.value.eval (parent.edge.point 0) -
        (Basic.PathModel.mk (request.approximation.block.children.map
          PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample) < target := by
  have bound := block_integral_error_lt request.patch request.approximation
    (Fraction.Order.Field.div_pos_direct request.target_positive (by decide)) finishInside
  have cancellation : 8 * (target / 8) = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact bound.trans_eq cancellation

end Request

end Purelib.Riemann.Integration.PreparedCompatiblePrimitives
