module
import Purelib.Riemann.Paths.PreparedPrimitivePaths
public import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive.Dyadic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
import Purelib.Riemann.Integration.PreparedPrimitiveErrorBudget
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Spatial
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Mathlib.Order.Basic

public section

/-!
# Actual prepared integral comparisons on uniform primitive patches

The uniform patch supplies sheet agreement for every retained child.  The
finite path estimate pays for the actual growing child count, without a
child-owner containment or operational-equivalence premise.
-/

namespace Purelib.Riemann.Integration.UniformPreparedPrimitives

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The exact rational Gaussian carrier. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge RootChildAt RootChildBlock)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : CenteredEdge curve differential}

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- A retained uniform-patch primitive controls the original child model's integral error.

The original root-child relation transports sheet equivalence at the child's start; the supplied endpoint, numerator,
model-error and movement bounds refer to that exact child. -/
theorem child_integral_error_le (patch : PreparedPatch parent)
    {index : Nat} (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator differential))
    {child : CenteredEdge curve differential} (relation : RootChildAt parent child)
    (startInside : (patch.neighborhood count).box.Contains (child.edge.point 0))
    (finishInside : (patch.neighborhood count).box.Contains (child.edge.point 1))
    {numeratorBound error distance : Fraction.Rational}
    (numeratorLe : normSq ((differentialNumerator differential).eval (child.edge.point 0)) ≤ numeratorBound)
    (errorLe : child.edge.modelErrorAllowance ≤ error) (movementLe : child.edge.pointMovement ≤ distance) :
    normSq (model.primitive.value.eval (child.edge.point 1) - model.primitive.value.eval (child.edge.point 0) -
      child.model.integralSample) ≤
      2 * model.primitive.remainderBound * distance ^ 2 +
        (4 * numeratorBound * Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale index + 40 *
          error) * distance := by
  let sample := ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (child.edge.point 0) startInside
  have parentEquivalent := patch.point_equivalent_at count relation.fraction relation.inside relation.point_eq
    startInside sample
  have childEquivalent := relation.rootEquivalent.symm.trans parentEquivalent
  exact PreparedPrimitiveEquivalence.integral_error_le_uniform model child.edge child.center sample
    startInside finishInside childEquivalent numeratorLe errorLe movementLe

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- Every retained root child satisfies the uniform primitive error estimate.

The original block relation supplies each child owner. Its endpoint containment,
numerator ceiling, model error and movement bounds concern that same child. -/
theorem children_bounded (patch : PreparedPatch parent)
    {index : Nat} (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator differential))
    {children : List (CenteredEdge curve differential)} (roots : RootChildBlock parent children)
    (numeratorBound error distance : Fraction.Rational) :
    ∀ child ∈ children,
      (patch.neighborhood count).box.Contains (child.edge.point 0) →
      (patch.neighborhood count).box.Contains (child.edge.point 1) →
      normSq ((differentialNumerator differential).eval (child.edge.point 0)) ≤ numeratorBound →
      child.edge.modelErrorAllowance ≤ error → child.edge.pointMovement ≤ distance →
      normSq (model.primitive.value.eval (child.edge.point 1) - model.primitive.value.eval (child.edge.point 0) -
        child.model.integralSample) ≤
        2 * model.primitive.remainderBound * distance ^ 2 +
          (4 * numeratorBound * Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale index + 40 *
            error) * distance := by
  induction roots with
  | nil => intro child member; cases member
  | cons head tail ih =>
      intro child member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · intro startInside finishInside numeratorLe errorLe movementLe
        exact UniformPreparedPrimitives.child_integral_error_le patch model head startInside finishInside numeratorLe
          errorLe movementLe
      · exact ih child member

open Purelib.Approximation.Rational in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
/-- The retained primitive request bounds the original refined path's integral error.

The exact request block supplies its original child roots, endpoint containment and dyadic count, preserving both count
factors in the finite-path estimate. -/
theorem request_integral_error_le (patch : PreparedPatch parent)
    {target : Fraction.Rational} (request : PreparedPrimitiveRequests.Request parent (patch.neighborhood count) target)
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) :
    normSq (request.model.primitive.value.eval (parent.edge.point 1) - request.model.primitive.value.eval
      (parent.edge.point 0) -
      (Basic.PathModel.mk (request.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample)
        ≤
        2 * request.model.primitive.remainderBound * movement parent * Geometric.Basic.quarterRadius (movement parent)
          request.budget.depth +
          (4 * request.numeratorBound * Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale
            request.index +
            40 * request.budget.error) * movement parent := by
  have starts := PreparedPrimitivePaths.block_starts_inside request.block (patch.neighborhood count).box
    (patch.start_inside count) finishInside
  have finishes := PreparedPrimitivePaths.block_finishes_inside request.block (patch.neighborhood count).box
    (patch.start_inside count) finishInside
  have bounded := children_bounded patch request.model request.block.roots request.numeratorBound request.budget.error
    (Geometric.Basic.quarterRadius (movement parent) request.block.depth)
  have pathBound := Primitive.Dyadic.dyadic_integral_error_le request.model.primitive.value.eval
    (Basic.PathModel.mk (request.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model))
    (PreparedPrimitivePaths.incrementSum_eq _ request.block.chain) request.block.depth
    (by rw [Map.length_map, request.block.childCount]) (movement parent) (2 * request.model.primitive.remainderBound)
    (4 * request.numeratorBound * Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale
      request.index + 40 * request.budget.error)
    (by
      intro cell member
      obtain ⟨child, inChildren, rfl⟩ := Map.mem_map.mp member
      exact bounded child inChildren (starts child inChildren) (finishes child inChildren)
        (request.numerator_le _ (starts child inChildren)) (request.child_modelError_le inChildren)
        (PreparedPrimitivePaths.block_movement_le request.block inChildren))
  rw [request.block_depth] at pathBound
  rw [parent.edge.point_one, parent.edge.point_zero]
  exact pathBound

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
/-- The original uniform-mesh membership supplies endpoint containment for the retained request's integral bound. -/
theorem request_integral_error_le_of_mesh (patch : PreparedPatch parent)
    {target : Fraction.Rational} (request : PreparedPrimitiveRequests.Request parent (patch.neighborhood count) target)
    (mesh : Mesh patch.bounds) (member : parent.parameterEdge ∈ mesh.edges) :
    normSq (request.model.primitive.value.eval (parent.edge.point 1) - request.model.primitive.value.eval
      (parent.edge.point 0) -
      (Basic.PathModel.mk (request.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample)
        ≤
        2 * request.model.primitive.remainderBound * movement parent * Geometric.Basic.quarterRadius (movement parent)
          request.budget.depth +
          (4 * request.numeratorBound * Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale
            request.index +
            40 * request.budget.error) * movement parent :=
  UniformPreparedPrimitives.request_integral_error_le patch request (patch.finish_inside_of_mesh count mesh member)

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
/-- The retained uniform primitive request pays an integral error strictly below eight times its original target. -/
theorem request_integral_error_lt (patch : PreparedPatch parent)
    {target : Fraction.Rational} (request : PreparedPrimitiveRequests.Request parent (patch.neighborhood count) target)
    (positive : 0 < target)
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) :
    normSq (request.model.primitive.value.eval (parent.edge.point 1) - request.model.primitive.value.eval
      (parent.edge.point 0) -
      (Basic.PathModel.mk (request.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample)
        < 8 * target :=
  (UniformPreparedPrimitives.request_integral_error_le patch request finishInside).trans_lt
    (PreparedPrimitiveErrorBudget.Request.operational_bound_lt request positive)

end Purelib.Riemann.Integration.UniformPreparedPrimitives
