module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Rational.Budget.Spatial
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Requested local primitive comparisons for prepared refinements

Choose the inverse-root polynomial first, cache its primitive and Taylor
bound, then choose the prepared root tolerance and geometric depth.  This
constructs all numerical smallness data.  The remaining geometric obligations
are that the actual children lie in the patch and retain its chosen sheet.
-/

namespace Purelib.Riemann.Readings.PreparedPrimitiveRequests

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
  (DirectParentBlock geometricMovement directParentBlockAtDepth)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator coefficientError)
open Purelib.Approximation.Rational.Budget.Spatial (SpatialBudget)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The exact rational Gaussian carrier. -/
abbrev Gaussian := Basic.Canonical

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- The exact original centered parent's geometric movement between its retained parameter endpoints. -/
def movement (parent : CenteredEdge curve differential) : Coordinate :=
  geometricMovement parent.edge.segment parent.edge.left.parameter parent.edge.request.endpoint.parameter

open Purelib.Data.Gaussian in
/-- The original retained parent movement is nonnegative. -/
theorem movement_nonnegative (parent : CenteredEdge curve differential) : 0 ≤ movement parent :=
  Norm.Basic.normSq_nonneg _

section
open Purelib.Riemann.Integration
/-- The sum of the original parent's point-error and root-error coefficients. -/
def preparedScale (parent : CenteredEdge curve differential) : Coordinate :=
  PreparedConstantModels.PreparedEdge.pointErrorCoefficient differential parent.edge.segment +
    PreparedConstantModels.PreparedEdge.rootErrorCoefficient differential parent.edge.segment

/-- The original prepared-model error scale is nonnegative. -/
theorem preparedScale_nonnegative (parent : CenteredEdge curve differential) : 0 ≤ preparedScale parent :=
  add_nonneg (PreparedConstantModels.PreparedEdge.pointErrorCoefficient_nonnegative differential parent.edge.segment)
    (PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative differential parent.edge.segment)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- The original local model error is bounded by its prepared scale times the sum of spatial and root-diameter
allowances. -/
theorem localModelErrorBound_le_preparedScale (parent : CenteredEdge curve differential)
    {rootDiameter : Coordinate} (nonnegative : 0 ≤ rootDiameter) (depth : Nat) :
    PreparedDirectDyadicRefinements.localModelErrorBound differential parent.edge.segment rootDiameter depth
      parent.edge.left.parameter parent.edge.request.endpoint.parameter ≤
        preparedScale parent * (Geometric.Basic.quarterRadius (movement parent) depth + rootDiameter) := by
  have spatialNonnegative := Geometric.Basic.quarterRadius_nonneg (movement_nonnegative parent) depth
  have bound := add_le_add
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (le_add_of_nonneg_right nonnegative : Geometric.Basic.quarterRadius (movement parent) depth ≤ _)
      (PreparedConstantModels.PreparedEdge.pointErrorCoefficient_nonnegative differential parent.edge.segment))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (le_add_of_nonneg_left spatialNonnegative : rootDiameter ≤ _)
      (PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative differential parent.edge.segment))
  exact bound.trans_eq (by unfold preparedScale; ring1)

/-- One quarter of the original continued neighborhood's retained denominator value. -/
def denominatorLower (patch : ContinuedNeighborhood curve.polynomial count) : Coordinate :=
  patch.base.site.denominatorValue / 4

open Purelib.Data.Rat in
/-- The original continued neighborhood's retained denominator lower bound is strictly positive. -/
theorem denominatorLower_positive (patch : ContinuedNeighborhood curve.polynomial count) : 0 < denominatorLower patch :=
  Fraction.Order.Field.div_pos_direct patch.base.site.denominatorValue_positive (by decide)

/-- The original root-refinement error scale combining numerator bound, root lower bound and parent movement. -/
def rootScale (patch : ContinuedNeighborhood curve.polynomial count) (numeratorBound distance : Coordinate) : Coordinate
  :=
  4 * numeratorBound / patch.rootLower * distance * (1 / 256)

open Purelib.Data.Rat in
/-- The original root-refinement scale is nonnegative for nonnegative numerator and movement bounds. -/
theorem rootScale_nonnegative (patch : ContinuedNeighborhood curve.polynomial count) {numeratorBound distance :
  Coordinate}
    (numeratorNonnegative : 0 ≤ numeratorBound) (distanceNonnegative : 0 ≤ distance) :
    0 ≤ rootScale patch numeratorBound distance :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Field.div_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) numeratorNonnegative) patch.rootLower_positive.le)
      distanceNonnegative) (by decide +kernel)

/-- The retained coefficient-error weight for the original neighborhood, numerator bound and movement. -/
def errorWeight (patch : ContinuedNeighborhood curve.polynomial count) (numeratorBound distance : Coordinate) :
  Coordinate :=
  (64 * numeratorBound / denominatorLower patch / patch.rootLower + 8) * distance

open Purelib.Data.Rat in
/-- The original coefficient-error weight is nonnegative under its retained scalar bounds. -/
theorem errorWeight_nonnegative (patch : ContinuedNeighborhood curve.polynomial count) {numeratorBound distance :
  Coordinate}
    (numeratorNonnegative : 0 ≤ numeratorBound) (distanceNonnegative : 0 ≤ distance) :
    0 ≤ errorWeight patch numeratorBound distance := by
  have scaled : 0 ≤ 64 * numeratorBound :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) numeratorNonnegative
  have first := Fraction.Order.Field.div_nonneg_direct scaled (denominatorLower_positive patch).le
  have second := Fraction.Order.Field.div_nonneg_direct first patch.rootLower_positive.le
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (add_nonneg second (by decide)) distanceNonnegative

open Purelib.Algebra in
open Purelib.Approximation.Rational in
/-- Split the original coefficient error into an exact geometric root-refinement term and a weighted preparation error.
-/
theorem coefficientError_split (patch : ContinuedNeighborhood curve.polynomial count)
    (index : Nat) (numeratorBound distance error : Coordinate) :
    coefficientError patch index numeratorBound error * distance =
      Geometric.Basic.quarterRadius (rootScale patch numeratorBound distance) index + errorWeight patch numeratorBound
        distance * error := by
  simp only [coefficientError, rootScale, errorWeight, denominatorLower, Geometric.Basic.quarterRadius,
    Field.ExplicitField.div_eq_mul_inv]
  ring1

open Purelib.Riemann.Branches in
/-- The sufficient original dyadic subdivision depth for the retained parent and requested root diameter. -/
def preparationDepth (parent : CenteredEdge curve differential) (rootDiameter : Coordinate) : Nat :=
  PreparedSheetContinuation.Subdivision.sufficientDyadicDepth parent.edge.segment parent.edge.left
    parent.edge.request.endpoint rootDiameter

open Purelib.Approximation.Rational in
set_option genInjectivity false in
/-- An original parent refinement request retaining its primitive model, numerator bound, spatial budget and exact
direct child block.

The model's root-refinement error is below one third of the target. The original block retains exactly the budget's
depth and root diameter, preserving the prepared child owners. -/
structure Request (parent : CenteredEdge curve differential)
    (patch : ContinuedNeighborhood curve.polynomial count) (target : Coordinate) where
  /-- The retained original differential-numerator norm bound on the neighborhood box. -/ numeratorBound : Coordinate
  /-- The cached original numerator bound is nonnegative. -/ numerator_nonnegative : 0 ≤ numeratorBound
  /-- The original numerator polynomial satisfies the bound at every point of the retained neighborhood. -/ numerator_le
    : ∀ point, patch.box.Contains point → normSq ((differentialNumerator differential).eval point) ≤ numeratorBound
  /-- The retained original primitive-model refinement index. -/ index : Nat
  /-- The exact primitive model at the retained neighborhood and index. -/ model : PrimitiveModel patch index
    (differentialNumerator differential)
  /-- The original geometric root-refinement error is strictly below one third of the target. -/ polynomial_accurate :
    Geometric.Basic.quarterRadius (rootScale patch numeratorBound (movement parent)) index < target / 3
  /-- The retained spatial, root-diameter and preparation-error budget for the original parent and model. -/ budget :
    Budget.Spatial.SpatialBudget target (movement parent) (4 * model.primitive.remainderBound * movement parent)
    (errorWeight patch numeratorBound (movement parent)) (preparedScale parent) (denominatorLower patch)
      (preparationDepth parent)
  /-- The exact original direct-refinement child block acquired for this request. -/ block : DirectParentBlock parent
  /-- The stored child-block depth equals the original budget depth exactly. -/ block_depth : block.depth = budget.depth
  /-- The stored child-block root diameter equals the original budget value exactly. -/ block_rootDiameter :
    block.rootDiameter = budget.rootDiameter

constructive_injectivity Request

namespace Request

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Acquire a spatial budget and direct child block for the supplied original primitive model and accuracy certificate.

The retained numerator bound, model and index are reused. The exact positive root diameter and sufficient depth from the
budget drive the original direct-block construction. -/
def ofModel (parent : CenteredEdge curve differential) (patch : ContinuedNeighborhood curve.polynomial count)
    (target : Coordinate) (targetPositive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (numeratorBound : Coordinate) (numeratorNonnegative : 0 ≤ numeratorBound)
    (numeratorLe : ∀ point, patch.box.Contains point → normSq ((differentialNumerator differential).eval point) ≤
      numeratorBound)
    (index : Nat) (model : PrimitiveModel patch index (differentialNumerator differential))
    (accurate : Geometric.Basic.quarterRadius (rootScale patch numeratorBound (movement parent)) index < target / 3) :
    Request parent patch target :=
  let budget := Budget.Spatial.SpatialBudget.acquire target (movement parent) (4 * model.primitive.remainderBound *
    movement parent)
    (errorWeight patch numeratorBound (movement parent)) (preparedScale parent) (denominatorLower patch)
      (preparationDepth parent)
    targetPositive (movement_nonnegative parent)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) model.primitive.remainderBound_nonnegative)
      (movement_nonnegative parent))
    (errorWeight_nonnegative patch numeratorNonnegative (movement_nonnegative parent))
    (preparedScale_nonnegative parent) (denominatorLower_positive patch)
  let block := directParentBlockAtDepth parent proper budget.rootDiameter budget.rootDiameter_positive
    budget.depth budget.prepared_depth
  { numeratorBound := numeratorBound
    numerator_nonnegative := numeratorNonnegative
    numerator_le := numeratorLe
    index := index
    model := model
    polynomial_accurate := accurate
    budget := budget
    block := block
    block_depth := rfl
    block_rootDiameter := rfl }

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
/-- Construct an original primitive comparison request at a positive target for a proper parent interval.

The exact neighborhood box determines the numerator bound and geometric refinement index; the resulting original
primitive model is passed to the retained budget and child-block constructor. -/
def acquire (parent : CenteredEdge curve differential) (patch : ContinuedNeighborhood curve.polynomial count)
    (target : Coordinate) (targetPositive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) : Request parent patch target :=
  let numeratorBound := Bounds.Box.denseEvalNormBound (differentialNumerator differential) patch.box
  have numeratorNonnegative := (Bounds.Box.denseHornerNormBounds_nonneg (differentialNumerator differential)
    patch.box).1
  let scale := rootScale patch numeratorBound (movement parent)
  let index := Geometric.Search.firstQuarterBelow scale 0 (target / 3)
  let model := PrimitiveModel.ofIndex patch index (differentialNumerator differential)
  ofModel parent patch target targetPositive proper numeratorBound numeratorNonnegative
    (fun point inside => by
      have scalar := Bounds.Box.normSq_eval_le_denseEvalNormBound
        (differentialNumerator differential) (z := point) inside
      simpa only [Norm.Basic.normSq_eq_canonical] using scalar) index model
    (Geometric.Search.firstQuarterBelow_accurate scale (rootScale_nonnegative patch numeratorNonnegative
      (movement_nonnegative parent))
      0 (target / 3) (Fraction.Order.Field.div_pos_direct targetPositive (by decide)))

open Purelib.Riemann.Paths in
/-- Every original retained child in the request block satisfies the exact stored preparation-error budget. -/
theorem child_modelError_le {parent : CenteredEdge curve differential}
    {patch : ContinuedNeighborhood curve.polynomial count} {target : Coordinate}
    (request : Request parent patch target) {child : CenteredEdge curve differential}
    (member : child ∈ request.block.children) : child.edge.modelErrorAllowance ≤ request.budget.error := by
  have bound := PreparedPrimitivePaths.block_modelError_le request.block member
  rw [request.block_depth, request.block_rootDiameter] at bound
  exact bound.trans ((localModelErrorBound_le_preparedScale parent
    request.budget.rootDiameter_positive.le request.budget.depth).trans request.budget.modelError_le)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The original retained child-model integral approximates the primitive endpoint difference within the request target.

Original child endpoint containments and root-box refinements identify the same primitive sheet. The separate
polynomial, Taylor and preparation budgets combine to the retained strict target. -/
theorem integral_error_lt {parent : CenteredEdge curve differential}
    {patch : ContinuedNeighborhood curve.polynomial count} {target : Coordinate}
    (request : Request parent patch target)
    (startInside : ∀ child ∈ request.block.children, patch.box.Contains (child.edge.point 0))
    (finishInside : ∀ child ∈ request.block.children, patch.box.Contains (child.edge.point 1))
    (rootBoxes : ∀ child ∈ request.block.children,
      child.edge.cached.preparedOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) :
    normSq (request.model.primitive.value.eval (parent.edge.point 1) - request.model.primitive.value.eval
      (parent.edge.point 0) -
      (Basic.PathModel.mk (request.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample)
        < target := by
  have errors : ∀ child ∈ request.block.children, child.edge.modelErrorAllowance ≤ request.budget.error := by
    intro child member
    exact request.child_modelError_le member
  have bound := PreparedPrimitivePaths.dyadic_integral_error_le request.model request.block.chain request.block.depth
    request.block.childCount (movement parent) request.numeratorBound request.budget.error
    startInside finishInside rootBoxes
    (fun child member => request.numerator_le _ (startInside child member)) errors request.budget.relative_small
    (fun _ member => PreparedPrimitivePaths.block_movement_le request.block member)
  rw [request.block_depth, coefficientError_split] at bound
  have total := (Fraction.Order.Arithmetic.add_lt_add_right_direct request.polynomial_accurate
    (4 * request.model.primitive.remainderBound * movement parent * Geometric.Basic.quarterRadius (movement parent)
      request.budget.depth +
      errorWeight patch request.numeratorBound (movement parent) * request.budget.error)).trans_le
        (add_le_add le_rfl (add_le_add request.budget.taylor_le request.budget.error_le))
  have totalBound : 4 * request.model.primitive.remainderBound * movement parent * Geometric.Basic.quarterRadius
    (movement parent) request.budget.depth +
      (Geometric.Basic.quarterRadius (rootScale patch request.numeratorBound (movement parent)) request.index +
        errorWeight patch request.numeratorBound (movement parent) * request.budget.error) < target := by
    calc
      _ = Geometric.Basic.quarterRadius (rootScale patch request.numeratorBound (movement parent)) request.index +
        (4 * request.model.primitive.remainderBound * movement parent * Geometric.Basic.quarterRadius (movement parent)
          request.budget.depth +
          errorWeight patch request.numeratorBound (movement parent) * request.budget.error) := by ring1
      _ < target / 3 + (target / 3 + target / 3) := total
      _ = (target / 3) * 3 := by ring1
      _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  rw [parent.edge.point_one, parent.edge.point_zero]
  exact bound.trans_lt totalBound

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- Original parent endpoint containment and retained child root refinements imply the request's strict integral-error
target.

The original direct-block geometry supplies both child endpoint containments without replacing the stored child list or
models. -/
theorem integral_error_lt_of_endpoints {parent : CenteredEdge curve differential}
    {patch : ContinuedNeighborhood curve.polynomial count} {target : Coordinate}
    (request : Request parent patch target)
    (startInside : patch.box.Contains (parent.edge.point 0))
    (finishInside : patch.box.Contains (parent.edge.point 1))
    (rootBoxes : ∀ child ∈ request.block.children,
      child.edge.cached.preparedOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) :
    normSq (request.model.primitive.value.eval (parent.edge.point 1) - request.model.primitive.value.eval
      (parent.edge.point 0) -
      (Basic.PathModel.mk (request.block.children.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample)
        < target :=
  request.integral_error_lt (PreparedPrimitivePaths.block_starts_inside request.block patch.box startInside
    finishInside)
    (PreparedPrimitivePaths.block_finishes_inside request.block patch.box startInside finishInside) rootBoxes

end Request

end Purelib.Riemann.Readings.PreparedPrimitiveRequests
