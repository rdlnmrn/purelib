module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Approximation.Rational.Budget.Spatial
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

public import Purelib.Riemann.Integration.PreparedModelAccuracy
import Purelib.Riemann.Readings.PreparedPrimitiveRequestWeakening
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
public import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Integration.Polynomial.Gaussian.Path.Execution
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-!
# Resample retained primitive requests at a second model-error ceiling

The polynomial, its index and its endpoint increment are unchanged. Only the
direct children are prepared again, paying both the original primitive budget
and an additional positive model-error ceiling. This lets a Newton-band bound
and a face-primitive comparison consume the same original parents and sum.
-/

namespace Purelib.Riemann.Integration.PreparedPrimitiveResampling

public section

open Purelib.Data.Rat

namespace Request

open Purelib.Data.Nat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests
  (Coordinate Request movement movement_nonnegative preparedScale preparedScale_nonnegative
    preparationDepth errorWeight errorWeight_nonnegative denominatorLower denominatorLower_positive)
open Purelib.Riemann.Readings.UniformPreparedRequests (PrimitiveSumRequest)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : CenteredEdge curve differential} {patch : ContinuedNeighborhood curve.polynomial count}
  {target ceiling : Coordinate}

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Refine the original spatial budget to a positive model-error ceiling.

The new error is the minimum of the retained error and ceiling; the selected root diameter and maximum depth preserve
the original Taylor and request payments. -/
@[expose] def cappedBudget (request : Request parent patch target) (positive : 0 < ceiling) :
    Budget.Spatial.SpatialBudget target (movement parent)
      (4 * request.model.primitive.remainderBound * movement parent)
      (errorWeight patch request.numeratorBound (movement parent)) (preparedScale parent)
      (denominatorLower patch) (preparationDepth parent) := by
  let error := min request.budget.error ceiling
  let selected := PreparedModelAccuracy.Budget.build (movement parent) (preparedScale parent)
    (preparationDepth parent) (movement_nonnegative parent) (preparedScale_nonnegative parent)
    (Fraction.Order.Basic.lt_min request.budget.error_positive positive : 0 < error)
  let depth := max request.budget.depth selected.depth
  have decreased := quarterRadius_antitone (movement_nonnegative parent)
    (Order.le_max_right request.budget.depth selected.depth)
  exact
    { error := error
      error_positive := Fraction.Order.Basic.lt_min request.budget.error_positive positive
      relative_small := (Fraction.Order.Field.divide_mono (Fraction.Order.Basic.min_le_left _ _)
        (denominatorLower_positive patch)).trans request.budget.relative_small
      rootDiameter := selected.diameter
      rootDiameter_positive := selected.diameterPositive
      depth := depth
      prepared_depth := selected.prepared.trans (Order.le_max_right _ _)
      modelError_le := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct decreased (by exact Eq.le (Eq.refl _))) (preparedScale_nonnegative
          parent)).trans selected.paid
      taylor_le := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (quarterRadius_antitone (movement_nonnegative parent) (Order.le_max_left _ _))
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.model.primitive.remainderBound_nonnegative)
          (movement_nonnegative parent))).trans request.budget.taylor_le
      error_le := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_left _ _)
        (errorWeight_nonnegative patch request.numerator_nonnegative (movement_nonnegative parent))).trans
          request.budget.error_le }

/-- Resample the retained primitive request using a positive model-error ceiling.

The original primitive model and target are retained; a capped budget selects the new direct child block and preserves
its exact depth and root-diameter identities. -/
@[expose] def resample (request : Request parent patch target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (positive : 0 < ceiling) :
    Request parent patch target :=
  let budget := cappedBudget request positive
  let block := PreparedDirectDyadicRefinements.directParentBlockAtDepth parent proper budget.rootDiameter
    budget.rootDiameter_positive budget.depth budget.prepared_depth
  { request with budget := budget, block := block, block_depth := rfl, block_rootDiameter := rfl }

section
open Purelib.Riemann.Integration
/-- Resampling retains the exact original primitive model. -/
theorem resample_model (request : Request parent patch target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (positive : 0 < ceiling) :
    (PreparedPrimitiveResampling.Request.resample request proper positive).model = request.model := rfl

/-- The resampled budget's retained model-error bound is at most the requested ceiling. -/
theorem resample_error_le (request : Request parent patch target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (positive : 0 < ceiling) :
    (PreparedPrimitiveResampling.Request.resample request proper positive).budget.error ≤ ceiling :=
      Fraction.Order.Basic.min_le_right _ _

end

open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
/-- Every retained resampled child meets the positive model-error ceiling.

The child belongs to the same resampled direct block. Its original model-error allowance is bounded by the retained
budget error, which is at most the supplied ceiling. -/
theorem resample_child_error (request : Request parent patch target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (positive : 0 < ceiling)
    {child : CenteredEdge curve differential} (member : child ∈ (PreparedPrimitiveResampling.Request.resample request
      proper positive).block.children) :
    child.edge.modelErrorAllowance ≤ ceiling :=
  ((PreparedPrimitiveRequests.Request.child_modelError_le
    (PreparedPrimitiveResampling.Request.resample request proper positive) member).trans
      (Fraction.Order.Basic.min_le_right _ _))

end Request

namespace UniformPrimitiveNeighborhoods

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents PrimitiveSumRequest LocalRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Request)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {target ceiling : Purelib.Riemann.Readings.PreparedPrimitiveRequests.Coordinate}

open Purelib.Riemann.Integration in
/-- Resample the local request while preserving its original patch, neighborhood and endpoint containment.

Only the retained primitive request is resampled under the supplied positive ceiling. The original local patch,
ownership and endpoint witnesses remain the same fields. -/
@[expose] def LocalRequest.resample {parent : CenteredEdge curve differential} (request : LocalRequest parent count
  target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (positive : 0 < ceiling) :
    LocalRequest parent count target :=
  { request with request := PreparedPrimitiveResampling.Request.resample request.request proper positive }

namespace RequestedParents

open Purelib.Riemann.Integration in
/-- Resample the original request family in parent order under the shared positive error ceiling.

Each original proper parent retains its primitive model while its local spatial budget and child block are refined. -/
@[expose] def resample {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count target
  parents)
    (proper : AllParentsProper parents) (positive : 0 < ceiling) : RequestedParents count target parents :=
  match requests with
  | .nil => .nil
  | .cons request tail => .cons
      (PreparedPrimitiveResampling.UniformPrimitiveNeighborhoods.LocalRequest.resample request proper.1 positive)
      (resample tail proper.2 positive)

/-- Resampling retains the exact original primitive increment list. -/
theorem resample_increments {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count target
  parents)
    (proper : AllParentsProper parents) (positive : 0 < ceiling) :
    (RequestedParents.resample requests proper positive).increments = requests.increments := by
  induction requests with
  | nil => rfl
  | cons request tail ih => exact congrArg (List.cons _) (ih proper.2)

/-- Resampling retains the exact original primitive-value list. -/
theorem resample_primitiveValues {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count
  target parents)
    (proper : AllParentsProper parents) (positive : 0 < ceiling) :
    (RequestedParents.resample requests proper positive).primitiveValues = requests.primitiveValues := by
  induction requests with
  | nil => rfl
  | cons request tail ih => exact congrArg (List.cons _) (ih proper.2)

open Purelib.Riemann.Integration in
/-- Every retained resampled child meets the positive model-error ceiling.

The original request family retains its parent order and properness witnesses. Each child belongs to the corresponding
head block or remaining tail, and its original allowance meets the same supplied ceiling. -/
theorem resample_child_error {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count
  target parents)
    (proper : AllParentsProper parents) (positive : 0 < ceiling) :
    ∀ child ∈ (RequestedParents.resample requests proper positive).blocks.children, child.edge.modelErrorAllowance ≤
      ceiling := by
  induction requests with
  | nil => intro child member; cases member
  | cons request tail ih =>
      intro child member
      rcases Membership.mem_append.mp member with first | last
      · exact PreparedPrimitiveResampling.Request.resample_child_error
          request.request proper.1 positive first
      · exact ih proper.2 child last

end RequestedParents

namespace PrimitiveSumRequest

variable {parents : List (CenteredEdge curve differential)}

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Resample the original sum request while retaining its cached primitive increments and total.

The new child blocks and tail integral sample come from the exact resampled request family; their readback identities
remain bound to the original primitive data. -/
@[expose] def resample (request : PrimitiveSumRequest parents count target) (proper : AllParentsProper parents)
    (positive : 0 < ceiling) : PrimitiveSumRequest parents count target :=
  let requests := RequestedParents.resample request.requests proper positive
  let blocks := requests.blocks
  let model := Basic.PathModel.mk (blocks.children.map CenteredEdge.model)
  { request with
    requests := requests
    blocks := blocks
    blocks_eq := rfl
    increments_eq := request.increments_eq.trans (RequestedParents.resample_increments request.requests proper
      positive).symm
    integralSample := model.tailIntegralSample
    integralSample_eq := model.integralSample_eq_tailIntegralSample.symm }

open Purelib.Riemann.Integration
/-- Resampling retains the exact original cached primitive sum. -/
theorem resample_primitiveSum (request : PrimitiveSumRequest parents count target) (proper : AllParentsProper parents)
    (positive : 0 < ceiling) :
    (PreparedPrimitiveResampling.UniformPrimitiveNeighborhoods.PrimitiveSumRequest.resample request proper
      positive).primitiveSum = request.primitiveSum := rfl

/-- Every retained resampled child meets the positive model-error ceiling.

The original request family retains its parent order and properness witnesses. Each child belongs to the corresponding
head block or remaining tail, and its original allowance meets the same supplied ceiling. -/
theorem resample_child_error (request : PrimitiveSumRequest parents count target) (proper : AllParentsProper parents)
    (positive : 0 < ceiling) :
    ∀ child ∈ (PreparedPrimitiveResampling.UniformPrimitiveNeighborhoods.PrimitiveSumRequest.resample request proper
      positive).blocks.children, child.edge.modelErrorAllowance ≤ ceiling :=
  RequestedParents.resample_child_error request.requests proper positive

end PrimitiveSumRequest
end UniformPrimitiveNeighborhoods
end
end Purelib.Riemann.Integration.PreparedPrimitiveResampling
