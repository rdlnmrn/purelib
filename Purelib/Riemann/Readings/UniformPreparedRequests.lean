module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Integration.Polynomial.Gaussian.Path.Execution
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.Integration.UniformPreparedPrimitives
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.InverseRootPrimitive
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.List.Map
import Purelib.Data.List.Membership

public section

/-!
# Requested primitive sums on covered prepared parent lists

Every actual covered parent receives a checked primitive request.  Their
retained direct blocks form an ordinary compatible prepared refinement.  The
primitive increments are added patch by patch, with a local tolerance paying
both factors of the number of patches in the total squared-error bound.

These are local primitive increments, not a claimed single global primitive.
Identifying cut-surface boundary words with periods remains a separate task.
-/

namespace Purelib.Riemann.Readings.UniformPreparedRequests

open Purelib.Data.List

open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredSegment CoveredParents)
open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

set_option genInjectivity false in
open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
/-- An original parent's uniform patch and cached neighborhood with an exact one-eighth-target primitive request.

The request retains its actual child block, and the stored neighborhood equation and finish containment identify the
same original patch geometry. -/
structure LocalRequest (parent : CenteredEdge curve differential) (count : Nat) (target : Fraction.Rational) where
  /-- The original parent's retained uniform primitive patch. -/ patch : PreparedPatch parent
  /-- The cached original continued neighborhood at the retained differential count. -/ neighborhood :
    ContinuedInverseRoot.ContinuedNeighborhood curve.polynomial count
  /-- The cached neighborhood equals the exact retained patch neighborhood. -/ neighborhood_eq : neighborhood =
    patch.neighborhood count
  /-- The exact original primitive request at one eighth of the retained target. -/ request :
    PreparedPrimitiveRequests.Request parent neighborhood (target / 8)
  /-- The original parent finish point belongs to the retained neighborhood. -/ finishInside : neighborhood.box.Contains
    (parent.edge.point 1)

constructive_injectivity LocalRequest

namespace LocalRequest

variable {parent : CenteredEdge curve differential} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Rat in
/-- Acquire the original parent's primitive request at one eighth of the retained positive target.

The retained patch determines the cached neighborhood; its proper edge and
positive target justify the same original primitive request. -/
@[expose] def acquire (patch : PreparedPatch parent) (count : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) : LocalRequest parent count target :=
  let neighborhood := patch.neighborhood count
  { patch := patch
    neighborhood := neighborhood
    neighborhood_eq := rfl
    request := PreparedPrimitiveRequests.Request.acquire parent neighborhood (target / 8)
      (Fraction.Order.Field.div_pos_direct positive (by decide)) proper
    finishInside := finishInside }

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
/-- The original local primitive increment differs from its retained child-block integral by less than the target. -/
theorem accurate (localRequest : LocalRequest parent count target) (positive : 0 < target) :
    normSq (localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
      localRequest.request.model.primitive.value.eval (parent.edge.point 0) -
        (Basic.PathModel.mk (localRequest.request.block.children.map CenteredEdge.model)).integralSample) < target := by
  rcases localRequest with ⟨patch, neighborhood, neighborhoodEq, request, finishInside⟩
  subst neighborhood
  have bounded := UniformPreparedPrimitives.request_integral_error_lt patch request
    (Fraction.Order.Field.div_pos_direct positive (by decide)) finishInside
  have paid : 8 * (target / 8) = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact bounded.trans_eq paid

end LocalRequest

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- A dependent ordered bank of original per-parent primitive requests.

Every cached request retains the corresponding original centered parent as its index, preserving the entire original
parent list. -/
inductive RequestedParents (count : Nat) (target : Fraction.Rational) : List (CenteredEdge curve differential) → Type 2
  /-- The empty original parent list carries no retained requests. -/ | nil : RequestedParents count target []
  /-- Retain the exact original head request and dependent ordered tail bank. -/ | cons {parent : CenteredEdge curve
    differential} {remaining : List (CenteredEdge curve differential)}
      (request : LocalRequest parent count target)
      (tail : RequestedParents count target remaining) : RequestedParents count target (parent :: remaining)

constructive_injectivity RequestedParents

namespace RequestedParents

variable {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
/-- Acquire the original ordered per-parent requests from retained patch coverage and parent properness.

Each request consumes the exact original patch and its endpoint evidence, while the dependent tail preserves the
remaining original parent list. -/
@[expose] def acquire {parents : List (CenteredEdge curve differential)} (covered :
  Observation.UniformPreparedMesh.CoveredParents count parents)
    (target : Fraction.Rational) (positive : 0 < target) (proper : AllParentsProper parents) :
    RequestedParents count target parents :=
  match covered with
  | .nil => .nil
  | .cons patch finishInside tail =>
      .cons (LocalRequest.acquire patch count target positive finishInside proper.1)
        (acquire tail target positive proper.2)
termination_by structural covered

/-- Read the exact original child blocks as a refinement of the retained parent list.

Structural readback retains each request's original child block and the
ordered dependent tail. -/
@[expose] def blocks : {parents : List (CenteredEdge curve differential)} →
    RequestedParents count target parents → DirectBlockRefinement parents
  | _, .nil => .nil
  | _, .cons localRequest tail => .cons localRequest.request.block tail.blocks

/-- Read the original primitive endpoint increments in retained parent order.

Each retained parent contributes its cached polynomial's finish reading
minus its start reading, in the original list order. -/
@[expose] def increments : {parents : List (CenteredEdge curve differential)} →
    RequestedParents count target parents → List Gaussian
  | _, .nil => []
  | parent :: _, .cons localRequest tail =>
      (localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
        localRequest.request.model.primitive.value.eval (parent.edge.point 0)) :: tail.increments

open Purelib.Riemann.Normalization in
/-- Read the original retained primitive polynomials in parent order.

Structural readback follows the original request bank and returns each
exact cached model polynomial. -/
@[expose] def primitiveValues : {parents : List (CenteredEdge curve differential)} →
    RequestedParents count target parents → List InverseRootPolynomial.Polynomial
  | _, .nil => []
  | _, .cons request tail => request.request.model.primitive.value :: tail.primitiveValues

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read each original primitive increment minus its exact retained child-block integral.

Every entry uses the same retained polynomial, endpoint readings and
child block as its original parent request. -/
@[expose] def errors : {parents : List (CenteredEdge curve differential)} →
    RequestedParents count target parents → List Gaussian
  | _, .nil => []
  | parent :: _, .cons localRequest tail =>
      (localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
        localRequest.request.model.primitive.value.eval (parent.edge.point 0) -
          (Basic.PathModel.mk (localRequest.request.block.children.map CenteredEdge.model)).integralSample) ::
            tail.errors

/-- The retained error list has exactly one entry per original parent. -/
theorem errors_length {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) : requests.errors.length = parents.length := by
  induction requests with
  | nil => rfl
  | cons localRequest tail ih => exact congrArg Nat.succ ih

/-- The retained primitive increment list has exactly one entry per original parent. -/
theorem increments_length {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) : requests.increments.length = parents.length := by
  induction requests with
  | nil => rfl
  | cons localRequest tail ih => exact congrArg Nat.succ ih

/-- Every retained original per-parent error meets the common positive target. -/
theorem errors_bounded {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target) :
    ∀ error ∈ requests.errors, normSq error ≤ target := by
  induction requests with
  | nil => intro error member; cases member
  | cons localRequest tail ih =>
      intro error member
      rcases Membership.mem_cons.mp member with rfl | member
      · exact (localRequest.accurate positive).le
      · exact ih error member

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained error sum equals the original primitive sum minus the exact flattened refinement integral. -/
theorem errors_sum {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.errors = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      requests.increments -
      (Basic.PathModel.mk (requests.blocks.children.map CenteredEdge.model)).integralSample := by
  induction requests with
  | nil => change (0 : Gaussian) = 0 - 0; ring1
  | cons localRequest tail ih =>
      simp only [errors, increments, Data.Gaussian.Norm.Sum.Basic.gaussianSum, blocks, DirectBlockRefinement.children,
        Map.map_append, Basic.PathModel.integralSample_mk_append]
      rw [ih]
      ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained total integral error is bounded by the original squared parent count times the local target. -/
theorem integral_error_le {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target) :
    normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments -
      (Basic.PathModel.mk (requests.blocks.children.map CenteredEdge.model)).integralSample) ≤
        (parents.length : Fraction.Rational) * ((parents.length : Fraction.Rational) * target) := by
  rw [← requests.errors_sum]
  have bounded := Norm.Sum.Bounds.normSq_sum_le requests.errors target
    (fun value member => by
      have scalar := requests.errors_bounded positive value member
      simpa only [Norm.Basic.normSq_eq_canonical] using scalar)
  rw [requests.errors_length] at bounded
  simpa only [Norm.Basic.normSq_eq_canonical] using bounded

end RequestedParents

set_option genInjectivity false in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Cached original per-parent requests, child blocks, increments and paid aggregate integral readbacks.

The local target retains its exact count-dependent budget equation, and every output cache reads from the same retained
original request bank. -/
structure PrimitiveSumRequest (parents : List (CenteredEdge curve differential)) (count : Nat) (target :
  Fraction.Rational) where
  /-- The original total target is strictly positive. -/ target_positive : 0 < target
  /-- The retained positive per-parent error allowance. -/ localTarget : Fraction.Rational
  /-- The local allowance equals the exact original count-dependent aggregate budget. -/ localTarget_eq : localTarget =
    Budget.Aggregate.perTerm target parents.length
  /-- The retained local error allowance is strictly positive. -/ localTarget_positive : 0 < localTarget
  /-- The original dependent request bank at the exact retained local target. -/ requests : RequestedParents count
    localTarget parents
  /-- The cached exact original child-block refinement. -/ blocks : DirectBlockRefinement parents
  /-- The child-block cache equals the readback of the retained original request bank. -/ blocks_eq : blocks =
    requests.blocks
  /-- The cached ordered original primitive increments. -/ increments : List Gaussian
  /-- The increment cache equals the exact retained request-bank readback. -/ increments_eq : increments =
    requests.increments
  /-- The cached finite sum of the original retained increments. -/ primitiveSum : Gaussian
  /-- The sum cache equals the exact finite Gaussian sum of stored increments. -/ primitiveSum_eq : primitiveSum =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum increments
  /-- The cached integral of the exact retained flattened child models. -/ integralSample : Gaussian
  /-- The integral cache equals the original path integral of the stored child-block refinement. -/ integralSample_eq :
    integralSample = (Basic.PathModel.mk (blocks.children.map CenteredEdge.model)).integralSample

constructive_injectivity PrimitiveSumRequest

namespace PrimitiveSumRequest

variable {parents : List (CenteredEdge curve differential)} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Assemble the aggregate caches from the supplied original checked per-parent requests.

The exact stored blocks determine the retained path integral, while their original primitive increments determine the
cached sum under the same count-dependent target. -/
@[expose] def ofRequests (parents : List (CenteredEdge curve differential))
    (target : Fraction.Rational) (positive : 0 < target)
    (requests : RequestedParents count (Budget.Aggregate.perTerm target parents.length) parents) :
    PrimitiveSumRequest parents count target :=
  let localTarget := Budget.Aggregate.perTerm target parents.length
  have localPositive := Budget.Aggregate.perTerm_positive positive parents.length
  let blocks := requests.blocks
  let increments := requests.increments
  let path := Basic.PathModel.mk (blocks.children.map CenteredEdge.model)
  { target_positive := positive
    localTarget := localTarget
    localTarget_eq := rfl
    localTarget_positive := localPositive
    requests := requests
    blocks := blocks
    blocks_eq := rfl
    increments := increments
    increments_eq := rfl
    primitiveSum := Data.Gaussian.Norm.Sum.Basic.gaussianSum increments
    primitiveSum_eq := rfl
    integralSample := path.tailIntegralSample
    integralSample_eq := path.integralSample_eq_tailIntegralSample.symm }

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
/-- Acquire the original covered parent bank at the count-dependent local target and cache its paid aggregate readbacks.

The supplied coverage and properness evidence build requests at the exact
per-term budget, then retain their original aggregate caches. -/
@[expose] def acquire (covered : Observation.UniformPreparedMesh.CoveredParents count parents) (proper :
  AllParentsProper parents)
    (target : Fraction.Rational) (positive : 0 < target) : PrimitiveSumRequest parents count target :=
  ofRequests parents target positive
    (RequestedParents.acquire covered _
      (Budget.Aggregate.perTerm_positive positive parents.length) proper)

open Purelib.Approximation.Rational in
/-- The exact cached primitive sum differs from the retained flattened path integral by less than the original total
target.

The count-dependent local allowance pays both original parent-count factors in the finite squared-norm estimate. -/
theorem accurate (request : PrimitiveSumRequest parents count target) :
    normSq (request.primitiveSum - request.integralSample) < target := by
  rw [request.primitiveSum_eq, request.integralSample_eq, request.increments_eq, request.blocks_eq]
  have bounded := request.requests.integral_error_le request.localTarget_positive
  have paid := Budget.Aggregate.count_mul_perTerm_lt request.target_positive parents.length
  rw [← request.localTarget_eq] at paid
  exact bounded.trans_lt paid

/-- Read the exact cached child blocks as compatible refinements of the original parent list. -/
@[expose] def compatible (request : PrimitiveSumRequest parents count target) := request.blocks.toCompatible

open Purelib.Geometry.Path.Gaussian in
open Purelib.Riemann.Integration in
/-- Transport the original connected parent chain through the exact retained child blocks. -/
@[expose] def chain (request : PrimitiveSumRequest parents count target) {start finish : Lifted.Basic.LiftedPoint 2}
    (parentsChain : PreparedDirectDyadicRefinements.CenteredPathChain parents (start := start) (finish := finish)) :=
  request.blocks.refinedChain parentsChain.toDirectPathChain

end PrimitiveSumRequest

end Purelib.Riemann.Readings.UniformPreparedRequests
