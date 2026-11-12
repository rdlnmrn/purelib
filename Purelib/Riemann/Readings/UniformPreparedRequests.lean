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
public import Purelib.Riemann.Integration.ContinuedPrimitiveOverlap
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap

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
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Riemann.Paths.PreparedPrimitivePaths
public import Purelib.Data.List.DependentProduct
import Purelib.Data.Fin.Fold.Max

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
    Request parent neighborhood (target / 8)
  /-- The original parent finish point belongs to the retained neighborhood. -/ finishInside : neighborhood.box.Contains
    (parent.edge.point 1)

constructive_injectivity LocalRequest

namespace LocalRequest

variable {parent : CenteredEdge curve differential} {target : Data.Rat.Fraction.Rational}

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
    request := Request.acquire parent neighborhood (target / 8)
      (Fraction.Order.Field.div_pos_direct positive (by decide)) proper
    finishInside := finishInside }

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
/-- The original local primitive increment differs from its retained child-block integral by less than the target. -/
theorem accurate (localRequest : LocalRequest parent count target) (positive : 0 < target) :
    normSq (localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
      localRequest.request.model.primitive.value.eval (parent.edge.point 0) -
        (PathModel.mk (localRequest.request.block.children.map CenteredEdge.model)).integralSample) < target := by
  rcases localRequest with ⟨patch, neighborhood, neighborhoodEq, request, finishInside⟩
  subst neighborhood
  have bounded := UniformPreparedPrimitives.request_integral_error_lt patch request
    (Fraction.Order.Field.div_pos_direct positive (by decide)) finishInside
  have paid : 8 * (target / 8) = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact bounded.trans_eq paid

section

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairGeometry PrimitivePairBudget)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Integration

/-- The exact original source coordinate belongs to the retained request neighborhood.

The cached whole neighborhood equation transports the original patch's
source containment; no observation, seed or parent is acquired again.
-/
theorem source_inside (localRequest : LocalRequest parent count target) :
    localRequest.neighborhood.box.Contains (parent.edge.segment.pointAt parent.edge.left.parameter) := by
  rewrite [localRequest.neighborhood_eq]
  have inside := localRequest.patch.start_inside count
  rewrite [parent.edge.point_zero] at inside
  exact inside

/-- Retain the primitive-pair geometry on the exact local request and supplied common neighborhood.

The local endpoints are certified by the request itself. The two common
containments refer to those same ordered coordinates, and the original pair
budget caches their actual mismatch scale once.
-/
@[expose] def pairGeometry (localRequest : LocalRequest parent count target)
    {commonCount : Nat} (common : ContinuedInverseRoot.ContinuedNeighborhood curve.polynomial commonCount)
    (startInside : common.box.Contains (parent.edge.segment.pointAt parent.edge.left.parameter))
    (finishInside : common.box.Contains (parent.edge.point 1)) :
    PrimitivePairGeometry localRequest.neighborhood common (differentialNumerator differential)
      (parent.edge.segment.pointAt parent.edge.left.parameter) (parent.edge.point 1) where
  leftStart := localRequest.source_inside
  leftFinish := localRequest.finishInside
  rightStart := startInside
  rightFinish := finishInside
  budget := PrimitivePairBudget.build localRequest.neighborhood common (differentialNumerator differential)
    (parent.edge.segment.pointAt parent.edge.left.parameter) (parent.edge.point 1)

/-- The retained local and common primitive increments obey their exact original pair budget on the same sheet.

The supplied common Point retains the original parent's signed root link.
The original source-to-query and uniform-patch bridges then prove the
unflipped transition. Auxiliary Point and preparation comparisons occur only
inside this proof and erase; the actual two cached primitive polynomials,
parents, neighborhoods and independent indices are unchanged.
-/
theorem increment_mismatch_le (localRequest : LocalRequest parent count target)
    {commonCount commonIndex : Nat}
    {common : ContinuedInverseRoot.ContinuedNeighborhood curve.polynomial commonCount}
    (geometry : PrimitivePairGeometry localRequest.neighborhood common (differentialNumerator differential)
      (parent.edge.segment.pointAt parent.edge.left.parameter) (parent.edge.point 1))
    (sample : Point common (parent.edge.segment.pointAt parent.edge.left.parameter))
    (related : NamedEquivalent (parent.edge.owner.certificate parent.edge.owner.parameterNonzero).value.name
      sample.certificate.value.name)
    (model : PrimitiveModel common commonIndex (differentialNumerator differential))
    (index : Nat) (localLater : index ≤ localRequest.request.index) (commonLater : index ≤ commonIndex) :
    normSq (localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
      localRequest.request.model.primitive.value.eval (parent.edge.segment.pointAt parent.edge.left.parameter) +
      (model.primitive.value.eval (parent.edge.segment.pointAt parent.edge.left.parameter) -
        model.primitive.value.eval (parent.edge.point 1))) ≤
      Approximation.Rational.Geometric.Basic.quarterRadius geometry.budget.scale index := by
  let localPoint := Point.acquire localRequest.neighborhood
    (parent.edge.segment.pointAt parent.edge.left.parameter) geometry.leftStart
  let aligned := Point.castPatch localRequest.neighborhood_eq.symm localPoint
  have alignedInside : (localRequest.patch.neighborhood count).box.Contains
      (parent.edge.segment.pointAt parent.edge.left.parameter) := by
    rewrite [← localRequest.neighborhood_eq]
    exact geometry.leftStart
  let queryToLocal := localRequest.patch.point_equivalent_at count 0 parent.edge.baseInside
    parent.edge.point_zero alignedInside aligned
  have localName : aligned.certificate.value.name = localPoint.certificate.value.name :=
    Point.castPatch_name localRequest.neighborhood_eq.symm localPoint
  let sourceToQuery := PreparedConstantModels.PreparedEdge.ownerRootEquivalent_baseQuery parent.edge
  have sourceToLocal : NamedEquivalent
      (parent.edge.owner.certificate parent.edge.owner.parameterNonzero).value.name
      localPoint.certificate.value.name := by
    rewrite [← localName]
    exact sourceToQuery.trans queryToLocal
  let roots := sourceToLocal.symm.trans related
  let edge := EdgeTransition.ofEquivalentPoints localPoint sample geometry.leftStart geometry.leftFinish
    geometry.rightStart geometry.rightFinish roots localRequest.request.index commonIndex
    (localRequest.neighborhood.base.refine localRequest.request.index) (common.base.refine commonIndex) rfl rfl
  exact geometry.budget.increment_le localRequest.request.model model edge rfl index localLater commonLater

/-- Refine the same local request to a model floor, returning every already adequate local cache literally.

The retained patch, neighborhood equation and endpoint containment are
unchanged. Only an insufficient inner request invokes original Request.refine;
its same numerator bound and actual neighborhood determine the later model.
-/
@[expose] def refine (localRequest : LocalRequest parent count target) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (minimum : Nat) :
    LocalRequest parent count target :=
  if adequate : minimum ≤ localRequest.request.index then localRequest
  else
    { localRequest with
      request := localRequest.request.refine (Fraction.Order.Field.div_pos_direct positive (by decide)) proper minimum }

/-- An already sufficient floor preserves the whole original local request and all original fields. -/
theorem refine_of_ge (localRequest : LocalRequest parent count target) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (minimum : Nat)
    (adequate : minimum ≤ localRequest.request.index) : localRequest.refine positive proper minimum = localRequest := by
  unfold refine
  rewrite [dif_pos adequate]
  rfl

/-- An insufficient local request retains all original outer caches around the exact original inner refinement. -/
theorem refine_of_lt (localRequest : LocalRequest parent count target) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (minimum : Nat)
    (insufficient : localRequest.request.index < minimum) :
    localRequest.refine positive proper minimum =
      { localRequest with
        request := localRequest.request.refine (Fraction.Order.Field.div_pos_direct positive (by decide)) proper
          minimum } := by
  unfold refine
  rewrite [dif_neg (Nat.not_le_of_lt insufficient)]
  rfl

/-- A zero floor returns the literal whole original local request. -/
theorem refine_zero (localRequest : LocalRequest parent count target) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) :
    localRequest.refine positive proper 0 = localRequest :=
  localRequest.refine_of_ge positive proper 0 (Nat.zero_le _)

/-- The actual refined local request meets the selected floor without changing its parent or neighborhood. -/
theorem refine_index_ge (localRequest : LocalRequest parent count target) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (minimum : Nat) :
    minimum ≤ (localRequest.refine positive proper minimum).request.index := by
  by_cases adequate : minimum ≤ localRequest.request.index
  · rewrite [localRequest.refine_of_ge positive proper minimum adequate]
    exact adequate
  · unfold refine
    rewrite [dif_neg adequate]
    exact localRequest.request.refine_index_ge (Fraction.Order.Field.div_pos_direct positive (by decide)) proper minimum

/-- The selected finite pair request is attained by the actual refined local model and any later common model.

Both original neighborhoods and the same cached pair budget are retained.
The necessary local refinement is constructed internally from the selected
stage; no successful lower-index or accuracy claim is an additional premise.
-/
theorem refine_increment_mismatch_lt (localRequest : LocalRequest parent count target) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    {commonCount commonIndex : Nat}
    {common : ContinuedInverseRoot.ContinuedNeighborhood curve.polynomial commonCount}
    (geometry : PrimitivePairGeometry localRequest.neighborhood common (differentialNumerator differential)
      (parent.edge.segment.pointAt parent.edge.left.parameter) (parent.edge.point 1))
    (sample : Point common (parent.edge.segment.pointAt parent.edge.left.parameter))
    (related : NamedEquivalent (parent.edge.owner.certificate parent.edge.owner.parameterNonzero).value.name
      sample.certificate.value.name)
    {current : Nat} {tolerance : Fraction.Rational}
    (selection : Approximation.Rational.Geometric.Search.Selection geometry.budget.scale current tolerance)
    (model : PrimitiveModel common commonIndex (differentialNumerator differential))
    (commonLater : selection.stage ≤ commonIndex)
    (floor : {minimum : Nat // selection.stage ≤ minimum} := ⟨selection.stage, Nat.le_refl _⟩) :
    let refined := localRequest.refine positive proper floor.val
    normSq (refined.request.model.primitive.value.eval (parent.edge.point 1) -
      refined.request.model.primitive.value.eval (parent.edge.segment.pointAt parent.edge.left.parameter) +
      (model.primitive.value.eval (parent.edge.segment.pointAt parent.edge.left.parameter) -
        model.primitive.value.eval (parent.edge.point 1))) < tolerance := by
  dsimp only
  by_cases adequate : floor.val ≤ localRequest.request.index
  · rewrite [localRequest.refine_of_ge positive proper floor.val adequate]
    have bound := localRequest.increment_mismatch_le geometry sample related model selection.stage
      (floor.property.trans adequate) commonLater
    exact bound.trans_lt (selection.allowance_eq.symm.trans_lt selection.accurate)
  · rewrite [localRequest.refine_of_lt positive proper floor.val (Nat.lt_of_not_ge adequate)]
    let refined : LocalRequest parent count target :=
      { localRequest with
        request := localRequest.request.refine (Fraction.Order.Field.div_pos_direct positive (by decide)) proper
          floor.val }
    have bound := refined.increment_mismatch_le geometry sample related model selection.stage
      (floor.property.trans (localRequest.request.refine_index_ge
        (Fraction.Order.Field.div_pos_direct positive (by decide)) proper floor.val)) commonLater
    exact bound.trans_lt (selection.allowance_eq.symm.trans_lt selection.accurate)

/-- Pay a new local target using the same actual patch, neighborhood and original parent.

An unchanged target delegates the original whole-cache refinement. A changed
target delegates the retained inner request's precise one-eighth payment;
all original outer geometric and endpoint caches remain unchanged.
-/
def retarget (localRequest : LocalRequest parent count target) (next : Fraction.Rational)
    (positive : 0 < next) (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (minimum : Nat := 0) : LocalRequest parent count next :=
  if same : next = target then
    Eq.mp (congrArg (LocalRequest parent count) same.symm)
      (localRequest.refine (same ▸ positive) proper minimum)
  else
    { patch := localRequest.patch
      neighborhood := localRequest.neighborhood
      neighborhood_eq := localRequest.neighborhood_eq
      request := localRequest.request.retarget (next / 8)
        (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) proper minimum
      finishInside := localRequest.finishInside }

/-- The original local target preserves the complete original refinement procedure and retained branches. -/
theorem retarget_self (localRequest : LocalRequest parent count target) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (minimum : Nat := 0) :
    localRequest.retarget target positive proper minimum = localRequest.refine positive proper minimum := by
  unfold retarget
  rewrite [dif_pos rfl]
  rfl

/-- The unchanged local target and zero floor preserve the same whole original local request. -/
theorem retarget_self_zero (localRequest : LocalRequest parent count target) (positive : 0 < target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) :
    localRequest.retarget target positive proper = localRequest :=
  (localRequest.retarget_self positive proper).trans (localRequest.refine_zero positive proper)

/-- Every retargeted local request attains the requested primitive-index floor. -/
theorem retarget_index_ge (localRequest : LocalRequest parent count target) (next : Fraction.Rational)
    (positive : 0 < next) (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (minimum : Nat := 0) : minimum ≤ (localRequest.retarget next positive proper minimum).request.index := by
  by_cases same : next = target
  · subst next
    rewrite [localRequest.retarget_self positive proper minimum]
    exact localRequest.refine_index_ge positive proper minimum
  · unfold retarget
    rewrite [dif_neg same]
    exact localRequest.request.retarget_index_ge (next / 8)
      (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) proper minimum

/-- Every retargeted local request retains the exact original neighborhood and its root/source owner caches. -/
theorem retarget_neighborhood (localRequest : LocalRequest parent count target) (next : Fraction.Rational)
    (positive : 0 < next) (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (minimum : Nat := 0) : (localRequest.retarget next positive proper minimum).neighborhood =
      localRequest.neighborhood := by
  by_cases same : next = target
  · subst next
    rewrite [localRequest.retarget_self positive proper minimum]
    unfold refine
    split <;> rfl
  · unfold retarget
    rewrite [dif_neg same]
    rfl

/-- Sufficient actual inner payments preserve the complete child block and exact cached primitive polynomial.

The same-target case keeps the original whole local request. The changed
case consumes the exact original request's retained-cache equality, while
preserving the same outer patch and neighborhood owners.
-/
theorem retarget_readbacks_of_cachePays (localRequest : LocalRequest parent count target)
    (next : Fraction.Rational) (positive : 0 < next)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (minimum : Nat)
    (paid : localRequest.request.cachePays (next / 8) minimum) :
    (localRequest.retarget next positive proper minimum).request.block = localRequest.request.block ∧
    (localRequest.retarget next positive proper minimum).request.model.primitive.value =
      localRequest.request.model.primitive.value := by
  by_cases same : next = target
  · subst next
    rewrite [localRequest.retarget_self positive proper minimum,
      localRequest.refine_of_ge positive proper minimum paid.1]
    exact ⟨rfl, rfl⟩
  · unfold retarget
    rewrite [dif_neg same]
    dsimp only
    rewrite [localRequest.request.retarget_of_cachePays (next / 8)
      (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) proper minimum paid]
    exact ⟨rfl, rfl⟩

/-- Retargeting an actually paid local cache preserves any stricter payment already satisfied by the same data. -/
theorem cachePays_retarget (localRequest : LocalRequest parent count target) (next : Fraction.Rational)
    (positive : 0 < next) (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (minimum : Nat) (paid : localRequest.request.cachePays (next / 8) minimum)
    (future : Fraction.Rational) (floor : Nat) (futurePaid : localRequest.request.cachePays future floor) :
    (localRequest.retarget next positive proper minimum).request.cachePays future floor := by
  by_cases same : next = target
  · subst next
    rewrite [localRequest.retarget_self positive proper minimum,
      localRequest.refine_of_ge positive proper minimum paid.1]
    exact futurePaid
  · unfold retarget
    rewrite [dif_neg same]
    exact localRequest.request.cachePays_retarget (next / 8)
      (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) proper minimum paid future floor futurePaid

end

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

variable {target : Data.Rat.Fraction.Rational}

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
/-- Acquire the original ordered per-parent requests from retained patch coverage and parent properness.

Each request consumes the exact original patch and its endpoint evidence, while the dependent tail preserves the
remaining original parent list. -/
@[expose] def acquire {parents : List (CenteredEdge curve differential)} (covered :
  CoveredParents count parents)
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
          (PathModel.mk (localRequest.request.block.children.map CenteredEdge.model)).integralSample) ::
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
    gaussianSum requests.errors = gaussianSum
      requests.increments -
      (PathModel.mk (requests.blocks.children.map CenteredEdge.model)).integralSample := by
  induction requests with
  | nil => change (0 : Gaussian) = 0 - 0; ring1
  | cons localRequest tail ih =>
      simp only [errors, increments, gaussianSum, blocks, DirectBlockRefinement.children,
        Map.map_append, PathModel.integralSample_mk_append]
      rw [ih]
      ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained total integral error is bounded by the original squared parent count times the local target. -/
theorem integral_error_le {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target) :
    normSq (gaussianSum requests.increments -
      (PathModel.mk (requests.blocks.children.map CenteredEdge.model)).integralSample) ≤
        (parents.length : Fraction.Rational) * ((parents.length : Fraction.Rational) * target) := by
  rw [← requests.errors_sum]
  have bounded := Norm.Sum.Bounds.normSq_sum_le requests.errors target
    (fun value member => by
      have scalar := requests.errors_bounded positive value member
      simpa only [Norm.Basic.normSq_eq_canonical] using scalar)
  rw [requests.errors_length] at bounded
  simpa only [Norm.Basic.normSq_eq_canonical] using bounded

section Refinement

/-- Read the whole original local request at its bounded original parent occurrence. -/
@[expose] def get : {parents : List (CenteredEdge curve differential)} →
    RequestedParents count target parents → (index : Fin parents.length) →
      LocalRequest (parents[index.val]'index.isLt) count target
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons head tail, index => Fin.cases head (fun index => tail.get index) index

/-- Lookup at the original first occurrence returns the same whole cached request. -/
theorem get_cons_zero {parent : CenteredEdge curve differential} {parents : List (CenteredEdge curve differential)}
    (head : LocalRequest parent count target) (tail : RequestedParents count target parents) :
    (cons head tail).get 0 = head := rfl

/-- Lookup after the first occurrence reads the literal original request-bank tail. -/
theorem get_cons_succ {parent : CenteredEdge curve differential} {parents : List (CenteredEdge curve differential)}
    (head : LocalRequest parent count target) (tail : RequestedParents count target parents)
    (index : Fin parents.length) : (cons head tail).get index.succ = tail.get index := rfl

/-- Split an original ordered request bank at its exact retained parent-list boundary.

The prefix retains each original whole local request, and the suffix is the
literal original dependent tail. No model, observation, child block or
primitive value is rebuilt.
-/
def split : (first second : List (CenteredEdge curve differential)) →
    RequestedParents count target (first ++ second) →
      RequestedParents count target first × RequestedParents count target second
  | [], _, requests => ⟨.nil, requests⟩
  | _ :: first, second, .cons head tail =>
      let remaining := split first second tail
      ⟨.cons head remaining.1, remaining.2⟩

/-- An empty prefix returns the literal supplied whole request bank as its suffix. -/
theorem split_nil (parents : List (CenteredEdge curve differential))
    (requests : RequestedParents count target parents) : split [] parents requests = ⟨.nil, requests⟩ := (rfl)

/-- Splitting after an original head retains that whole request and splits only its literal tail. -/
theorem split_cons (parent : CenteredEdge curve differential) (first second : List (CenteredEdge curve differential))
    (head : LocalRequest parent count target) (tail : RequestedParents count target (first ++ second)) :
    split (parent :: first) second (.cons head tail) =
      ⟨.cons head (split first second tail).1, (split first second tail).2⟩ := (rfl)

/-- Every split prefix occurrence retains its complete original request at the original bounded embedding.

The existing dependent-product index embedding preserves the actual
ordinal. Heterogeneous equality retains the original parent-indexed request
without replacing either parent or transporting its numerical cache.
-/
theorem get_split_left : (first second : List (CenteredEdge curve differential)) →
    (requests : RequestedParents count target (first ++ second)) → (index : Fin first.length) →
    HEq ((split first second requests).1.get index) (requests.get (DependentProduct.leftIndex first second index))
  | [], _, _, index => Fin.elim0 index
  | _ :: first, second, .cons head tail, index => by
      refine Fin.cases (HEq.refl head) ?_ index
      intro remaining
      exact get_split_left first second tail remaining

/-- Every split suffix occurrence reads the same whole original request after the actual retained prefix.

The right embedding reuses the existing bounded ordinal operation. The
literal suffix and all original parent, neighborhood, model and block data
are retained rather than reconstructed from equal scalar readings.
-/
theorem get_split_right : (first second : List (CenteredEdge curve differential)) →
    (requests : RequestedParents count target (first ++ second)) → (index : Fin second.length) →
    HEq ((split first second requests).2.get index) (requests.get (DependentProduct.rightIndex first second index))
  | [], _, requests, index => HEq.refl (requests.get index)
  | _ :: first, second, .cons _ tail, index => get_split_right first second tail index

/-- The split requests retain the exact original ordered primitive-increment list. -/
theorem increments_split (first second : List (CenteredEdge curve differential))
    (requests : RequestedParents count target (first ++ second)) :
    requests.increments = (split first second requests).1.increments ++ (split first second requests).2.increments := by
  induction first with
  | nil => rfl
  | cons parent first ih =>
      cases requests with
      | cons head tail =>
          change _ :: tail.increments = _ :: _
          exact congrArg (fun values => _ :: values) (ih tail)

/-- The split requests retain the original ordered primitive-polynomial cache list. -/
theorem primitiveValues_split (first second : List (CenteredEdge curve differential))
    (requests : RequestedParents count target (first ++ second)) :
    requests.primitiveValues = (split first second requests).1.primitiveValues ++
      (split first second requests).2.primitiveValues := by
  induction first with
  | nil => rfl
  | cons parent first ih =>
      cases requests with
      | cons head tail =>
          change _ :: tail.primitiveValues = _ :: _
          exact congrArg (fun values => _ :: values) (ih tail)

/-- The split requests retain every original child block and its ordered child-edge list. -/
theorem children_split (first second : List (CenteredEdge curve differential))
    (requests : RequestedParents count target (first ++ second)) :
    requests.blocks.children = (split first second requests).1.blocks.children ++
      (split first second requests).2.blocks.children := by
  induction first with
  | nil => rfl
  | cons parent first ih =>
      cases requests with
      | cons head tail =>
          change head.request.block.children ++ tail.blocks.children =
            (head.request.block.children ++ (split first second tail).1.blocks.children) ++
              (split first second tail).2.blocks.children
          rewrite [ih tail]
          exact (Append.append_assoc _ _ _).symm

/-- Compute only changed original request spines, using none for the identical unchanged bank.

Heads are inspected and any necessary model refinement is performed before
the original tail is visited. Unchanged heads and tails are retained
literally; a changed result uses the same original dependent cons constructor.
-/
private def refine? {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target)
    (proper : AllParentsProper parents) (minimum : Nat) : Option (RequestedParents count target parents) :=
  match requests with
  | .nil => none
  | .cons head tail =>
      let selected := if minimum ≤ head.request.index then none else some (head.refine positive proper.1 minimum)
      let remaining := refine? tail positive proper.2 minimum
      match selected, remaining with
      | none, none => none
      | none, some updated => some (.cons head updated)
      | some updated, none => some (.cons updated tail)
      | some updated, some rest => some (.cons updated rest)
termination_by structural requests

/-- Refine the supplied ordered request bank while retaining every already sufficient entry and unchanged tail.

An entirely adequate bank is returned as the literal original value. Only
necessary later primitive models and their actual child blocks are built;
there is no cover, seed, source or center re-acquisition.
-/
def refine {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target)
    (proper : AllParentsProper parents) (minimum : Nat) : RequestedParents count target parents :=
  (refine? requests positive proper minimum).getD requests

/-- An original cons refines to its same whole head operation followed by its same whole tail operation. -/
theorem refine_cons {parent : CenteredEdge curve differential} {parents : List (CenteredEdge curve differential)}
    (head : LocalRequest parent count target) (tail : RequestedParents count target parents) (positive : 0 < target)
    (proper : AllParentsProper (parent :: parents)) (minimum : Nat) :
    (cons head tail).refine positive proper minimum =
      cons (head.refine positive proper.1 minimum) (tail.refine positive proper.2 minimum) := by
  by_cases adequate : minimum ≤ head.request.index
  · have same := head.refine_of_ge positive proper.1 minimum adequate
    cases remaining : refine? tail positive proper.2 minimum <;>
      (simp only [refine, refine?, if_pos adequate, remaining, Option.getD, same,
        -eq_self, -iff_self]; rfl)
  · cases remaining : refine? tail positive proper.2 minimum <;>
      (simp only [refine, refine?, if_neg adequate, remaining, Option.getD,
        -eq_self, -iff_self]; rfl)

/-- Splitting and refining preserve the same complete original prefix and suffix operations.

Both sides use the one supplied global floor. The existing whole-bank
refinement retains its adequate entries and literal unchanged tails; this
law does not acquire a second request bank or recompute any aggregate cache.
-/
theorem split_refine (first second : List (CenteredEdge curve differential))
    (requests : RequestedParents count target (first ++ second)) (positive : 0 < target)
    (firstProper : AllParentsProper first) (secondProper : AllParentsProper second) (minimum : Nat) :
    split first second (requests.refine positive
      (Integration.PreparedDirectDyadicRefinements.allParentsProper_append firstProper secondProper) minimum) =
      ⟨(split first second requests).1.refine positive firstProper minimum,
        (split first second requests).2.refine positive secondProper minimum⟩ := by
  induction first with
  | nil => rfl
  | cons parent first ih =>
      cases requests with
      | cons head tail =>
          have refined := refine_cons head tail positive
            (Integration.PreparedDirectDyadicRefinements.allParentsProper_append firstProper secondProper) minimum
          refine (congrArg (split (parent :: first) second) refined).trans ?_
          change (cons (head.refine positive firstProper.1 minimum)
            (split first second (tail.refine positive
              (Integration.PreparedDirectDyadicRefinements.allParentsProper_append firstProper.2 secondProper)
                minimum)).1, _) = _
          rewrite [ih tail firstProper.2]
          exact congrArg (fun firstBank => (firstBank,
            (split first second tail).2.refine positive secondProper minimum))
              (refine_cons head (split first second tail).1 positive firstProper minimum).symm

/-- Bounded lookup consumes the original local refinement at that same original parent occurrence. -/
theorem get_refine {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target)
    (proper : AllParentsProper parents) (minimum : Nat) (index : Fin parents.length) :
    (requests.refine positive proper minimum).get index =
      (requests.get index).refine positive (AllParentsProper.get proper index) minimum := by
  induction requests with
  | nil => exact Fin.elim0 index
  | cons head tail ih =>
      rewrite [refine_cons]
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro next
        exact ih proper.2 next

/-- Every actual refined request meets the common requested model-index floor. -/
theorem refine_index_ge {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target)
    (proper : AllParentsProper parents) (minimum : Nat) (index : Fin parents.length) :
    minimum ≤ ((requests.refine positive proper minimum).get index).request.index := by
  rewrite [requests.get_refine positive proper minimum index]
  exact (requests.get index).refine_index_ge positive (AllParentsProper.get proper index) minimum

/-- An adequate original bank produces no changed spine at all. -/
private theorem refine?_none_of_ge {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target)
    (proper : AllParentsProper parents) (minimum : Nat)
    (adequate : ∀ index : Fin parents.length, minimum ≤ (requests.get index).request.index) :
    refine? requests positive proper minimum = none := by
  induction requests with
  | nil => rfl
  | cons head tail ih =>
      have first : minimum ≤ head.request.index := adequate 0
      have rest : ∀ index : Fin _, minimum ≤ (tail.get index).request.index := by
        intro index
        exact adequate index.succ
      have remaining := ih proper.2 rest
      simp only [refine?, if_pos first, remaining, -eq_self, -iff_self]
      rfl

/-- If every original entry is sufficient, refinement returns the same whole original bank. -/
theorem refine_of_ge {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target)
    (proper : AllParentsProper parents) (minimum : Nat)
    (adequate : ∀ index : Fin parents.length, minimum ≤ (requests.get index).request.index) :
    requests.refine positive proper minimum = requests := by
  unfold refine
  rewrite [refine?_none_of_ge requests positive proper minimum adequate]
  rfl

/-- Zero-floor refinement preserves the whole original request bank and every ordered tail. -/
theorem refine_zero {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target) (proper : AllParentsProper parents) :
    requests.refine positive proper 0 = requests := requests.refine_of_ge positive proper 0 (fun _ => Nat.zero_le _)

/-- Refining an insufficient head with an adequate suffix retains that literal whole original suffix. -/
theorem refine_cons_tail_of_ge {parent : CenteredEdge curve differential}
    {parents : List (CenteredEdge curve differential)} (head : LocalRequest parent count target)
    (tail : RequestedParents count target parents) (positive : 0 < target)
    (proper : AllParentsProper (parent :: parents)) (minimum : Nat)
    (adequate : ∀ index : Fin parents.length, minimum ≤ (tail.get index).request.index) :
    (cons head tail).refine positive proper minimum = cons (head.refine positive proper.1 minimum) tail := by
  rewrite [refine_cons, tail.refine_of_ge positive proper.2 minimum adequate]
  rfl

end Refinement

section TargetRefinement

open Purelib.Data.Rat

/-- Retarget the actual original request bank in order, retaining all outer parent and neighborhood ownership.

The unchanged target runs the exact original whole-bank refinement. For a
new target each same original head uses its retained model/block payment
checks before the original tail is visited; no patch or source is acquired.
-/
def retarget {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (next : Fraction.Rational) (positive : 0 < next)
    (proper : AllParentsProper parents) (minimum : Nat := 0) : RequestedParents count next parents :=
  if same : next = target then
    Eq.mp (congrArg (fun allowance => RequestedParents count allowance parents) same.symm)
      (requests.refine (same ▸ positive) proper minimum)
  else
    match requests with
    | .nil => .nil
    | .cons head tail =>
        let first := head.retarget next positive proper.1 minimum
        let remaining := tail.retarget next positive proper.2 minimum
        .cons first remaining
termination_by structural requests

/-- The original target preserves the complete original bank refinement, including literal adequate tails. -/
theorem retarget_self {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target)
    (proper : AllParentsProper parents) (minimum : Nat := 0) :
    requests.retarget target positive proper minimum = requests.refine positive proper minimum := by
  unfold retarget
  rewrite [dif_pos rfl]
  rfl

/-- The original target and zero floor return the same whole supplied original bank. -/
theorem retarget_self_zero {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (positive : 0 < target) (proper : AllParentsProper parents) :
    requests.retarget target positive proper = requests :=
  (requests.retarget_self positive proper).trans (requests.refine_zero positive proper)

/-- Retargeting preserves the actual head-before-tail order and each original local request operation. -/
theorem retarget_cons {parent : CenteredEdge curve differential} {parents : List (CenteredEdge curve differential)}
    (head : LocalRequest parent count target) (tail : RequestedParents count target parents)
    (next : Fraction.Rational) (positive : 0 < next) (proper : AllParentsProper (parent :: parents))
    (minimum : Nat := 0) :
    (cons head tail).retarget next positive proper minimum =
      cons (head.retarget next positive proper.1 minimum) (tail.retarget next positive proper.2 minimum) := by
  change parent.edge.left.parameter < parent.edge.request.endpoint.parameter ∧ AllParentsProper parents at proper
  rcases proper with ⟨firstProper, remainingProper⟩
  by_cases same : next = target
  · subst next
    rewrite [(cons head tail).retarget_self positive ⟨firstProper, remainingProper⟩ minimum,
      head.retarget_self positive firstProper minimum, tail.retarget_self positive remainingProper minimum,
      refine_cons]
    rfl
  · simp only [retarget, dif_neg same, -eq_self, -iff_self]
    rfl

/-- Bounded retarget lookup consumes the actual local request at the same original parent occurrence. -/
theorem get_retarget {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (next : Fraction.Rational) (positive : 0 < next)
    (proper : AllParentsProper parents) (minimum : Nat) (index : Fin parents.length) :
    (requests.retarget next positive proper minimum).get index =
      (requests.get index).retarget next positive (AllParentsProper.get proper index) minimum := by
  induction requests with
  | nil => exact Fin.elim0 index
  | cons head tail ih =>
      rewrite [retarget_cons head tail next positive proper minimum]
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro remaining
        exact ih proper.2 remaining

/-- Every actual retargeted bank entry attains the requested primitive-index floor. -/
theorem retarget_index_ge {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (next : Fraction.Rational) (positive : 0 < next)
    (proper : AllParentsProper parents) (minimum : Nat) (index : Fin parents.length) :
    minimum ≤ ((requests.retarget next positive proper minimum).get index).request.index := by
  rewrite [requests.get_retarget next positive proper minimum index]
  exact (requests.get index).retarget_index_ge next positive (AllParentsProper.get proper index) minimum

/-- All actual ordered request entries already pay a proposed local target and common index floor.

The recursive predicate reads precisely the stored polynomial, Taylor and
preparation payments used by each original retarget call. It does not
acquire observations, search for indices, or construct models or blocks.
-/
@[expose] def cachePays {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (next : Fraction.Rational) (minimum : Nat) : Prop :=
  match requests with
  | .nil => True
  | .cons head tail => head.request.cachePays (next / 8) minimum ∧ tail.cachePays next minimum

/-- Checking all actual retained payments is a finite scalar traversal of the same original ordered bank. -/
instance instDecidableCachePays {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (next : Fraction.Rational) (minimum : Nat) :
    Decidable (requests.cachePays next minimum) :=
  match requests with
  | .nil => isTrue trivial
  | .cons head tail =>
      match (inferInstance : Decidable (head.request.cachePays (next / 8) minimum)),
          instDecidableCachePays tail next minimum with
      | isTrue first, isTrue remaining => isTrue ⟨first, remaining⟩
      | isFalse first, _ => isFalse (fun paid => first paid.1)
      | _, isFalse remaining => isFalse (fun paid => remaining paid.2)
termination_by structural requests

/-- A weaker local target and sufficient original entry indices pay the entire original request bank. -/
theorem cachePays_of_le {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (next : Fraction.Rational) (minimum : Nat)
    (weaker : target ≤ next)
    (adequate : ∀ index : Fin parents.length, minimum ≤ (requests.get index).request.index) :
    requests.cachePays next minimum := by
  induction requests with
  | nil => trivial
  | cons head tail ih =>
      have first := head.request.cachePays_of_le (next / 8) minimum
        (Fraction.Order.Field.divide_mono weaker (by decide +kernel)) (adequate 0)
      exact ⟨first, ih (fun index => adequate index.succ)⟩

/-- Every original entry covered by the actual retained-payment predicate already attains its requested floor. -/
theorem cachePays_index_ge {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (next : Fraction.Rational) (minimum : Nat)
    (paid : requests.cachePays next minimum) (index : Fin parents.length) :
    minimum ≤ (requests.get index).request.index := by
  induction requests with
  | nil => exact Fin.elim0 index
  | cons head tail ih =>
      refine Fin.cases ?_ ?_ index
      · exact paid.1.1
      · intro remaining
        exact ih paid.2 remaining

/-- Actual sufficient payments preserve the complete original block bank and ordered primitive increments.

The existing original retarget operation is evaluated once. This proof
transports its exact block and polynomial readbacks entry by entry; it does
not replace the parent indices or obtain equality from numerical values.
-/
theorem retarget_readbacks_of_cachePays {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (next : Fraction.Rational) (positive : 0 < next)
    (proper : AllParentsProper parents) (minimum : Nat) (paid : requests.cachePays next minimum) :
    (requests.retarget next positive proper minimum).blocks = requests.blocks ∧
      (requests.retarget next positive proper minimum).increments = requests.increments := by
  induction requests with
  | nil =>
      by_cases same : next = target
      · subst next
        rewrite [retarget_self nil positive proper minimum]
        exact ⟨rfl, rfl⟩
      · unfold retarget
        rewrite [dif_neg same]
        exact ⟨rfl, rfl⟩
  | cons head tail ih =>
      rewrite [retarget_cons head tail next positive proper minimum]
      have first := head.retarget_readbacks_of_cachePays next positive proper.1 minimum paid.1
      have remaining := ih proper.2 paid.2
      constructor
      · change DirectBlockRefinement.cons _ _ = DirectBlockRefinement.cons _ _
        rewrite [first.1, remaining.1]
        rfl
      · change (_ :: _) = (_ :: _)
        rewrite [first.2, remaining.2]
        rfl

/-- Retargeting an actually paid bank preserves every further payment already satisfied by its same retained entries. -/
theorem cachePays_retarget {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (next : Fraction.Rational) (positive : 0 < next)
    (proper : AllParentsProper parents) (minimum : Nat) (paid : requests.cachePays next minimum)
    (future : Fraction.Rational) (floor : Nat) (futurePaid : requests.cachePays future floor) :
    (requests.retarget next positive proper minimum).cachePays future floor := by
  induction requests with
  | nil =>
      by_cases same : next = target
      · subst next
        rewrite [retarget_self nil positive proper minimum]
        trivial
      · unfold retarget
        rewrite [dif_neg same]
        trivial
  | cons head tail ih =>
      rewrite [retarget_cons head tail next positive proper minimum]
      exact ⟨head.cachePays_retarget next positive proper.1 minimum paid.1 (future / 8) floor futurePaid.1,
        ih proper.2 paid.2 futurePaid.2⟩

end TargetRefinement

section BoundaryComparison

open Purelib.Data.Gaussian
open Purelib.Algebra.FiniteSum
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Geometry.Path.Gaussian
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)

/-- The indexed retained request increments read back the exact original ordered Gaussian sum. -/
private theorem increments_sumFin {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) :
    Fin.sumFin (fun index : Fin parents.length =>
      (requests.get index).request.model.primitive.value.eval ((parents[index.val]'index.isLt).edge.point 1) -
      (requests.get index).request.model.primitive.value.eval ((parents[index.val]'index.isLt).edge.point 0)) =
      gaussianSum requests.increments := by
  induction requests with
  | nil => rfl
  | cons head tail ih =>
      rewrite [Fin.sumFin_succ]
      exact congrArg (fun remaining => head.request.model.primitive.value.eval _ -
        head.request.model.primitive.value.eval _ + remaining) ih

/-- Pointwise original local/common increment bounds control their actual connected boundary mismatch.

The original request bank supplies each actual polynomial, and the same
original parent chain supplies endpoint cancellation. The existing indexed
Gaussian finite-sum estimate contributes the precise squared parent count.
-/
theorem boundary_mismatch_le {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (primitive : Gaussian → Gaussian)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain parents (start := start) (finish := finish)) (allowance : Coordinate)
    (bounded : ∀ index : Fin parents.length,
      normSq ((requests.get index).request.model.primitive.value.eval
          ((parents[index.val]'index.isLt).edge.point 1) -
        (requests.get index).request.model.primitive.value.eval ((parents[index.val]'index.isLt).edge.point 0) -
        (primitive ((parents[index.val]'index.isLt).edge.point 1) -
          primitive ((parents[index.val]'index.isLt).edge.point 0))) ≤ allowance) :
    normSq (gaussianSum requests.increments - (primitive finish.coordinate - primitive start.coordinate)) ≤
      (parents.length : Coordinate) ^ 2 * allowance := by
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le
    (fun index : Fin parents.length =>
      (requests.get index).request.model.primitive.value.eval ((parents[index.val]'index.isLt).edge.point 1) -
        (requests.get index).request.model.primitive.value.eval ((parents[index.val]'index.isLt).edge.point 0) -
        (primitive ((parents[index.val]'index.isLt).edge.point 1) -
          primitive ((parents[index.val]'index.isLt).edge.point 0))) allowance
    (fun index => by
      rewrite [Norm.Basic.normSq_eq_canonical]
      exact bounded index)
  have commonEq := (Norm.Sum.Indexed.sumFin_map parents (fun parent =>
    primitive (parent.edge.point 1) - primitive (parent.edge.point 0))).trans
      (Riemann.Paths.PreparedPrimitivePaths.mapped_increment_sum primitive parents)
  rewrite [Fin.sumFin_sub, requests.increments_sumFin, commonEq,
    Riemann.Paths.PreparedPrimitivePaths.incrementSum_eq primitive chain] at estimate
  rewrite [Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate

end BoundaryComparison

section PairComparison

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.List (DependentProduct)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairGeometry)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Fin.Fold

variable {parents : List (CenteredEdge curve differential)} {commonCount : Nat}
variable {common : ContinuedNeighborhood curve.polynomial commonCount} {tolerance : Coordinate}

/-- Original pair geometries and actual finite selections retained at the same bounded request occurrences.

Each dependent entry stores one original pair budget and its computed
Selection. The original request bank determines the exact left neighborhood,
parent, numerator and endpoints; the same supplied common patch is retained.
-/
@[expose] def PairSelections (requests : RequestedParents count target parents)
    (common : ContinuedNeighborhood curve.polynomial commonCount) (tolerance : Coordinate) : Type :=
  DependentProduct parents (fun index =>
    let parent := parents[index.val]'index.isLt
    Σ geometry : PrimitivePairGeometry (requests.get index).neighborhood common (differentialNumerator differential)
      (parent.edge.segment.pointAt parent.edge.left.parameter) (parent.edge.point 1),
      Search.Selection geometry.budget.scale 0 tolerance)

/-- Materialize the original pair/selection bank once on the supplied request bank and common endpoint domains.

Every entry constructs its original pair geometry and one finite selection.
No primitive model or Point/source preparation is acquired by this bank.
-/
def pairSelections (requests : RequestedParents count target parents)
    (common : ContinuedNeighborhood curve.polynomial commonCount) (tolerance : Coordinate) (positive : 0 < tolerance)
    (inside : ∀ index : Fin parents.length,
      common.box.Contains ((parents[index.val]'index.isLt).edge.segment.pointAt
        (parents[index.val]'index.isLt).edge.left.parameter) ∧
      common.box.Contains ((parents[index.val]'index.isLt).edge.point 1)) :
    PairSelections requests common tolerance :=
  DependentProduct.ofFn parents fun index =>
    let geometry := (requests.get index).pairGeometry common (inside index).1 (inside index).2
    ⟨geometry, geometry.budget.choose 0 tolerance positive⟩

namespace PairSelections

variable {requests : RequestedParents count target parents}

/-- Read the exact retained pair geometry and finite Selection at its original bounded request occurrence. -/
@[expose] def get (selections : PairSelections requests common tolerance) (index : Fin parents.length) :=
  DependentProduct.get parents selections index

/-- Compute the finite maximum of the stages of these same retained original selections.

The maximum reads existing entries; it does not repeat any pair bound,
selection, model or root preparation. The empty bank has stage zero.
-/
def stage (selections : PairSelections requests common tolerance) : Nat :=
  Max.maxFin parents.length (fun index => (selections.get index).2.stage)

/-- Every original retained selection stage is covered by the one computed common floor. -/
theorem stage_covers (selections : PairSelections requests common tolerance) (index : Fin parents.length) :
    (selections.get index).2.stage ≤ selections.stage :=
  Max.le_maxFin (fun index => (selections.get index).2.stage) index

/-- A constructed-bank lookup is the complete original pair and its same once-computed finite selection. -/
theorem get_pairSelections (common : ContinuedNeighborhood curve.polynomial commonCount) (tolerance : Coordinate)
    (positive : 0 < tolerance)
    (inside : ∀ index : Fin parents.length,
      common.box.Contains ((parents[index.val]'index.isLt).edge.segment.pointAt
        (parents[index.val]'index.isLt).edge.left.parameter) ∧
      common.box.Contains ((parents[index.val]'index.isLt).edge.point 1)) (index : Fin parents.length) :
    (requests.pairSelections common tolerance positive inside).get index =
      let geometry := (requests.get index).pairGeometry common (inside index).1 (inside index).2
      ⟨geometry, geometry.budget.choose 0 tolerance positive⟩ := by
  unfold pairSelections get
  exact DependentProduct.get_ofFn parents _ index

/-- One actual common model and the refined ordered bank meet every retained pair's original chosen target.

The finite maximum supplies each local floor and the actual common-model
index. Each original Point and signed relation concerns its same parent;
the original refinement procedure preserves all adequate entries and tails.
-/
theorem refined_increment_lt (selections : PairSelections requests common tolerance)
    (positive : 0 < target) (proper : AllParentsProper parents)
    (index : Fin parents.length)
    (sample : Point common ((parents[index.val]'index.isLt).edge.segment.pointAt
      (parents[index.val]'index.isLt).edge.left.parameter))
    (related : NamedEquivalent
      ((parents[index.val]'index.isLt).edge.owner.certificate
        (parents[index.val]'index.isLt).edge.owner.parameterNonzero).value.name sample.certificate.value.name)
    {commonIndex : Nat} (model : PrimitiveModel common commonIndex (differentialNumerator differential))
    (commonLater : selections.stage ≤ commonIndex)
    (floor : {minimum : Nat // selections.stage ≤ minimum} := ⟨selections.stage, Nat.le_refl _⟩) :
    let actual := (requests.refine positive proper floor.val).get index
    normSq (actual.request.model.primitive.value.eval ((parents[index.val]'index.isLt).edge.point 1) -
      actual.request.model.primitive.value.eval ((parents[index.val]'index.isLt).edge.point 0) -
      (model.primitive.value.eval ((parents[index.val]'index.isLt).edge.point 1) -
        model.primitive.value.eval ((parents[index.val]'index.isLt).edge.point 0))) < tolerance := by
  dsimp only
  let retained := selections.get index
  have later := selections.stage_covers index
  have bound := (requests.get index).refine_increment_mismatch_lt positive (AllParentsProper.get proper index)
    retained.1 sample related retained.2 model (later.trans commonLater) ⟨floor.val, later.trans floor.property⟩
  rewrite [requests.get_refine positive proper floor.val index]
  rewrite [(parents[index.val]'index.isLt).edge.point_zero]
  have identity (a b c d : Gaussian) : a - b - (c - d) = a - b + (d - c) := by ring1
  rewrite [identity]
  exact bound

/-- Every retained pair's paid increment estimate bounds the refined bank's actual connected boundary mismatch.

The original finite Gaussian sum bound retains the squared original parent
count. The actual original chain performs endpoint cancellation; no new
path, shared source or root owner is introduced.
-/
theorem refined_boundary_le (selections : PairSelections requests common tolerance)
    (positive : 0 < target) (proper : AllParentsProper parents)
    (samples : (index : Fin parents.length) → Point common
      ((parents[index.val]'index.isLt).edge.segment.pointAt (parents[index.val]'index.isLt).edge.left.parameter))
    (related : ∀ index, NamedEquivalent
      ((parents[index.val]'index.isLt).edge.owner.certificate
        (parents[index.val]'index.isLt).edge.owner.parameterNonzero).value.name
      (samples index).certificate.value.name)
    {commonIndex : Nat} (model : PrimitiveModel common commonIndex (differentialNumerator differential))
    (commonLater : selections.stage ≤ commonIndex)
    {start finish : Geometry.Path.Gaussian.Lifted.Basic.LiftedPoint 2}
    (chain : Integration.PreparedDirectDyadicRefinements.DirectPathChain parents
      (start := start) (finish := finish))
    (floor : {minimum : Nat // selections.stage ≤ minimum} := ⟨selections.stage, Nat.le_refl _⟩) :
    normSq (gaussianSum (requests.refine positive proper floor.val).increments -
      (model.primitive.value.eval finish.coordinate - model.primitive.value.eval start.coordinate)) ≤
      (parents.length : Coordinate) ^ 2 * tolerance :=
  (requests.refine positive proper floor.val).boundary_mismatch_le model.primitive.value.eval chain tolerance
    (fun index => (selections.refined_increment_lt positive proper index (samples index) (related index)
      model commonLater floor).le)

end PairSelections

end PairComparison

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
    gaussianSum increments
  /-- The cached integral of the exact retained flattened child models. -/ integralSample : Gaussian
  /-- The integral cache equals the original path integral of the stored child-block refinement. -/ integralSample_eq :
    integralSample = (PathModel.mk (blocks.children.map CenteredEdge.model)).integralSample

constructive_injectivity PrimitiveSumRequest

namespace PrimitiveSumRequest

variable {parents : List (CenteredEdge curve differential)} {target : Data.Rat.Fraction.Rational}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Assemble aggregate caches from the actual supplied local target and original ordered request bank.

The exact target equation and positivity are retained unchanged. Each new
aggregate block, increment and integral reads the same actual requests;
no per-term target or local primitive is acquired again.
-/
@[expose] def ofLocalRequests (parents : List (CenteredEdge curve differential))
    (target : Fraction.Rational) (positive : 0 < target) (localTarget : Fraction.Rational)
    (localEq : localTarget = Approximation.Rational.Budget.Aggregate.perTerm target parents.length)
    (localPositive : 0 < localTarget) (requests : RequestedParents count localTarget parents) :
    PrimitiveSumRequest parents count target :=
  let blocks := requests.blocks
  let increments := requests.increments
  let path := PathModel.mk (blocks.children.map CenteredEdge.model)
  { target_positive := positive
    localTarget := localTarget
    localTarget_eq := localEq
    localTarget_positive := localPositive
    requests := requests
    blocks := blocks
    blocks_eq := rfl
    increments := increments
    increments_eq := rfl
    primitiveSum := gaussianSum increments
    primitiveSum_eq := rfl
    integralSample := path.tailIntegralSample
    integralSample_eq := path.integralSample_eq_tailIntegralSample.symm }

/-- Reassembling a complete original request from its own stored target and bank gives the same whole request.

The exact stored block, increment, sum and integral equations identify all
cached data. This is a proof-only readback law; executable clients can keep
those existing values instead of evaluating the assembly procedure again.
-/
theorem ofLocalRequests_eq (request : PrimitiveSumRequest parents count target) :
    ofLocalRequests parents target request.target_positive request.localTarget request.localTarget_eq
      request.localTarget_positive request.requests = request := by
  rcases request with ⟨positive, localTarget, localEq, localPositive, requests, blocks, blocksEq,
    increments, incrementsEq, primitiveSum, primitiveSumEq, integralSample, integralSampleEq⟩
  subst blocks
  subst increments
  subst primitiveSum
  have integralEq := integralSampleEq.trans
    (PathModel.mk (requests.blocks.children.map CenteredEdge.model)).integralSample_eq_tailIntegralSample
  cases integralEq
  rfl

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Assemble the original aggregate caches at the exact count-dependent target from supplied requests.

The complete original default computation is shared with ofLocalRequests;
its whole local-target equality remains reflexive and all requests are the
same supplied original values.
-/
@[expose] def ofRequests (parents : List (CenteredEdge curve differential))
    (target : Fraction.Rational) (positive : 0 < target)
    (requests : RequestedParents count (Budget.Aggregate.perTerm target parents.length) parents) :
    PrimitiveSumRequest parents count target :=
  let localTarget := Budget.Aggregate.perTerm target parents.length
  have localPositive := Budget.Aggregate.perTerm_positive positive parents.length
  ofLocalRequests parents target positive localTarget rfl localPositive requests

section

open Purelib.Approximation.Rational
open Purelib.Data.Rat

/-- Acquire the original covered parent bank at the count-dependent local target and cache its paid aggregate readbacks.

The supplied coverage and properness evidence build requests at the exact
per-term budget, then retain their original aggregate caches. -/
@[expose] def acquire (covered : CoveredParents count parents) (proper : AllParentsProper parents)
    (target : Fraction.Rational) (positive : 0 < target) : PrimitiveSumRequest parents count target :=
  let stored := covered.parentList
  let original := covered.parentList_eq
  let cached := Eq.mp (congrArg (CoveredParents count) original.symm) covered
  have ordered : AllParentsProper stored := Eq.mp (congrArg AllParentsProper original.symm) proper
  let requests := RequestedParents.acquire cached (Budget.Aggregate.perTerm target stored.length)
    (Budget.Aggregate.perTerm_positive positive stored.length) ordered
  let result := ofRequests stored target positive requests
  Eq.mp (congrArg (fun entries => PrimitiveSumRequest entries count target) original) result

/-- Retained-parent acquisition preserves the complete original aggregate request and all cached fields. -/
theorem acquire_eq (covered : CoveredParents count parents) (proper : AllParentsProper parents)
    (target : Fraction.Rational) (positive : 0 < target) :
    acquire covered proper target positive = ofRequests parents target positive
      (RequestedParents.acquire covered (Budget.Aggregate.perTerm target parents.length)
        (Budget.Aggregate.perTerm_positive positive parents.length) proper) := by
  cases covered <;> rfl

end

/-- View the actual retained request bank at its exact original count-dependent target.

Only the stored local-target equation transports the dependent target
index. The same original parent bank, model and block caches are retained;
no request, observation or scalar integral is computed again.
-/
@[expose] def requestsAtTarget (request : PrimitiveSumRequest parents count target) :
    RequestedParents count (Approximation.Rational.Budget.Aggregate.perTerm target parents.length) parents :=
  by
    rcases request with ⟨positive, localTarget, localEq, localPositive, requests, blocks, blocksEq,
      increments, incrementsEq, primitiveSum, primitiveSumEq, integralSample, integralSampleEq⟩
    cases localEq
    exact requests

/-- The target-indexed view reads the identical retained blocks and primitive increments. -/
theorem requestsAtTarget_readbacks (request : PrimitiveSumRequest parents count target) :
    request.requestsAtTarget.blocks = request.blocks ∧ request.requestsAtTarget.increments = request.increments := by
  rcases request with ⟨positive, localTarget, localEq, localPositive, requests, blocks, blocksEq,
    increments, incrementsEq, primitiveSum, primitiveSumEq, integralSample, integralSampleEq⟩
  cases localEq
  exact ⟨blocksEq.symm, incrementsEq.symm⟩

/-- The original aggregate assembler on its actual target-indexed bank equals the complete retained request. -/
theorem ofRequests_requestsAtTarget_eq (request : PrimitiveSumRequest parents count target) :
    ofRequests parents target request.target_positive request.requestsAtTarget = request := by
  have original := ofLocalRequests_eq request
  rcases request with ⟨positive, localTarget, localEq, localPositive, requests, blocks, blocksEq,
    increments, incrementsEq, primitiveSum, primitiveSumEq, integralSample, integralSampleEq⟩
  cases localEq
  exact original

/-- Refine the actual aggregate request, preserving the whole supplied result when its ordered bank is already adequate.

A changed bank uses the original shared aggregate assembler with the SAME
cached local target, target equation and positivity. Its actual new child
blocks, primitive sum and integral are computed once from those requests.
-/
def refine (request : PrimitiveSumRequest parents count target) (proper : AllParentsProper parents)
    (minimum : Nat) : PrimitiveSumRequest parents count target :=
  match RequestedParents.refine? request.requests request.localTarget_positive proper minimum with
  | none => request
  | some requests =>
      ofLocalRequests parents target request.target_positive request.localTarget request.localTarget_eq
        request.localTarget_positive requests

/-- Adequate aggregate refinement preserves the whole original request, blocks, target and integral cache. -/
theorem refine_of_ge (request : PrimitiveSumRequest parents count target) (proper : AllParentsProper parents)
    (minimum : Nat)
    (adequate : ∀ index : Fin parents.length, minimum ≤ (request.requests.get index).request.index) :
    request.refine proper minimum = request := by
  unfold refine
  rewrite [RequestedParents.refine?_none_of_ge request.requests request.localTarget_positive proper minimum adequate]
  rfl

/-- A zero floor preserves the same whole original aggregate request. -/
theorem refine_zero (request : PrimitiveSumRequest parents count target) (proper : AllParentsProper parents) :
    request.refine proper 0 = request := request.refine_of_ge proper 0 (fun _ => Nat.zero_le _)

/-- Aggregate refinement retains the actual original per-term target scalar. -/
theorem refine_localTarget (request : PrimitiveSumRequest parents count target) (proper : AllParentsProper parents)
    (minimum : Nat) : (request.refine proper minimum).localTarget = request.localTarget := by
  unfold refine
  cases RequestedParents.refine? request.requests request.localTarget_positive proper minimum <;> rfl

/-- The aggregate stores the same whole refined bank, with its dependent target proof transported. -/
theorem refine_requests_heq (request : PrimitiveSumRequest parents count target) (proper : AllParentsProper parents)
    (minimum : Nat) : HEq (request.refine proper minimum).requests
      (request.requests.refine request.localTarget_positive proper minimum) := by
  unfold refine RequestedParents.refine
  cases RequestedParents.refine? request.requests request.localTarget_positive proper minimum <;> rfl

/-- Every actual request retained by the aggregate meets the computed common floor. -/
theorem refine_index_ge (request : PrimitiveSumRequest parents count target) (proper : AllParentsProper parents)
    (minimum : Nat) (index : Fin parents.length) :
    minimum ≤ ((request.refine proper minimum).requests.get index).request.index := by
  have bounded := request.requests.refine_index_ge request.localTarget_positive proper minimum index
  unfold refine
  cases selected : RequestedParents.refine? request.requests request.localTarget_positive proper minimum with
  | none =>
      unfold RequestedParents.refine at bounded
      rewrite [selected] at bounded
      exact bounded
  | some requests =>
      unfold RequestedParents.refine at bounded
      rewrite [selected] at bounded
      exact bounded

/-- Refining an actual retained aggregate reads the same whole original bank refinement at its exact target index. -/
theorem requestsAtTarget_refine (request : PrimitiveSumRequest parents count target)
    (proper : AllParentsProper parents) (minimum : Nat) :
    (request.refine proper minimum).requestsAtTarget = request.requestsAtTarget.refine
      (Approximation.Rational.Budget.Aggregate.perTerm_positive request.target_positive parents.length)
      proper minimum := by
  rcases request with ⟨positive, localTarget, localEq, localPositive, requests, blocks, blocksEq,
    increments, incrementsEq, primitiveSum, primitiveSumEq, integralSample, integralSampleEq⟩
  cases localEq
  unfold refine RequestedParents.refine requestsAtTarget
  dsimp only
  cases RequestedParents.refine? requests localPositive proper minimum <;> rfl

section TargetRefinement

open Purelib.Approximation.Rational
open Purelib.Data.Rat

/-- Retarget the supplied actual aggregate using the same original ordered parents and retained local caches.

The unchanged target delegates its exact original refinement. Otherwise the
new count-dependent local target is computed ONCE, each original request is
retargeted with actual model/spatial cache reuse. When the same stored
payments suffice, all four original aggregate caches are retained directly;
otherwise the shared assembler computes their actual changed readbacks.
No source, patch, center, Point or cover is reacquired.
-/
def retarget (request : PrimitiveSumRequest parents count target) (next : Fraction.Rational)
    (positive : 0 < next) (proper : AllParentsProper parents) (minimum : Nat := 0) :
    PrimitiveSumRequest parents count next :=
  if same : next = target then
    Eq.mp (congrArg (PrimitiveSumRequest parents count) same.symm) (request.refine proper minimum)
  else
    let localTarget := Budget.Aggregate.perTerm next parents.length
    have localPositive := Budget.Aggregate.perTerm_positive positive parents.length
    let requests := request.requests.retarget localTarget localPositive proper minimum
    if paid : request.requests.cachePays localTarget minimum then
      have retained := request.requests.retarget_readbacks_of_cachePays
        localTarget localPositive proper minimum paid
      { target_positive := positive
        localTarget := localTarget
        localTarget_eq := rfl
        localTarget_positive := localPositive
        requests := requests
        blocks := request.blocks
        blocks_eq := request.blocks_eq.trans retained.1.symm
        increments := request.increments
        increments_eq := request.increments_eq.trans retained.2.symm
        primitiveSum := request.primitiveSum
        primitiveSum_eq := request.primitiveSum_eq
        integralSample := request.integralSample
        integralSample_eq := request.integralSample_eq }
    else
      ofLocalRequests parents next positive localTarget rfl localPositive requests

/-- The original aggregate target returns its exact original refinement with the complete retained cache branches. -/
theorem retarget_self (request : PrimitiveSumRequest parents count target) (positive : 0 < target)
    (proper : AllParentsProper parents) (minimum : Nat := 0) :
    request.retarget target positive proper minimum = request.refine proper minimum := by
  unfold retarget
  rewrite [dif_pos rfl]
  rfl

/-- The same target and zero floor retain the whole original aggregate and every integral/child cache. -/
theorem retarget_self_zero (request : PrimitiveSumRequest parents count target) (positive : 0 < target)
    (proper : AllParentsProper parents) : request.retarget target positive proper = request :=
  (request.retarget_self positive proper).trans (request.refine_zero proper)

/-- Changed-target cache reuse preserves the complete former original aggregate assembly result.

The supplied retargeted bank is identical in both branches. The cached
branch uses its exact retained readback laws; the changed-data branch is
the original assembly procedure itself.
-/
theorem retarget_eq_ofLocalRequests (request : PrimitiveSumRequest parents count target)
    (next : Fraction.Rational) (positive : 0 < next) (proper : AllParentsProper parents) (minimum : Nat)
    (changed : next ≠ target) :
    request.retarget next positive proper minimum =
      ofLocalRequests parents next positive (Budget.Aggregate.perTerm next parents.length) rfl
        (Budget.Aggregate.perTerm_positive positive parents.length)
        (request.requests.retarget (Budget.Aggregate.perTerm next parents.length)
          (Budget.Aggregate.perTerm_positive positive parents.length) proper minimum) := by
  unfold retarget
  rewrite [dif_neg changed]
  dsimp only
  split
  · exact (ofLocalRequests_eq _).symm
  · rfl

/-- Sufficient actual retained payments preserve all four complete aggregate data and scalar caches.

The original block and increment readbacks transport the existing stored
values into the new target-indexed request. In particular, this branch
never reevaluates the child-model integral or the primitive-increment sum.
No ordering of the old and new targets is required.
-/
theorem retarget_caches_of_cachePays (request : PrimitiveSumRequest parents count target)
    (next : Fraction.Rational) (positive : 0 < next) (proper : AllParentsProper parents) (minimum : Nat)
    (paid : request.requests.cachePays (Budget.Aggregate.perTerm next parents.length) minimum) :
    (request.retarget next positive proper minimum).blocks = request.blocks ∧
      (request.retarget next positive proper minimum).increments = request.increments ∧
      (request.retarget next positive proper minimum).primitiveSum = request.primitiveSum ∧
      (request.retarget next positive proper minimum).integralSample = request.integralSample := by
  by_cases same : next = target
  · subst next
    have samePaid : request.requests.cachePays request.localTarget minimum := by
      exact Eq.mpr (congrArg (fun allowance => request.requests.cachePays allowance minimum)
        request.localTarget_eq) paid
    rewrite [request.retarget_self positive proper minimum,
      request.refine_of_ge proper minimum (request.requests.cachePays_index_ge _ minimum samePaid)]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · unfold retarget
    rewrite [dif_neg same]
    dsimp only
    rewrite [dif_pos paid]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A weaker aggregate target and sufficient original indices reuse all four actual aggregate caches. -/
theorem retarget_caches_of_le (request : PrimitiveSumRequest parents count target)
    (next : Fraction.Rational) (positive : 0 < next) (proper : AllParentsProper parents) (minimum : Nat)
    (weaker : target ≤ next)
    (adequate : ∀ index : Fin parents.length, minimum ≤ (request.requests.get index).request.index) :
    (request.retarget next positive proper minimum).blocks = request.blocks ∧
      (request.retarget next positive proper minimum).increments = request.increments ∧
      (request.retarget next positive proper minimum).primitiveSum = request.primitiveSum ∧
      (request.retarget next positive proper minimum).integralSample = request.integralSample :=
  request.retarget_caches_of_cachePays next positive proper minimum
    (request.requests.cachePays_of_le _ minimum
      (request.localTarget_eq.trans_le (Budget.Aggregate.perTerm_mono weaker parents.length)) adequate)

/-- A paid aggregate retarget preserves any further actual payments on its same original ordered request caches. -/
theorem cachePays_retarget (request : PrimitiveSumRequest parents count target)
    (next : Fraction.Rational) (positive : 0 < next) (proper : AllParentsProper parents) (minimum : Nat)
    (paid : request.requests.cachePays (Budget.Aggregate.perTerm next parents.length) minimum)
    (future : Fraction.Rational) (floor : Nat) (futurePaid : request.requests.cachePays future floor) :
    (request.retarget next positive proper minimum).requests.cachePays future floor := by
  by_cases same : next = target
  · subst next
    have samePaid : request.requests.cachePays request.localTarget minimum :=
      Eq.mpr (congrArg (fun allowance => request.requests.cachePays allowance minimum) request.localTarget_eq) paid
    rewrite [request.retarget_self positive proper minimum,
      request.refine_of_ge proper minimum (request.requests.cachePays_index_ge _ minimum samePaid)]
    exact futurePaid
  · unfold retarget
    rewrite [dif_neg same]
    dsimp only
    rewrite [dif_pos paid]
    exact request.requests.cachePays_retarget _ _ proper minimum paid future floor futurePaid

/-- A changed aggregate target retains exactly its once-computed new count-dependent local allowance. -/
theorem retarget_localTarget_of_ne (request : PrimitiveSumRequest parents count target) (next : Fraction.Rational)
    (positive : 0 < next) (proper : AllParentsProper parents) (minimum : Nat) (changed : next ≠ target) :
    (request.retarget next positive proper minimum).localTarget = Budget.Aggregate.perTerm next parents.length := by
  unfold retarget
  rewrite [dif_neg changed]
  dsimp only
  split <;> rfl

/-- Every actual retargeted aggregate request meets the requested primitive-index floor. -/
theorem retarget_index_ge (request : PrimitiveSumRequest parents count target) (next : Fraction.Rational)
    (positive : 0 < next) (proper : AllParentsProper parents) (minimum : Nat) (index : Fin parents.length) :
    minimum ≤ ((request.retarget next positive proper minimum).requests.get index).request.index := by
  by_cases same : next = target
  · subst next
    rewrite [request.retarget_self positive proper minimum]
    exact request.refine_index_ge proper minimum index
  · unfold retarget
    rewrite [dif_neg same]
    dsimp only
    by_cases paid : request.requests.cachePays (Budget.Aggregate.perTerm next parents.length) minimum
    · rewrite [dif_pos paid]
      exact request.requests.retarget_index_ge (Budget.Aggregate.perTerm next parents.length)
        (Budget.Aggregate.perTerm_positive positive parents.length) proper minimum index
    · rewrite [dif_neg paid]
      exact request.requests.retarget_index_ge (Budget.Aggregate.perTerm next parents.length)
        (Budget.Aggregate.perTerm_positive positive parents.length) proper minimum index

/-- Retargeting preserves each exact original local neighborhood, including every root and source-owner cache.

Changed targets and indices affect only the actual primitive/spatial request.
The same bounded original parent occurrence still reads the identical
outer neighborhood, in both default and changed-target branches.
-/
theorem retarget_neighborhood (request : PrimitiveSumRequest parents count target) (next : Fraction.Rational)
    (positive : 0 < next) (proper : AllParentsProper parents) (minimum : Nat) (index : Fin parents.length) :
    ((request.retarget next positive proper minimum).requests.get index).neighborhood =
      (request.requests.get index).neighborhood := by
  by_cases same : next = target
  · subst next
    rewrite [request.retarget_self positive proper minimum]
    have retained := request.requests.get_refine request.localTarget_positive proper minimum index
    unfold refine
    cases selected : RequestedParents.refine? request.requests request.localTarget_positive proper minimum with
    | none => rfl
    | some requests =>
        unfold RequestedParents.refine at retained
        rewrite [selected] at retained
        dsimp only [Option.getD] at retained
        change (requests.get index).neighborhood = _
        rewrite [retained]
        unfold LocalRequest.refine
        split <;> rfl
  · unfold retarget
    rewrite [dif_neg same]
    dsimp only
    by_cases paid : request.requests.cachePays (Budget.Aggregate.perTerm next parents.length) minimum
    · rewrite [dif_pos paid]
      change ((request.requests.retarget (Budget.Aggregate.perTerm next parents.length)
        (Budget.Aggregate.perTerm_positive positive parents.length) proper minimum).get index).neighborhood = _
      rewrite [request.requests.get_retarget (Budget.Aggregate.perTerm next parents.length)
        (Budget.Aggregate.perTerm_positive positive parents.length) proper minimum index]
      exact (request.requests.get index).retarget_neighborhood (Budget.Aggregate.perTerm next parents.length)
        (Budget.Aggregate.perTerm_positive positive parents.length) (AllParentsProper.get proper index) minimum
    · rewrite [dif_neg paid]
      change ((request.requests.retarget (Budget.Aggregate.perTerm next parents.length)
        (Budget.Aggregate.perTerm_positive positive parents.length) proper minimum).get index).neighborhood = _
      rewrite [request.requests.get_retarget (Budget.Aggregate.perTerm next parents.length)
        (Budget.Aggregate.perTerm_positive positive parents.length) proper minimum index]
      exact (request.requests.get index).retarget_neighborhood (Budget.Aggregate.perTerm next parents.length)
        (Budget.Aggregate.perTerm_positive positive parents.length) (AllParentsProper.get proper index) minimum

end TargetRefinement

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
