module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint.Bank
public import Purelib.Curves.Legendre.Periods.Jets.Source.Integrands
import Purelib.Data.Nat.Order

/-! # Both original endpoint plans on one actual source request

The retained six integrand requests and both original endpoint stages
are paid before the common Newton model is constructed. The original
modelRequest procedure selects that model once. Both endpoint attachments
then consume its identical selected stage and model-power caches.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.EndpointPlan

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds)

variable {parameter firstPoint lastPoint : Canonical} {count floor firstFloor lastFloor : Nat}
variable {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
variable {bounds : UniformBounds patch} {integrandTarget firstAllocation lastAllocation : Rational}
variable {firstSample : ContinuedNeighborhood.Point patch firstPoint}
variable {lastSample : ContinuedNeighborhood.Point patch lastPoint}

/-- The complete common model request and both actual attachments on the two retained original plans.

The source-request floor is exactly the maximum of the six-integrand stage
and the two endpoint stages. Its subtype retains the complete existing
selection factory, including all original model and polynomial caches.
-/
abbrev AttachedPair (requests : IntegrandRequests bounds floor integrandTarget) (cache : Cache patch)
    (firstPlan : EndpointPlan firstSample firstFloor firstAllocation)
    (lastPlan : EndpointPlan lastSample lastFloor lastAllocation) (target : Rational) (positive : 0 < target) :=
  (source : { retained : Request cache
      (max requests.stage (max firstPlan.requests.stage lastPlan.requests.stage)) target //
    retained = requests.modelRequest cache (max firstPlan.requests.stage lastPlan.requests.stage) target positive }) ×
  Attachment firstPlan source.val × Attachment lastPlan source.val

namespace AttachedPair

variable {requests : IntegrandRequests bounds floor integrandTarget} {cache : Cache patch}
variable {firstPlan : EndpointPlan firstSample firstFloor firstAllocation}
variable {lastPlan : EndpointPlan lastSample lastFloor lastAllocation} {target : Rational} {positive : 0 < target}

/-- Read the one retained original model selection without requesting or refining it again. -/
@[expose] def source (retained : AttachedPair requests cache firstPlan lastPlan target positive) :
    Request cache (max requests.stage (max firstPlan.requests.stage lastPlan.requests.stage)) target := retained.1.val

/-- The source cache is the complete original six-integrand and two-endpoint request factory. -/
theorem source_eq (retained : AttachedPair requests cache firstPlan lastPlan target positive) :
    retained.source =
      requests.modelRequest cache (max firstPlan.requests.stage lastPlan.requests.stage) target positive :=
  retained.1.property

/-- Read the actual first endpoint root and three primitive observations on that same source model. -/
@[expose] def firstAttachment (retained : AttachedPair requests cache firstPlan lastPlan target positive) :
    Attachment firstPlan retained.source := retained.2.1

/-- Read the independent last endpoint root and primitives on the identical retained source model. -/
@[expose] def lastAttachment (retained : AttachedPair requests cache firstPlan lastPlan target positive) :
    Attachment lastPlan retained.source := retained.2.2

/-- The actual selected source stage pays all six original integrand requests. -/
theorem integrands_paid (retained : AttachedPair requests cache firstPlan lastPlan target positive) :
    requests.stage ≤ retained.source.selection.stage := by
  rewrite [retained.source_eq]
  exact requests.stage_le_modelRequest cache (max firstPlan.requests.stage lastPlan.requests.stage) target positive

end AttachedPair

/-- Select the common original model once, then attach both already prepared endpoint plans to that exact stage. -/
def attachPair (requests : IntegrandRequests bounds floor integrandTarget) (cache : Cache patch)
    (firstPlan : EndpointPlan firstSample firstFloor firstAllocation)
    (lastPlan : EndpointPlan lastSample lastFloor lastAllocation) (target : Rational) (positive : 0 < target) :
    AttachedPair requests cache firstPlan lastPlan target positive := by
  let source := requests.modelRequest cache (max firstPlan.requests.stage lastPlan.requests.stage) target positive
  have paid : max firstPlan.requests.stage lastPlan.requests.stage ≤ source.selection.stage :=
    requests.endpointFloor_le_modelRequest cache (max firstPlan.requests.stage lastPlan.requests.stage) target positive
  have firstPaid : firstPlan.requests.stage ≤ source.selection.stage :=
    (Data.Nat.Order.le_max_left _ _).trans paid
  have lastPaid : lastPlan.requests.stage ≤ source.selection.stage :=
    (Data.Nat.Order.le_max_right _ _).trans paid
  let firstAttached := firstPlan.attach source firstPaid
  let lastAttached := lastPlan.attach source lastPaid
  exact ⟨⟨source, rfl⟩, firstAttached, lastAttached⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.EndpointPlan

end
