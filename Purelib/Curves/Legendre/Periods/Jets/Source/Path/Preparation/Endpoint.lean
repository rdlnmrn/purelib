module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Preparation
public import Purelib.Curves.Legendre.Periods.Jets.Source.Stage

/-! # Exact endpoint attachment on an already retained source cell

The complete original cell factory equation transports the existing point,
plan, root attachment and geometric branch together. The operation consumes
the retained cell directly; it never constructs another primitive-model
cache or requests another endpoint reading.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Preparation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds)

variable {parameter : Canonical} {count floor firstFloor lastFloor : Nat}
variable {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
variable {bounds : UniformBounds patch} {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}
variable {firstSample : ContinuedNeighborhood.Point patch start.coordinate}
variable {lastSample : ContinuedNeighborhood.Point patch finish.coordinate}
variable {allowance firstAllocation lastAllocation target : Rational}
variable {requests : IntegrandRequests bounds floor (allowance / 4)}
variable {firstPlan : EndpointPlan firstSample firstFloor firstAllocation}
variable {lastPlan : EndpointPlan lastSample lastFloor lastAllocation}
variable {startInside : patch.box.Contains start.coordinate} {finishInside : patch.box.Contains finish.coordinate}
variable {positive : 0 < target}

/-- Attach an existing endpoint bundle to the identical complete retained cell by exact factory transport.

Both the actual first bank lookup and the supplied original common-owner
branch are preserved. All point, plan and root fields cross the cell equality
together, so no copied patch, recomputed model or substituted reading is used.
-/
def endpoint
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive)
    {point : LiftedPoint 2} {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    (found : Vertex.Bank.Found bank point) {sample : ContinuedNeighborhood.Point patch point.coordinate}
    {endpointFloor : Nat} (plan : EndpointPlan sample endpointFloor allocation)
    (attached : EndpointPlan.Attachment plan prepared.attached.source)
    (branch : RootBranch sample found.original.sample) : Endpoint prepared.cell point bank :=
  let family := fun cell : Cell (parameter := parameter) lifted =>
    (retainedSample : ContinuedNeighborhood.Point cell.patch point.coordinate) ×
    (retainedPlan : EndpointPlan retainedSample endpointFloor allocation) ×
    EndpointPlan.Attachment retainedPlan cell.request × RootBranch retainedSample found.original.sample
  let original : family
      (Cell.ofModels prepared.attached.source lifted prepared.models startInside finishInside) :=
    ⟨sample, plan, attached, branch⟩
  let retained : family prepared.cell := Eq.mp (congrArg family prepared.cell_eq.symm) original
  Endpoint.ofAttachment prepared.cell found retained.2.1 retained.2.2.1 retained.2.2.2

/-- Exact cell-index transport keeps the actual first matching original bank lookup unchanged. -/
theorem endpoint_found
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive)
    {point : LiftedPoint 2} {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    (found : Vertex.Bank.Found bank point) {sample : ContinuedNeighborhood.Point patch point.coordinate}
    {endpointFloor : Nat} (plan : EndpointPlan sample endpointFloor allocation)
    (attached : EndpointPlan.Attachment plan prepared.attached.source)
    (branch : RootBranch sample found.original.sample) :
    (prepared.endpoint found plan attached branch).found = found := by rfl

/-- The same whole-bundle transport preserves the complete original point owner, including its retained track. -/
theorem endpoint_owner
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive)
    {point : LiftedPoint 2} {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    (found : Vertex.Bank.Found bank point) {sample : ContinuedNeighborhood.Point patch point.coordinate}
    {endpointFloor : Nat} (plan : EndpointPlan sample endpointFloor allocation)
    (attached : EndpointPlan.Attachment plan prepared.attached.source)
    (branch : RootBranch sample found.original.sample) :
    (prepared.endpoint found plan attached branch).sample.owner = sample.owner := by
  rcases prepared with ⟨retained, models, ⟨cell, equal⟩, query⟩
  cases equal
  change (Endpoint.ofAttachment (Cell.ofModels retained.source lifted models startInside finishInside)
    found plan attached branch).sample.owner = sample.owner
  exact congrArg (fun actual => actual.owner)
    (Endpoint.ofAttachment_sample (Cell.ofModels retained.source lifted models startInside finishInside)
      found plan attached branch)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Preparation

end
