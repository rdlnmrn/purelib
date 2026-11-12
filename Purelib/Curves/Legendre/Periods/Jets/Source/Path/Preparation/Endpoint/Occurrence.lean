module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Preparation.Endpoint
public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Refinement

/-! # Original endpoint bundles at retained bank occurrences

The whole original cell factory identity transports the same Point, plan,
attachment, original comparison and actual common-refinement cache together.
Only dependent cell indices change; no source or endpoint factory executes.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Preparation

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds)

variable {parameter : Canonical} {count floor firstFloor lastFloor : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
    {bounds : UniformBounds patch} {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}
    {firstSample : ContinuedNeighborhood.Point patch start.coordinate}
    {lastSample : ContinuedNeighborhood.Point patch finish.coordinate}
    {allowance firstAllocation lastAllocation target : Rational}
    {requests : IntegrandRequests bounds floor (allowance / 4)}
    {firstPlan : EndpointPlan firstSample firstFloor firstAllocation}
    {lastPlan : EndpointPlan lastSample lastFloor lastAllocation}
    {startInside : patch.box.Contains start.coordinate} {finishInside : patch.box.Contains finish.coordinate}
    {positive : 0 < target}

/-- Attach one retained occurrence and its entire original refinement bundle to the same actual cached source Cell.

The full Point, plan, source attachment, derived operational comparison
and cached common-refinement factory cross the whole cell equality as
one dependent bundle. None is replaced by a separately executed factory.
-/
def occurrenceEndpoint
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive)
    {point : LiftedPoint 2} {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    {key : Fin bank.length} (found : Vertex.Bank.FoundAt bank point key)
    {sample : ContinuedNeighborhood.Point patch point.coordinate} {endpointFloor : Nat}
    (plan : EndpointPlan sample endpointFloor allocation)
    (attached : EndpointPlan.Attachment plan prepared.attached.source)
    (equivalent : NamedEquivalent sample.certificate.value.name found.original.sample.certificate.value.name)
    (refinement : RootBranch.Refinement sample found.original.sample equivalent) :
    OccurrenceEndpoint prepared.cell point bank key :=
  let family := fun cell : Cell (parameter := parameter) lifted =>
    (retainedSample : ContinuedNeighborhood.Point cell.patch point.coordinate) ×
    (retainedPlan : EndpointPlan retainedSample endpointFloor allocation) ×
    (_retainedAttachment : EndpointPlan.Attachment retainedPlan cell.request) ×
    (retainedEquivalent : NamedEquivalent retainedSample.certificate.value.name
      found.original.sample.certificate.value.name) ×
    RootBranch.Refinement retainedSample found.original.sample retainedEquivalent
  let original : family
      (Cell.ofModels prepared.attached.source lifted prepared.models startInside finishInside) :=
    ⟨sample, plan, attached, equivalent, refinement⟩
  let retained : family prepared.cell := Eq.mp (congrArg family prepared.cell_eq.symm) original
  OccurrenceEndpoint.ofRefinement prepared.cell found retained.2.1 retained.2.2.1
    retained.2.2.2.1 retained.2.2.2.2

/-- Whole-cell transport preserves the same complete positional bank witness. -/
private theorem packaged_occurrenceEndpoint_found
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive)
    {point : LiftedPoint 2} {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    {key : Fin bank.length} (found : Vertex.Bank.FoundAt bank point key)
    {sample : ContinuedNeighborhood.Point patch point.coordinate} {endpointFloor : Nat}
    (plan : EndpointPlan sample endpointFloor allocation)
    (attached : EndpointPlan.Attachment plan prepared.attached.source)
    (equivalent : NamedEquivalent sample.certificate.value.name found.original.sample.certificate.value.name)
    (refinement : RootBranch.Refinement sample found.original.sample equivalent) :
    (prepared.occurrenceEndpoint found plan attached equivalent refinement).found = found := by rfl

/-- Whole-cell transport preserves the same complete positional bank witness. -/
theorem occurrenceEndpoint_found
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive)
    {point : LiftedPoint 2} {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    {key : Fin bank.length} (found : Vertex.Bank.FoundAt bank point key)
    {sample : ContinuedNeighborhood.Point patch point.coordinate} {endpointFloor : Nat}
    (plan : EndpointPlan sample endpointFloor allocation)
    (attached : EndpointPlan.Attachment plan prepared.attached.source)
    (equivalent : NamedEquivalent sample.certificate.value.name found.original.sample.certificate.value.name)
    (refinement : RootBranch.Refinement sample found.original.sample equivalent) :
    (prepared.occurrenceEndpoint found plan attached equivalent refinement).found = found :=
  packaged_occurrenceEndpoint_found prepared found plan attached equivalent refinement

/-- The dependent cell transport keeps the entire actual original common-refinement cache heterogeneously. -/
private theorem packaged_occurrenceEndpoint_refinement_heq
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive)
    {point : LiftedPoint 2} {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    {key : Fin bank.length} (found : Vertex.Bank.FoundAt bank point key)
    {sample : ContinuedNeighborhood.Point patch point.coordinate} {endpointFloor : Nat}
    (plan : EndpointPlan sample endpointFloor allocation)
    (attached : EndpointPlan.Attachment plan prepared.attached.source)
    (equivalent : NamedEquivalent sample.certificate.value.name found.original.sample.certificate.value.name)
    (refinement : RootBranch.Refinement sample found.original.sample equivalent) :
    HEq (prepared.occurrenceEndpoint found plan attached equivalent refinement).refinement refinement := by
  rcases prepared with ⟨retained, models, ⟨cell, equal⟩, query⟩
  cases equal
  rfl

/-- The dependent cell transport keeps the entire actual original common-refinement cache heterogeneously. -/
theorem occurrenceEndpoint_refinement_heq
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive)
    {point : LiftedPoint 2} {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    {key : Fin bank.length} (found : Vertex.Bank.FoundAt bank point key)
    {sample : ContinuedNeighborhood.Point patch point.coordinate} {endpointFloor : Nat}
    (plan : EndpointPlan sample endpointFloor allocation)
    (attached : EndpointPlan.Attachment plan prepared.attached.source)
    (equivalent : NamedEquivalent sample.certificate.value.name found.original.sample.certificate.value.name)
    (refinement : RootBranch.Refinement sample found.original.sample equivalent) :
    HEq (prepared.occurrenceEndpoint found plan attached equivalent refinement).refinement refinement :=
  packaged_occurrenceEndpoint_refinement_heq prepared found plan attached equivalent refinement

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Preparation

end
