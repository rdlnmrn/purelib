module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly.ParentOccurrence
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.TraceEndpoints
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Crop
import Purelib.Approximation.Gaussian.Equivalence

/-! # Actual endpoint incidence from a physical occurrence's SAME paid Trace

The original selected Segment, Parents and centers determine one actual
finite lookup on its materialized trace. Both old and fine quarter source
views can consume it directly, without RootComparisons, an independent
reference Owner, whole-Segment contour payment or another trace cache.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

namespace PreparedParents.Trace.Physical.Spine.Sources.ParentOccurrence

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
variable (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets) parent)

/-- Read the three actual endpoint comparison functions directly from the SAME original selected paid Trace.

The entire original parent equality transports only the centered interface.
The original rootTrace retains the whole actual physical path and literal
View tail identities; no whole path identity is inferred from parent words.
-/
def traceEndpoints : PreparedTraceBudget.Trace.EndpointComparisons parent :=
  Eq.mp (congrArg (fun child : CenteredEdge (Fibre.frameCurve frame) basis =>
    PreparedTraceBudget.Trace.EndpointComparisons child) occurrence.parent_eq.symm)
    (occurrence.selected.parents.traceEndpointComparisons
      occurrence.selected.acquired.traced.trace.get rfl occurrence.child)

/-- The selected rootTrace retains the WHOLE original materialized paid path under its exact endpoint reindices.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def RootTracePathHeqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) parent),
    HEq (occurrence.selected.acquired.rootTrace occurrence.selected.acquired.traced.trace.get rfl).path
      occurrence.selected.acquired.traced.trace.get

/-- The selected rootTrace retains the WHOLE original materialized paid path under its exact endpoint reindices. -/
theorem rootTrace_path_heq : RootTracePathHeqLaw := by
  unfold RootTracePathHeqLaw
  intro parameter frame basis count floor sheet baseStart baseFinish original stage targets parent occurrence
  exact occurrence.selected.acquired.internalTrace_heq occurrence.selected.acquired.traced.trace.get

/-- The same selected rootTrace has the complete original budget/subdivision/fits ownerPath factory identity.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def RootTracePathEqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) parent),
    (occurrence.selected.acquired.rootTrace occurrence.selected.acquired.traced.trace.get rfl).path =
      PreparedTraceBudget.ownerPath occurrence.selected.acquired.traced.budget
        occurrence.selected.acquired.traced.prepared.subdivision occurrence.selected.acquired.traced.fits

/-- The same selected rootTrace has the complete original budget/subdivision/fits ownerPath factory identity. -/
theorem rootTrace_path_eq : RootTracePathEqLaw := by
  unfold RootTracePathEqLaw
  intro parameter frame basis count floor sheet baseStart baseFinish original stage targets parent occurrence
  exact (occurrence.selected.acquired.rootTrace occurrence.selected.acquired.traced.trace.get rfl).path_eq

/-- The literal selected physical parents retain their entire original actual center family.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def CenterFamilyHeqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) parent),
    HEq occurrence.selected.parents.covered.centers occurrence.selected.parents.centers

/-- The literal selected physical parents retain their entire original actual center family. -/
theorem center_family_heq : CenterFamilyHeqLaw := by
  unfold CenterFamilyHeqLaw
  intro parameter frame basis count floor sheet baseStart baseFinish original stage targets parent occurrence
  exact occurrence.selected.parents.covered_centers_heq

/-- Read the SAME accepted request position under this exact retained physical child. -/
@[expose] def requestIndex : Fin occurrence.selected.acquired.traced.prepared.subdivision.requests.length :=
  occurrence.selected.parents.requestIndex occurrence.child

/-- Direct request lookup preserves this exact original physical child coordinate, including repeated visits.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def RequestIndexValLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) parent),
    occurrence.requestIndex.val = occurrence.child.val

/-- Direct request lookup preserves this exact original physical child coordinate, including repeated visits. -/
theorem requestIndex_val : RequestIndexValLaw := by
  unfold RequestIndexValLaw
  intro parameter frame basis count floor sheet baseStart baseFinish original stage targets parent occurrence
  exact occurrence.selected.parents.requestIndex_val occurrence.child

/-- Derive inherited source-Owner to SAME primitive Point agreement on the original retained source query.

The source-stationary link supplies the actual inherited/prepared relation.
The LocalRequest consumes its original Query and Point refinements. No
source Owner or primitive sample is replaced by coordinate equality.
-/
def traceSourcePoint {localCount : Nat} {tolerance : Rational}
    (query : PreparedEdge.Query parent.edge 0 parent.edge.baseInside)
    (request : LocalRequest parent localCount tolerance)
    (inside : request.neighborhood.box.Contains (parent.edge.point 0))
    (sample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point 0)) :
    NamedEquivalent (ownerName parent.edge.owner) sample.certificate.value.name :=
  let endpoints := occurrence.traceEndpoints
  let actual := request.retainedQueryEquivalent 0 parent.edge.baseInside query rfl inside sample
  (endpoints.1 query).symm.trans actual

/-- Derive both literal upper-endpoint Point comparisons through ONE direct lookup on the SAME actual Trace.

The selected comparison product and Query-to-Point relation are each read
once. The moving and retention Owners keep their separate whole original
suffixes; the SAME Query, request and old Point are used unchanged in both
compositions. No fixed-box movement premise or final signed relation is an
input, and no paid/query/Point producer is replayed.
-/
def tracePoints {localCount : Nat} {tolerance : Rational}
    (query : PreparedEdge.Query parent.edge 1 (of_decide_eq_true rfl))
    (request : LocalRequest parent localCount tolerance)
    (sample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point 1)) :
    PointResult request sample × PointResult request sample :=
  let endpoints := occurrence.traceEndpoints
  let actual := request.retainedQueryEquivalent 1 (of_decide_eq_true rfl) query rfl request.finishInside sample
  let moving := endpoints.2.1 query
  let kept := endpoints.2.2 query
  ⟨⟨moving, moving.2.symm.trans actual⟩, ⟨kept, kept.2.symm.trans actual⟩⟩

/-- The entire original endpoint pair is the literal retained let-bound constructor result.

This private factory identity keeps both full PointResults together. Its
only clients project the complete moving and reset EndpointResults; no
cached Owner or operational comparison is reconstructed from scalar fields.
-/
private theorem tracePoints_eq {localCount : Nat} {tolerance : Rational}
    (query : PreparedEdge.Query parent.edge 1 (of_decide_eq_true rfl))
    (request : LocalRequest parent localCount tolerance)
    (sample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point 1)) :
    tracePoints (frame := frame) (basis := basis) (parent := parent) occurrence query request sample =
      (show PointResult (frame := frame) (basis := basis) (parent := parent) request sample ×
          PointResult (frame := frame) (basis := basis) (parent := parent) request sample from
        let endpoints := occurrence.traceEndpoints
        let actual := request.retainedQueryEquivalent 1 (of_decide_eq_true rfl) query rfl request.finishInside sample
        let moving := endpoints.2.1 query
        let kept := endpoints.2.2 query
        ⟨⟨moving, moving.2.symm.trans actual⟩, ⟨kept, kept.2.symm.trans actual⟩⟩
      ) := by
  rfl

/-- The moving Point result retains the exact selected direct-Trace endpoint result.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def TracePointsMovingEqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) parent)
    {localCount : Nat}
    {tolerance : Rational}
    (query : PreparedEdge.Query parent.edge 1 (of_decide_eq_true rfl))
    (request : LocalRequest parent localCount tolerance)
    (sample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point 1)),
    (occurrence.tracePoints query request sample).1.1 = occurrence.traceEndpoints.2.1 query

/-- The moving Point result retains the exact selected direct-Trace endpoint result. -/
theorem tracePoints_moving_eq : TracePointsMovingEqLaw := by
  unfold TracePointsMovingEqLaw
  intro parameter frame basis count floor sheet baseStart baseFinish original stage targets parent occurrence
    localCount tolerance query request sample
  have projected := congrArg
    (fun result : PointResult (frame := frame) (basis := basis) (parent := parent) request sample ×
        PointResult (frame := frame) (basis := basis) (parent := parent) request sample => result.1.1)
    (tracePoints_eq (frame := frame) (basis := basis) (parent := parent) occurrence query request sample)
  dsimp only at projected
  exact projected

/-- The retained Point result preserves its distinct original reset endpoint result.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def TracePointsRetainedEqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) parent)
    {localCount : Nat}
    {tolerance : Rational}
    (query : PreparedEdge.Query parent.edge 1 (of_decide_eq_true rfl))
    (request : LocalRequest parent localCount tolerance)
    (sample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point 1)),
    (occurrence.tracePoints query request sample).2.1 = occurrence.traceEndpoints.2.2 query

/-- The retained Point result preserves its distinct original reset endpoint result. -/
theorem tracePoints_retained_eq : TracePointsRetainedEqLaw := by
  unfold TracePointsRetainedEqLaw
  intro parameter frame basis count floor sheet baseStart baseFinish original stage targets parent occurrence
    localCount tolerance query request sample
  have projected := congrArg
    (fun result : PointResult (frame := frame) (basis := basis) (parent := parent) request sample ×
        PointResult (frame := frame) (basis := basis) (parent := parent) request sample => result.2.1)
    (tracePoints_eq (frame := frame) (basis := basis) (parent := parent) occurrence query request sample)
  dsimp only at projected
  exact projected

/-- Read the original endpoint comparison cache and arbitrary ordered query crop on this SAME selected physical child.

The actual acquired Segment, its retained centers and whole original
rootTrace are reused. The complete parent_eq changes only the nominal
child interface; no Owner is identified from endpoint coordinates.
-/
def cropComparisons (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1)
    (upperInside : 0 ≤ upper ∧ upper ≤ 1) (ordered : lower ≤ upper) :
    PreparedTraceBudget.Trace.CropComparisons parent lower upper lowerInside upperInside :=
  PreparedTraceBudget.Trace.CropComparisons.cast occurrence.parent_eq.symm
    (occurrence.selected.parents.traceCropComparisons
      occurrence.selected.acquired.traced.trace.get rfl occurrence.child
      lower upper lowerInside upperInside ordered)

/-- Construct the crop on the two SAME Queries and derive both actual Query-to-Point endpoint comparisons.

One literal occurrence lookup retains the old source/moving/reset
comparison functions. The new crop is constructed once on the supplied
queries; each original LocalRequest refinement compares that SAME query
to its unchanged Point. The three old endpoint functions remain in the
returned product for genuine source/retention attachments.
-/
def croppedPoints {localCount : Nat} {tolerance : Rational}
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (ordered : lower ≤ upper) (firstQuery : PreparedEdge.Query parent.edge lower lowerInside)
    (lastQuery : PreparedEdge.Query parent.edge upper upperInside)
    (request : LocalRequest parent localCount tolerance)
    (firstSample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point lower))
    (lastSample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point upper)) :
    PreparedTraceBudget.Trace.EndpointComparisons parent ×
      OwnerPath (Fibre.frameCurve frame).polynomial
        (parent.edge.point lower) firstQuery.owner (parent.edge.point upper) lastQuery.owner ×
      NamedEquivalent (ownerName firstQuery.owner) firstSample.certificate.value.name ×
      NamedEquivalent (ownerName lastQuery.owner) lastSample.certificate.value.name :=
  let selected := occurrence.cropComparisons lower upper lowerInside upperInside ordered
  let path := selected.2 firstQuery lastQuery
  let first := NamedEquivalent.transport firstQuery.name_eq rfl
    (request.retainedQueryEquivalent lower lowerInside firstQuery rfl (request.point_inside lowerInside) firstSample)
  let last := NamedEquivalent.transport lastQuery.name_eq rfl
    (request.retainedQueryEquivalent upper upperInside lastQuery rfl (request.point_inside upperInside) lastSample)
  ⟨selected.1, path, first, last⟩

/-- The exact selected physical crop retains one actual endpoint occurrence under the whole parent_eq.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def CropComparisonsVerticesLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) parent)
    (lower : Rational)
    (upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1)
    (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (ordered : lower ≤ upper)
    (source : PreparedEdge.Query parent.edge lower lowerInside)
    (target : PreparedEdge.Query parent.edge upper upperInside),
    ((occurrence.cropComparisons lower upper lowerInside upperInside ordered).2 source target).vertices =
      [parent.edge.point upper]

/-- The exact selected physical crop retains one actual endpoint occurrence under the whole parent_eq.

Only proof data follows the original parent transport and stored rootTrace
lookup. The source/moving/reset functions are not executed by this law.
-/
theorem cropComparisons_vertices : CropComparisonsVerticesLaw := by
  unfold CropComparisonsVerticesLaw
  intro parameter frame basis count floor sheet baseStart baseFinish original stage targets parent occurrence
    lower upper lowerInside upperInside ordered source target
  unfold cropComparisons
  exact PreparedTraceBudget.Trace.CropComparisons.cast_vertices
    (curve := Fibre.frameCurve frame) (differential := basis) (last := parent) occurrence.parent_eq.symm
    (occurrence.selected.parents.traceCropComparisons
      occurrence.selected.acquired.traced.trace.get rfl occurrence.child
      lower upper lowerInside upperInside ordered)
    (fun source target => occurrence.selected.parents.traceCropComparisons_vertices
      occurrence.selected.acquired.traced.trace.get rfl occurrence.child
      lower upper lowerInside upperInside ordered source target) source target

end PreparedParents.Trace.Physical.Spine.Sources.ParentOccurrence

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
