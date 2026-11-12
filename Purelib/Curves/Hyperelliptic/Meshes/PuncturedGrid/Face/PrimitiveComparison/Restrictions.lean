module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Chord
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Restrictions
import Purelib.Riemann.Paths.OwnerTracePath.StationaryHead
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Approximation.Gaussian.Equivalence

/-! # Actual root Entries of the same retained per-link source restrictions

Each actual stationary link supplies its own signed comparison. Each
actual moving link is followed along the restriction of its same retained
face-contained segment. The source/moving/retention owners remain distinct,
including every repeated or stationary occurrence. No query, selector,
join, transport row or numerical model bank is prepared again.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint CachedSource StepRequest)
open Purelib.Riemann.Branches
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget (Trace)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName_eq_of_heq)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootFrames bank.grid} {face : RegularFace bank} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial face.cell.box start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {cell : CellModel}

/-- The original face anchor reaches the three actual retained trace-view Owners at every same cached request. -/
@[expose] def TraceRoots (models : FaceModels frames face) (sheet : Fin 2) :
    ∀ {current : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits},
      Trace.Restrictions budget cell subdivision fits trace → Prop
  | _, _, .stop _ _, _, _, _ => True
  | _, _, .next _ _ _ _ _ _ _, _, _, kept =>
      Reached face.cell.box (models.frame.owners sheet) kept.1.source.owner ∧
      Reached face.cell.box (models.frame.owners sheet) kept.1.moving.owner ∧
      Reached face.cell.box (models.frame.owners sheet) kept.1.tail.owner ∧
      TraceRoots models sheet kept.2.2.2.2
termination_by structural _ _ subdivision _ _ _ => subdivision

/-- Transport only the proved original sheet index in a retained reachability certificate. -/
private theorem reached_sheet {models : FaceModels frames face} {first last : Fin 2}
    {point : Canonical} {owner : Owner (curve.polynomial.eval point)} (same : first = last)
    (reached : Reached face.cell.box (models.frame.owners first) owner) :
    Reached face.cell.box (models.frame.owners last) owner :=
  Eq.mp (congrArg (fun sheet => Reached face.cell.box (models.frame.owners sheet) owner) same) reached

/-- Derive actual per-link root lineage from the SAME cached trace views and original initial Entry.

The moving path contains the actual stored head link. Endpoint casts use
separate exact geometry and whole-Owner identities. Both stationary
comparisons use their actual original head links, with no join factory
replayed. All newly constructed Entry values are certified views of these
same Owners, not replacements of the original root caches.
-/
theorem traceRoots (models : FaceModels frames face) :
    ∀ {current : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
      (kept : Trace.Restrictions budget cell subdivision fits trace)
      (entry : Entry models (segment.pointAt current.parameter) owner), TraceRoots models entry.sheet kept
  | _, _, .stop _ _, _, _, _, _ => True.intro
  | _, _, .next current owner request cached ordered small remaining, _, trace, kept, entry => by
      let view := kept.1
      let sourceComparison : NamedEquivalent (ownerName owner) (ownerName cached.preparedOwner) :=
        NamedEquivalent.transport rfl view.source_name_eq
        (trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point)
      let sourceEntry : Entry models (segment.pointAt current.parameter) cached.preparedOwner :=
        entry.followEquivalent sourceComparison
      have sourceSheet : sourceEntry.sheet = entry.sheet := entry.followEquivalent_sheet sourceComparison
      have sourceReached := (reached_sheet (models := models) sourceSheet sourceEntry.reached).castFinish
        view.source_point.symm view.source_owner_heq.symm
      let actualSource : Entry models view.source.point view.source.owner := ⟨entry.sheet, sourceReached⟩
      let original := view.source.path.headLink view.moving view.2.1.property
      let movingPath : OwnerPath curve.polynomial view.source.point view.source.owner
          view.moving.point view.moving.owner := .cons original.val (.nil _ _)
      let restricted := segment.restrict within current.parameter request.endpoint.parameter
        current.inside request.endpoint.inside
      let actualSegment := (restricted.castStart view.source_point.symm).castFinish view.moving_point.symm
      have sourceInside := Eq.mpr (congrArg face.cell.box.Contains view.source_point)
        (segment.pointAt_contains within current.parameter current.inside)
      have movingInside := Eq.mpr (congrArg face.cell.box.Contains view.moving_point)
        (segment.pointAt_contains within request.endpoint.parameter request.endpoint.inside)
      let movingEntry : Entry models view.moving.point view.moving.owner :=
        actualSource.followSegment actualSegment movingPath rfl sourceInside movingInside
      have movingSheet : movingEntry.sheet = entry.sheet :=
        actualSource.followSegment_sheet actualSegment movingPath rfl sourceInside movingInside
      have movingReached := reached_sheet (models := models) movingSheet movingEntry.reached
      let samePoint := view.tail_point.trans view.moving_point.symm
      let targetAtMoving := castOwnerParameter (congrArg curve.polynomial.eval samePoint) view.tail.owner
      have targetName : ownerName targetAtMoving = ownerName view.tail.owner :=
        ownerName_eq_of_heq (congrArg curve.polynomial.eval samePoint).symm
          (castOwnerParameter_heq (congrArg curve.polynomial.eval samePoint) view.tail.owner)
      let retention := NamedEquivalent.transport rfl targetName.symm
        (view.moving.path.stationaryHeadEquivalent view.tail view.2.2.property samePoint)
      let retainedEntry : Entry models view.moving.point targetAtMoving := movingEntry.followEquivalent retention
      have retainedSheet : retainedEntry.sheet = entry.sheet :=
        (movingEntry.followEquivalent_sheet retention).trans movingSheet
      have retainedReached := reached_sheet (models := models) retainedSheet retainedEntry.reached
      have tailReached := retainedReached.castFinish samePoint.symm
        (castOwnerParameter_heq (congrArg curve.polynomial.eval samePoint) view.tail.owner)
      let targetAtEndpoint := castOwnerParameter (congrArg curve.polynomial.eval view.tail_point) view.tail.owner
      have endpointName : ownerName targetAtEndpoint = ownerName view.tail.owner :=
        ownerName_eq_of_heq (congrArg curve.polynomial.eval view.tail_point).symm
          (castOwnerParameter_heq (congrArg curve.polynomial.eval view.tail_point) view.tail.owner)
      let endpointEntry : Entry models (segment.pointAt request.endpoint.parameter) targetAtEndpoint :=
        ⟨entry.sheet, tailReached.castFinish view.tail_point
          (castOwnerParameter_heq (congrArg curve.polynomial.eval view.tail_point) view.tail.owner).symm⟩
      have nextName : ownerName targetAtEndpoint =
          ownerName (PreparedSheetContinuation.advance segment within current owner request small) :=
        endpointName.trans (view.tail_name_eq.trans (congrArg (fun owner => ownerName owner) remaining.sourceOwner_eq))
      let nextComparison := NamedEquivalent.transport rfl nextName (NamedEquivalent.refl (ownerName targetAtEndpoint))
      let nextEntry : Entry models (segment.pointAt request.endpoint.parameter)
          (PreparedSheetContinuation.advance segment within current owner request small) :=
        endpointEntry.followEquivalent nextComparison
      have nextSheet : nextEntry.sheet = entry.sheet := endpointEntry.followEquivalent_sheet nextComparison
      have following := traceRoots models kept.2.2.2.2 nextEntry
      exact ⟨sourceReached, movingReached, tailReached,
        Eq.mp (congrArg (fun sheet => TraceRoots models sheet kept.2.2.2.2) nextSheet) following⟩
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- The same source endpoint laws and actual initial Entry derive both model incidence and actual root lineage.

The two certificates concern the identical retained restriction/trace cache.
No equality of independent integrals, primitive constants, root owners or
matrix actions is an input or conclusion.
-/
theorem rooted (models : FaceModels frames face) (sourceStart : cell.start = start)
    (sourceFinish : cell.finish = finish) {current : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current owner}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (kept : Trace.Restrictions budget cell subdivision fits trace)
    (entry : Entry models (segment.pointAt current.parameter) owner) :
    Trace.Restrictions.Follows kept ∧ TraceRoots models entry.sheet kept :=
  ⟨Trace.Restrictions.follows sourceStart sourceFinish kept, traceRoots models kept entry⟩

namespace TraceRoots

variable (models : FaceModels frames face) (sheet : Fin 2)
    {current : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {cached : CachedSource segment current owner request}
    {ordered : current.parameter ≤ request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current owner request).track.initial.clearance.bound}
    {remaining : Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within current owner request small)}
    {fits : budget.RequestsFit current (Subdivision.next current owner request cached ordered small remaining).requests}
    {trace : Trace budget (Subdivision.next current owner request cached ordered small remaining) fits}
    (kept : Trace.Restrictions budget cell (Subdivision.next current owner request cached ordered small remaining)
      fits trace) (roots : TraceRoots models sheet kept)

/-- Read a genuine Entry on the same actual source-suffix Owner from the derived root certificate. -/
def sourceEntry : Entry models kept.1.source.point kept.1.source.owner := ⟨sheet, roots.1⟩

/-- Read a genuine Entry on the same actual moving-suffix Owner from the derived root certificate. -/
def movingEntry : Entry models kept.1.moving.point kept.1.moving.owner := ⟨sheet, roots.2.1⟩

/-- Read a genuine Entry on the same actual retained-tail Owner from the derived root certificate. -/
def retainedEntry : Entry models kept.1.tail.point kept.1.tail.owner := ⟨sheet, roots.2.2.1⟩

/-- The three certified views preserve the same original supplied face-sheet index. -/
theorem entry_sheets : (sourceEntry models sheet kept roots).sheet = sheet ∧
    (movingEntry models sheet kept roots).sheet = sheet ∧ (retainedEntry models sheet kept roots).sheet = sheet :=
  ⟨rfl, rfl, rfl⟩

end TraceRoots

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

end
