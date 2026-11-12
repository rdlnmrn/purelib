module

public import Purelib.Riemann.Paths.PreparedPathTrace
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootPath
import Purelib.Riemann.Paths.OwnerTracePath.Suffix
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # Literal owner traces from the same retained path lineage

The retained prepared path and lineage determine the original canonical
trace factory. Its specification is consumed only to certify an already
materialized actual path. Original path, Owner and suffix values remain
inputs; no source preparation or ownerPath factory is replayed to extract
any computational Owner or link.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathTrace

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels
  (PreparedPath CompleteSegment ownerAtStart zeroEndpoint oneEndpoint)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter_heq)

namespace PreparedPath.TraceLineage

/-- Read the canonical owner-path factory from the SAME original prepared path and retained lineage. -/
@[expose] def ownerPath {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Canonical} → {path : ClearPath polynomial ambient start finish} →
    {owner : Owner (polynomial.eval start)} → {prepared : PreparedPath path owner} →
    PreparedPath.TraceLineage prepared →
      OwnerPath polynomial start owner finish (PreparedPathGluing.finishOwner prepared)
  | _, _, _, _, _, .nil point owner => .nil point owner
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining =>
      let front := CompleteSegment.ownerPath first budget fits
      let following := ownerPath remaining
      (front.append (following.reindexOwners finishOwnerEq rfl)).reindexOwners rfl
        (PreparedPath.castOwner_finishOwner finishOwnerEq rest).symm

end PreparedPath.TraceLineage

namespace CompleteSegment

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}

/-- Reindex the SAME supplied complete-segment path to its original raw subdivision trace.

Only the supplied materialized path is transported. Its original factory
is consumed in the erased specification proof; no complete-segment path,
source Owner, request or continuation is prepared again.
-/
def asTrace (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests)
    (materialized : OwnerPath polynomial start owner finish prepared.finishOwner)
    (materializedEq : materialized = CompleteSegment.ownerPath prepared budget fits) :
    PreparedSubdivisionTrace.PreparedTraceBudget.Trace budget prepared.subdivision fits := by
  have firstOwner : HEq (ownerAtStart segment owner) owner := by
    unfold ownerAtStart
    exact castOwnerParameter_heq _ _
  let raw := materialized.castEndpoints prepared.start_eq.symm prepared.finish_eq.symm
    firstOwner.symm prepared.finishOwner_heq_terminalOwner
  have rawEq := congrArg (fun kept : OwnerPath polynomial start owner finish prepared.finishOwner =>
    kept.castEndpoints prepared.start_eq.symm prepared.finish_eq.symm firstOwner.symm
      prepared.finishOwner_heq_terminalOwner) materializedEq
  exact ⟨raw, rawEq.trans (OwnerPath.castEndpoints_inverse prepared.start_eq prepared.finish_eq
    firstOwner prepared.finishOwner_heq_terminalOwner.symm
    (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget prepared.subdivision fits))⟩

/-- The raw subdivision view preserves the complete supplied materialized path heterogeneously. -/
theorem asTrace_heq (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests)
    (materialized : OwnerPath polynomial start owner finish prepared.finishOwner)
    (materializedEq : materialized = CompleteSegment.ownerPath prepared budget fits) :
    HEq (asTrace prepared budget fits materialized materializedEq).path materialized := by
  unfold asTrace
  exact OwnerPath.castEndpoints_heq _ _ _ _ _

end CompleteSegment

namespace TracedSegment

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}

/-- The exact original complete-segment trace factory at the same retained terminal Owner. -/
@[expose] def canonicalTrace (traced : TracedSegment segment within owner) :
    OwnerPath polynomial start owner finish traced.finishOwner :=
  (CompleteSegment.ownerPath traced.prepared traced.budget traced.fits).reindexOwners rfl
    traced.finishOwner_eq.symm

/-- Literal trace coherence concerns the complete supplied path value and the same original factory. -/
@[expose] def Coherent (traced : TracedSegment segment within owner) : Prop :=
  traced.trace.get = traced.canonicalTrace

/-- The actual public segment producer retains its literal original trace factory. -/
theorem coherent_of_build (traced : TracedSegment segment within owner)
    (factory : traced = TracedSegment.build segment within owner) : traced.Coherent := by
  cases factory
  unfold Coherent canonicalTrace TracedSegment.build
  rfl

/-- Reindex the SAME supplied materialized segment trace to its original subdivision factory.

The factory term occurs only in the specification proof. Runtime data
comes from the supplied actual path and erased endpoint/Owner transports;
no trace thunk, source cache or ownerPath producer is executed here.
-/
def asTrace (traced : TracedSegment segment within owner)
    (materialized : OwnerPath polynomial start owner finish traced.finishOwner)
    (materializedEq : materialized = traced.trace.get) (coherent : traced.Coherent) :
    PreparedSubdivisionTrace.PreparedTraceBudget.Trace traced.budget traced.prepared.subdivision traced.fits := by
  let displayed := materialized.reindexOwners rfl traced.finishOwner_eq
  have displayedEq : displayed = CompleteSegment.ownerPath traced.prepared traced.budget traced.fits :=
    (congrArg (fun kept : OwnerPath polynomial start owner finish traced.finishOwner =>
      kept.reindexOwners rfl traced.finishOwner_eq)
      (materializedEq.trans coherent)).trans
        (OwnerPath.reindexOwners_inverse rfl traced.finishOwner_eq.symm
          (CompleteSegment.ownerPath traced.prepared traced.budget traced.fits))
  exact CompleteSegment.asTrace traced.prepared traced.budget traced.fits displayed displayedEq

/-- Exact subdivision reindexing retains the complete supplied materialized path heterogeneously. -/
theorem asTrace_heq (traced : TracedSegment segment within owner)
    (materialized : OwnerPath polynomial start owner finish traced.finishOwner)
    (materializedEq : materialized = traced.trace.get) (coherent : traced.Coherent) :
    HEq (asTrace traced materialized materializedEq coherent).path materialized := by
  unfold asTrace
  exact (CompleteSegment.asTrace_heq _ _ _ _ _).trans
    (OwnerPath.castEndpoints_heq rfl rfl (heq_of_eq rfl) (heq_of_eq traced.finishOwner_eq) materialized)

end TracedSegment

namespace TracedPath

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    {path : ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}

/-- Read only the canonical factory on this SAME prepared path, lineage and exact endpoint-Owner transport. -/
@[expose] def canonicalTrace (traced : TracedPath path owner) :
    OwnerPath polynomial start owner finish traced.finishOwner :=
  traced.lineage.ownerPath.reindexOwners rfl traced.finishOwner_eq.symm

/-- Literal coherence of the actual trace is stronger than equality of its winding. -/
@[expose] def Coherent (traced : TracedPath path owner) : Prop :=
  traced.trace.get = traced.canonicalTrace

/-- Original Owner transports commute with the same retained append, without inspecting either path. -/
private theorem append_reindex {start middle finish : Canonical}
    {first : Owner (polynomial.eval start)}
    {preparedMiddle actualMiddle : Owner (polynomial.eval middle)}
    {preparedFinish actualFinish castFinish : Owner (polynomial.eval finish)}
    (middleEq : actualMiddle = preparedMiddle) (finishEq : actualFinish = preparedFinish)
    (castEq : castFinish = preparedFinish)
    (front : OwnerPath polynomial start first middle preparedMiddle)
    (following : OwnerPath polynomial middle actualMiddle finish preparedFinish) :
    (front.reindexOwners rfl middleEq.symm).append (following.reindexOwners rfl finishEq.symm) =
      ((front.append (following.reindexOwners middleEq rfl)).reindexOwners rfl castEq.symm).reindexOwners
        rfl (finishEq.trans castEq.symm).symm := by
  cases middleEq
  cases finishEq
  cases castEq
  rfl

/-- Concatenating the same two coherent caches preserves literal original trace coherence. -/
theorem coherent_cons {middle : Canonical}
    {head : ClearSegment polynomial ambient start middle} {tail : ClearPath polynomial ambient middle finish}
    {within : head.WithinAmbient}
    (first : TracedSegment head within owner) (rest : TracedPath tail first.finishOwner)
    (firstCoherent : first.Coherent) (restCoherent : rest.Coherent) :
    (TracedPath.cons first rest).Coherent := by
  change first.trace.get.append rest.trace.get = _
  have front := firstCoherent
  have following := restCoherent
  unfold TracedSegment.Coherent at front
  unfold Coherent at following
  exact (congrArg₂ (fun (front : OwnerPath polynomial start owner middle first.finishOwner)
      (following : OwnerPath polynomial middle first.finishOwner finish rest.finishOwner) => front.append following)
    front following).trans
    (append_reindex first.finishOwner_eq rest.finishOwner_eq
      (PreparedPath.castOwner_finishOwner first.finishOwner_eq rest.prepared)
      (CompleteSegment.ownerPath first.prepared first.budget first.fits) rest.lineage.ownerPath)

/-- The original path producer's retained prepared/lineage caches certify its exact actual trace. -/
private theorem build_coherent :
    {start finish : Canonical} → (path : ClearPath polynomial ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner (polynomial.eval start)) →
    (TracedPath.build path within owner).Coherent
  | _, _, .nil _, _, _ => rfl
  | _, _, .cons head tail, within, owner =>
      coherent_cons (TracedSegment.build head within.head owner)
        (TracedPath.build tail within.tail (TracedSegment.build head within.head owner).finishOwner)
        (TracedSegment.coherent_of_build _ rfl) (build_coherent tail within.tail _)

/-- Specialize the actual public whole-path factory without executing it to recover an Owner or link. -/
theorem coherent_of_build (within : path.WithinAmbient) (traced : TracedPath path owner)
    (factory : traced = TracedPath.build path within owner) :
    traced.Coherent := by
  cases factory
  exact build_coherent _ _ _

end TracedPath

end Purelib.Riemann.Paths.PreparedPathTrace

end
