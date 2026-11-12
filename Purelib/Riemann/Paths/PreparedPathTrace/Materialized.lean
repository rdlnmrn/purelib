module

public import Purelib.Riemann.Paths.PreparedPathTrace.Lineage
public import Purelib.Riemann.Paths.OwnerTracePath.Split
import Purelib.Tactic.QuotientFreeOmega

/-! # Retained complete segments of a materialized original path trace

The exact stored request counts select constructor boundaries in the
actual supplied path. Complete prefix and suffix identities then transport
those same values to the original segment budget and remaining lineage.
Canonical path factories occur only in erased specification proofs.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathTrace

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint StepRequest)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath CompleteSegment zeroEndpoint oneEndpoint)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget (Trace traceVertices)

variable {polynomial : GaussianPolynomial} {ambient : Box}

/-- The original trace keeps three links for each supplied request, including both stationary roles. -/
private theorem traceVertices_length {start finish : Canonical}
    (segment : ClearSegment polynomial ambient start finish) :
    ∀ (current : Endpoint) (requests : List StepRequest),
      (traceVertices segment current requests).length = 3 * requests.length
  | _, [] => rfl
  | _current, request :: remaining => by
      change (traceVertices segment request.endpoint remaining).length + 1 + 1 + 1 =
        3 * (remaining.length + 1)
      have following := traceVertices_length segment request.endpoint remaining
      omega0

namespace CompleteSegment

/-- The exact prefix link count reads only the SAME original retained subdivision step count. -/
theorem ownerPath_length {start finish : Canonical}
    {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)} (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests) :
    (CompleteSegment.ownerPath prepared budget fits).vertices.length = 3 * prepared.subdivision.stepCount :=
  (congrArg List.length (CompleteSegment.ownerPath_vertices prepared budget fits)).trans
    ((traceVertices_length segment zeroEndpoint prepared.subdivision.requests).trans
      (congrArg (fun count : Nat => 3 * count) prepared.subdivision.requests_length))

end CompleteSegment

namespace PreparedPath.TraceLineage

variable {start middle finish : Canonical} {head : ClearSegment polynomial ambient start middle}
    {tail : ClearPath polynomial ambient middle finish} {owner : Owner (polynomial.eval start)}
    {within : head.WithinAmbient} (first : CompleteSegment head within owner)
    (budget : PreparedTraceBudget head zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint first.subdivision.requests)
    {middleOwner : Owner (polynomial.eval middle)} {rest : PreparedPath tail middleOwner}
    (finishOwnerEq : middleOwner = first.finishOwner) (remaining : PreparedPath.TraceLineage rest)

/-- The materialized split, original raw Trace and identical following path at one original segment boundary.

The exact whole-suffix identity includes its point, Owner and full path.
The supplied actual materialization is traversed once; all canonical
factory equations are proof arguments. Both the raw Trace and following
path retain complete heterogeneous identities to these actual pieces.
-/
@[expose] def HeadConsumer
    (materialized : OwnerPath polynomial start owner finish (PreparedPathGluing.finishOwner rest))
    (Result : Type u) :=
  (divided : OwnerPath.Split materialized) →
  divided = OwnerPath.splitAt (3 * first.subdivision.stepCount) materialized →
  (_same : divided.suffix =
    (⟨middle, first.finishOwner, remaining.ownerPath.reindexOwners finishOwnerEq rfl⟩ :
      OwnerPath.Suffix (PreparedPathGluing.finishOwner rest))) →
  (front : Trace budget first.subdivision fits) →
  HEq front.path divided.initial →
  (following : OwnerPath polynomial middle middleOwner finish (PreparedPathGluing.finishOwner rest)) →
  HEq following divided.suffix.path → following = remaining.ownerPath → Result

/-- Split the SAME actual path once at the original retained complete-segment boundary.

The original factory equation only identifies the boundary. Prefix and
suffix data are read from the computed split, then reindexed with whole
suffix identities. The raw Trace uses the original budget/fits cache;
neither the expected prefix nor the remaining path factory is executed.
-/
def withHead
    (materialized : OwnerPath polynomial start owner finish (PreparedPathGluing.finishOwner rest))
    (factory : materialized = (CompleteSegment.ownerPath first budget fits).append
      (remaining.ownerPath.reindexOwners finishOwnerEq rfl)) {Result : Type u}
    (consume : HeadConsumer first budget fits finishOwnerEq remaining materialized Result) : Result := by
  let divided := OwnerPath.splitAt (3 * first.subdivision.stepCount) materialized
  have countEq := (CompleteSegment.ownerPath_length first budget fits).symm
  have same : divided.suffix =
      (⟨middle, first.finishOwner, remaining.ownerPath.reindexOwners finishOwnerEq rfl⟩ :
        OwnerPath.Suffix (PreparedPathGluing.finishOwner rest)) :=
    OwnerPath.splitAt_suffix (3 * first.subdivision.stepCount) materialized
      (CompleteSegment.ownerPath first budget fits) (remaining.ownerPath.reindexOwners finishOwnerEq rfl)
      countEq factory
  let prefixPath := OwnerPath.Split.prefixCast divided same
  have prefixEq : prefixPath = CompleteSegment.ownerPath first budget fits :=
    OwnerPath.splitAt_prefix (3 * first.subdivision.stepCount) materialized
      (CompleteSegment.ownerPath first budget fits) (remaining.ownerPath.reindexOwners finishOwnerEq rfl)
      countEq factory same
  let front := CompleteSegment.asTrace first budget fits prefixPath prefixEq
  have frontKept : HEq front.path divided.initial :=
    (CompleteSegment.asTrace_heq first budget fits prefixPath prefixEq).trans
      (OwnerPath.Split.prefixCast_heq divided same)
  let following := (OwnerPath.Suffix.pathCast same).reindexOwners finishOwnerEq.symm rfl
  have followingEq : following = remaining.ownerPath :=
    (congrArg (fun kept : OwnerPath polynomial middle first.finishOwner finish
        (PreparedPathGluing.finishOwner rest) => kept.reindexOwners finishOwnerEq.symm rfl)
      (OwnerPath.Suffix.pathCast_eq same)).trans
      (OwnerPath.reindexOwners_inverse finishOwnerEq rfl remaining.ownerPath)
  have followingKept : HEq following divided.suffix.path :=
    (OwnerPath.castEndpoints_heq rfl rfl (heq_of_eq finishOwnerEq.symm) (heq_of_eq rfl)
      (OwnerPath.Suffix.pathCast same)).trans (OwnerPath.Suffix.pathCast_heq same)
  exact consume divided rfl same front frontKept following followingKept followingEq

/-- Reindex the SAME supplied whole-lineage path and consume its actual first segment and unchanged tail.

The original cons lineage supplies the precise outer finish-Owner
transport. Its proof is reversed on the actual materialized input before
the shared splitting operation. No Owner or path is recovered by running
that lineage's canonical factory.
-/
def withCons
    (materialized : OwnerPath polynomial start owner finish
      (PreparedPathGluing.finishOwner
        (PreparedPath.cons head tail owner within first (PreparedPath.castOwner finishOwnerEq rest))))
    (factory : materialized =
      (PreparedPath.TraceLineage.cons (first := first) (rest := rest)
        budget fits finishOwnerEq remaining).ownerPath) {Result : Type u}
    (consume : HeadConsumer first budget fits finishOwnerEq remaining
      (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) Result) : Result := by
  let displayed := materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)
  have displayedEq : displayed = (CompleteSegment.ownerPath first budget fits).append
      (remaining.ownerPath.reindexOwners finishOwnerEq rfl) :=
    (congrArg (fun kept : OwnerPath polynomial start owner finish
      (PreparedPathGluing.finishOwner
        (PreparedPath.cons head tail owner within first (PreparedPath.castOwner finishOwnerEq rest))) =>
      kept.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) factory).trans
      (OwnerPath.reindexOwners_inverse rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest).symm
        ((CompleteSegment.ownerPath first budget fits).append
          (remaining.ownerPath.reindexOwners finishOwnerEq rfl)))
  exact withHead first budget fits finishOwnerEq remaining displayed displayedEq consume

/-- The actual retained first materialized split, raw Trace and following path with their complete certificates.

Existing dependent products store the same eight fields described by
HeadConsumer. The supplied split owns both literal path pieces, while
whole suffix equality and HEq retain the original raw Trace and following
OwnerPath. No observation, numerical request or replacement owner occurs.
-/
@[expose] def Head
    (materialized : OwnerPath polynomial start owner finish (PreparedPathGluing.finishOwner rest)) :=
  Σ divided : {value : OwnerPath.Split materialized //
    value = OwnerPath.splitAt (3 * first.subdivision.stepCount) materialized},
  Σ _same : PLift (divided.val.suffix =
    (⟨middle, first.finishOwner, remaining.ownerPath.reindexOwners finishOwnerEq rfl⟩ :
      OwnerPath.Suffix (PreparedPathGluing.finishOwner rest))),
  Σ _front : {value : Trace budget first.subdivision fits // HEq value.path divided.val.initial},
  {following : OwnerPath polynomial middle middleOwner finish (PreparedPathGluing.finishOwner rest) //
    HEq following divided.val.remaining ∧ following = remaining.ownerPath}

namespace Head

/-- Retain the existing materialized-head callback values as the same complete finite cache. -/
private def pack
    (materialized : OwnerPath polynomial start owner finish (PreparedPathGluing.finishOwner rest)) :
    HeadConsumer first budget fits finishOwnerEq remaining materialized
      (Head first budget fits finishOwnerEq remaining materialized) :=
  fun divided factory same front frontKept following followingKept followingFactory =>
    ⟨⟨divided, factory⟩, ⟨same⟩, ⟨front, frontKept⟩, ⟨following, followingKept, followingFactory⟩⟩

/-- Split the same original materialization once and retain its actual original complete-segment head.

The existing withCons producer constructs every path/Trace value and
certificate. Its callback stores those actual values; no canonical path
or trace factory is executed to recover a retained prefix or suffix.
-/
def build
    (materialized : OwnerPath polynomial start owner finish
      (PreparedPathGluing.finishOwner
        (PreparedPath.cons head tail owner within first (PreparedPath.castOwner finishOwnerEq rest))))
    (factory : materialized =
      (PreparedPath.TraceLineage.cons (first := first) (rest := rest)
        budget fits finishOwnerEq remaining).ownerPath) :
    Head first budget fits finishOwnerEq remaining
      (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) :=
  withCons first budget fits finishOwnerEq remaining materialized factory
    (pack first budget fits finishOwnerEq remaining
      (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)))

variable {first budget fits finishOwnerEq remaining}
variable {materialized : OwnerPath polynomial start owner finish (PreparedPathGluing.finishOwner rest)}
variable (retained : Head first budget fits finishOwnerEq remaining materialized)

/-- Read the same original raw Trace stored in the retained complete-segment head. -/
@[expose] def front : Trace budget first.subdivision fits := retained.2.2.1.val

/-- Read the actual unchanged following OwnerPath owned by the retained split. -/
@[expose] def following : OwnerPath polynomial middle middleOwner finish (PreparedPathGluing.finishOwner rest) :=
  retained.2.2.2.val

/-- The retained following path has its exact original whole-lineage factory. -/
theorem following_eq : retained.following = remaining.ownerPath := retained.2.2.2.property.2

/-- Consume the same retained split, raw Trace and following path through the original callback contract.

Every original factory, suffix equality and whole-path HEq is forwarded
unchanged. The callback sees the same complete values; no path split or
preparation executes when this cache is consumed.
-/
def withData {Result : Type u}
    (consume : HeadConsumer first budget fits finishOwnerEq remaining materialized Result) : Result :=
  consume retained.1.val retained.1.property retained.2.1.down
    retained.2.2.1.val retained.2.2.1.property
    retained.2.2.2.val retained.2.2.2.property.1 retained.2.2.2.property.2

/-- The retained-head eliminator applies the callback to exactly its stored original values and certificates. -/
theorem withData_eq {Result : Type u}
    (consume : HeadConsumer first budget fits finishOwnerEq remaining materialized Result) :
    retained.withData consume =
      consume retained.1.val retained.1.property retained.2.1.down
        retained.2.2.1.val retained.2.2.1.property
        retained.2.2.2.val retained.2.2.2.property.1 retained.2.2.2.property.2 := by
  unfold withData
  rfl

/-- Building and consuming the actual head cache gives the original complete materialized-head operation. -/
theorem build_withData
    (path : OwnerPath polynomial start owner finish
      (PreparedPathGluing.finishOwner
        (PreparedPath.cons head tail owner within first (PreparedPath.castOwner finishOwnerEq rest))))
    (factory : path =
      (PreparedPath.TraceLineage.cons (first := first) (rest := rest)
        budget fits finishOwnerEq remaining).ownerPath) {Result : Type u}
    (consume : HeadConsumer first budget fits finishOwnerEq remaining
      (path.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) Result) :
    (build first budget fits finishOwnerEq remaining path factory).withData consume =
      withCons first budget fits finishOwnerEq remaining path factory consume := by
  unfold build withCons withHead pack withData
  rfl

end Head

end PreparedPath.TraceLineage

end Purelib.Riemann.Paths.PreparedPathTrace

end
