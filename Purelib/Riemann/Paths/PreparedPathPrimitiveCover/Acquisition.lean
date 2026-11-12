module

public import Purelib.RootIsolation.SquareRoot.Preparation.Terminal.Width.Acquisition
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.AccuracyRequest
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Polynomial.Geometry.ClearPath

/-! # Original covered paths from retained width-paid acquisitions

Each original physical edge acquires its primitive/trace budget and actual
width-paid subdivision once. The original chosen mesh and TracedSegment
factory are retained. Their exact stored finish Owner is the next edge's
source. One original CoveredTracedPath is assembled from this cache spine;
no relation to an older acquisition or covered-path factory is asserted.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels

namespace CoveredTracedPath

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint oneEndpoint CompleteSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath TracedSegment)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Preparation.Terminal.AcquiredDyadic (WidthAcquisition)

namespace Acquisition

variable {polynomial : GaussianPolynomial} {ambient : Box} {start middle finish : Canonical}
variable {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
variable {owner : Owner (polynomial.eval start)}

-- Coordinate formulas are unnecessary while elaborating these original owner indices.
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- The original whole automatic budget and width-paid acquisition result for one actual segment. -/
@[expose] def Prepared (request : AccuracyRequest) :=
  Σ budget : { retained : PrimitiveTraceBudget segment // retained = PrimitiveTraceBudget.build segment },
    WidthAcquisition (within := within) (owner := owner) budget.val request

/-- The complete preparation is the original automatic factory on the same segment, owner and width request. -/
@[irreducible, expose] def PreparedCache (request : AccuracyRequest)
    (retained : Prepared (segment := segment) (within := within) (owner := owner) request) : Prop :=
  retained = WidthAcquisition.prepare segment within owner request

namespace Prepared

variable {request : AccuracyRequest}
variable (retained : Prepared (segment := segment) (within := within) (owner := owner) request)

/-- Read the identical original primitive/trace budget computed by the automatic preparation. -/
@[expose] def budget := retained.1.val

/-- Read the entire original width-paid acquisition with its original chosen-depth and terminal caches. -/
@[expose] def paid : WidthAcquisition (within := within) (owner := owner) retained.budget request := retained.2

/-- Read the original acquired requests, prepared subdivision and cached terminal Owner unchanged. -/
@[expose] def acquired := retained.paid.acquired

/-- The actual stored subdivision inherits the original acquisition's internally derived trace request fit. -/
theorem fits : retained.budget.trace.RequestsFit zeroEndpoint retained.acquired.prepared.subdivision.requests := by
  rewrite [← retained.acquired.requests_eq]
  exact retained.paid.requestsFit

/-- The same stored subdivision inherits the computed physical width payment on its identical requests. -/
theorem widths : Branches.PreparedSheetContinuation.Subdivision.WidthsFit request.tolerance zeroEndpoint
    retained.acquired.prepared.subdivision.requests := by
  rewrite [← retained.acquired.requests_eq]
  exact retained.paid.widthsFit

end Prepared

/-- The retained mesh is the original view at the actual chosen depth and unchanged primitive bounds. -/
@[irreducible, expose] def MeshCache {request : AccuracyRequest}
    (retained : Prepared (segment := segment) (within := within) (owner := owner) request)
    (mesh : Mesh retained.budget.bounds) : Prop := mesh = retained.paid.mesh

/-- The retained trace is the original whole factory on the same requests, prepared path and stored finish Owner. -/
@[irreducible, expose] def TraceCache {request : AccuracyRequest}
    (retained : Prepared (segment := segment) (within := within) (owner := owner) request)
    (traced : TracedSegment segment within owner) : Prop :=
  traced = TracedSegment.ofPrepared retained.budget.trace retained.acquired.prepared retained.fits
    retained.acquired.requests retained.acquired.requests_eq
    retained.acquired.finishOwner retained.acquired.finishOwner_eq

/-- One actual segment retains its complete automatic preparation, mesh and original trace factory result. -/
@[expose] def Segment (request : AccuracyRequest) :=
  Σ prepared : { retained : Prepared (segment := segment) (within := within) (owner := owner) request //
      PreparedCache request retained },
    Σ _mesh : { retained : Mesh prepared.val.budget.bounds // MeshCache prepared.val retained },
      { traced : TracedSegment segment within owner // TraceCache prepared.val traced }

namespace Segment

variable {request : AccuracyRequest}

/-- Retain completed original acquisition, mesh and trace caches without repeating any acquisition or trace factory. -/
@[expose] def ofCompleted
    (prepared : Prepared (segment := segment) (within := within) (owner := owner) request)
    (prepared_eq : PreparedCache request prepared)
    (mesh : Mesh prepared.budget.bounds) (mesh_eq : MeshCache prepared mesh)
    (traced : TracedSegment segment within owner) (traced_eq : TraceCache prepared traced) :
    Segment (segment := segment) (within := within) (owner := owner) request :=
  ⟨⟨prepared, prepared_eq⟩, ⟨⟨mesh, mesh_eq⟩, ⟨traced, traced_eq⟩⟩⟩

/-- Acquire one width-paid original segment and retain its actual original mesh and trace factories once. -/
def build (request : AccuracyRequest) : Segment (segment := segment) (within := within) (owner := owner) request :=
  let prepared := WidthAcquisition.prepare segment within owner request
  let mesh := prepared.2.mesh
  let traced := TracedSegment.ofPrepared prepared.1.val.trace prepared.2.acquired.prepared
    (Prepared.fits prepared) prepared.2.acquired.requests prepared.2.acquired.requests_eq
    prepared.2.acquired.finishOwner prepared.2.acquired.finishOwner_eq
  ofCompleted prepared (by unfold PreparedCache; rfl) mesh (by unfold MeshCache; rfl)
    traced (by unfold TraceCache; rfl)

variable (retained : Segment (segment := segment) (within := within) (owner := owner) request)

/-- Read the same complete original budget/acquisition result retained for this physical edge. -/
@[expose] def prepared := retained.1.val

/-- Read the identical original primitive mesh at that same acquired depth. -/
@[expose] def mesh : Mesh retained.prepared.budget.bounds := retained.2.1.val

/-- Read the complete original TracedSegment passed to the actual covered-path construction. -/
@[expose] def traced : TracedSegment segment within owner := retained.2.2.val

/-- The stored complete preparation has the exact original automatic-factory identity. -/
theorem prepared_eq : retained.prepared = WidthAcquisition.prepare segment within owner request := by
  have cache := retained.1.property
  unfold PreparedCache at cache
  exact cache

/-- The stored mesh is the original view of the same retained acquisition. -/
theorem mesh_eq : retained.mesh = retained.prepared.paid.mesh := by
  have cache := retained.2.1.property
  unfold MeshCache at cache
  exact cache

/-- The stored whole trace is the original factory on the exact acquired requests and finishing Owner. -/
theorem traced_eq : retained.traced =
    TracedSegment.ofPrepared retained.prepared.budget.trace retained.prepared.acquired.prepared
      retained.prepared.fits retained.prepared.acquired.requests retained.prepared.acquired.requests_eq
      retained.prepared.acquired.finishOwner retained.prepared.acquired.finishOwner_eq := by
  have cache := retained.2.2.property
  unfold TraceCache at cache
  exact cache

/-- The whole retained trace uses the identical acquired complete preparation. -/
theorem traced_prepared_eq : retained.traced.prepared = retained.prepared.acquired.prepared := by
  rewrite [retained.traced_eq]
  rfl

/-- The source handed to the next physical edge is exactly the cached acquired finish Owner. -/
theorem traced_finishOwner_eq : retained.traced.finishOwner = retained.prepared.acquired.finishOwner := by
  rewrite [retained.traced_eq]
  rfl

/-- The actual cached trace finish names the same root as its retained acquired subdivision's terminal Owner. -/
theorem finishName_eq :
    ownerRootName retained.traced.finishOwner.parameterNonzero retained.traced.finishOwner =
      ownerRootName retained.prepared.acquired.prepared.subdivision.terminalOwner.parameterNonzero
        retained.prepared.acquired.prepared.subdivision.terminalOwner := by
  rewrite [retained.traced_finishOwner_eq, retained.prepared.acquired.finishOwner_eq]
  unfold CompleteSegment.finishOwner CompleteSegment.terminalOwner
  exact SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ _

/-- The original primitive mesh covers the exact prepared edges stored in the retained trace. -/
theorem edges_eq : retained.traced.prepared.subdivision.parameterEdges = retained.mesh.edges := by
  rewrite [retained.traced_prepared_eq, retained.mesh_eq]
  exact retained.prepared.paid.mesh_eq

end Segment

variable (width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest)

/-- A finite acquisition spine follows the original clear path and every exact cached finish-owner handoff.

Only the original ClearPath is matched. A head retains the entire original
segment acquisition/mesh/trace cache. Its stored actual finish Owner is the
next acquisition's source index; no canonicalized substitute is introduced.
-/
@[expose] def Spine
    (width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest) :
    {start finish : Canonical} →
    (path : ClearPath polynomial ambient start finish) → path.WithinAmbient →
    Owner (polynomial.eval start) → Type 1
  | _, _, .nil _, _, _ => PUnit
  | _, _, .cons head tail, within, owner =>
      Σ first : Segment (segment := head) (within := within.head) (owner := owner) (width head),
        Spine width tail within.tail first.traced.finishOwner

namespace Spine

/-- Acquire each actual physical edge once, passing its retained finish Owner directly to the same original tail. -/
def build
    (width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest) :
    {start finish : Canonical} →
    (path : ClearPath polynomial ambient start finish) → (within : path.WithinAmbient) →
    (owner : Owner (polynomial.eval start)) → Spine width path within owner
  | _, _, .nil _point, _within, _owner => PUnit.unit
  | _, _, .cons head tail, within, owner =>
      let first := Segment.build (segment := head) (within := within.head) (owner := owner) (width head)
      let following := build width tail within.tail first.traced.finishOwner
      ⟨first, following⟩

/-- Assemble the original covered path from retained acquisitions without acquiring another root. -/
@[expose] def assemble
    (width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest) :
    {start finish : Canonical} →
    (path : ClearPath polynomial ambient start finish) → (within : path.WithinAmbient) →
    (owner : Owner (polynomial.eval start)) → Spine width path within owner → CoveredTracedPath path owner
  | _, _, .nil point, _within, owner, _retained =>
      ⟨TracedPath.build (.nil point) (.nil point) owner, .nil point owner⟩
  | _, _, .cons _head tail, within, _owner, retained =>
      let first := retained.1
      let rest := assemble width tail within.tail first.traced.finishOwner retained.2
      ⟨TracedPath.cons first.traced rest.traced,
        .cons first.prepared.budget.bounds first.mesh first.edges_eq
          (rest.cover.castOwner first.traced.finishOwner_eq)⟩

/-- An empty paid path keeps its exact supplied original source Owner as the finishing Owner. -/
theorem assemble_nil_finishOwner (point : Canonical) (owner : Owner (polynomial.eval point))
    (within : (ClearPath.nil (polynomial := polynomial) (ambient := ambient) point).WithinAmbient)
    (retained : Spine width (.nil point) within owner) :
    (assemble width (.nil point) within owner retained).traced.finishOwner = owner := rfl

variable {start middle finish : Canonical}
variable {headSegment : ClearSegment polynomial ambient start middle}
variable {tailPath : ClearPath polynomial ambient middle finish}
variable {within : (ClearPath.cons headSegment tailPath).WithinAmbient}
variable {owner : Owner (polynomial.eval start)}

/-- Read the same entire acquired segment cache at the original path head. -/
@[expose] def head (retained : Spine width (.cons headSegment tailPath) within owner) :
    Segment (segment := headSegment) (within := within.head) (owner := owner) (width headSegment) := retained.1

/-- Read the identical retained tail, whose source is the exact stored first trace's finishing Owner. -/
@[expose] def tail (retained : Spine width (.cons headSegment tailPath) within owner) :
    Spine width tailPath within.tail (Spine.head width retained).traced.finishOwner := retained.2

/-- The assembled nonempty path retains the identical first trace and actual assembled tail. -/
theorem assemble_cons_traced (retained : Spine width (.cons headSegment tailPath) within owner) :
    (assemble width (.cons headSegment tailPath) within owner retained).traced =
      TracedPath.cons (Spine.head width retained).traced
        (assemble width tailPath within.tail (Spine.head width retained).traced.finishOwner
          (Spine.tail width retained)).traced := rfl

/-- The assembled path ends at the same cached Owner as its actual assembled tail. -/
theorem assemble_cons_finishOwner (retained : Spine width (.cons headSegment tailPath) within owner) :
    (assemble width (.cons headSegment tailPath) within owner retained).traced.finishOwner =
      (assemble width tailPath within.tail (Spine.head width retained).traced.finishOwner
        (Spine.tail width retained)).traced.finishOwner := rfl

end Spine

end Acquisition

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
variable (width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest)
variable (path : ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
variable (owner : Owner (polynomial.eval start))

/-- A complete new width-paid covered acquisition retains its whole spine and original assembled covered path.

The original CoveredTracedPath, actual source/finish Owners and complete
request/trace/mesh caches are retained together. The factory equation is for
this new paid construction; no equality to an older unpaid execution is a
field or conclusion.
-/
@[expose] def Acquisition :=
  Σ spine : { retained : Acquisition.Spine width path within owner //
      retained = Acquisition.Spine.build width path within owner },
    { covered : CoveredTracedPath path owner //
      covered = Acquisition.Spine.assemble width path within owner spine.val }

namespace Acquisition

/-- Retain completed original acquisition and covered-path caches without executing either factory again. -/
@[expose] def ofCompleted (spine : Spine width path within owner)
    (spine_eq : spine = Spine.build width path within owner)
    (covered : CoveredTracedPath path owner) (covered_eq : covered = Spine.assemble width path within owner spine) :
    Acquisition width path within owner := ⟨⟨spine, spine_eq⟩, ⟨covered, covered_eq⟩⟩

/-- Construct a total width-paid covered path from the original admitted geometry and exact supplied source Owner. -/
def build : Acquisition width path within owner :=
  let spine := Spine.build width path within owner
  let covered := Spine.assemble width path within owner spine
  ofCompleted width path within owner spine rfl covered rfl

variable {width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest}
variable {path : ClearPath polynomial ambient start finish} {within : path.WithinAmbient}
variable {owner : Owner (polynomial.eval start)}
variable (retained : Acquisition width path within owner)

/-- Read the identical whole acquisition spine with all original per-edge requests and actual terminal caches. -/
@[expose] def spine : Spine width path within owner := retained.1.val

/-- Read the complete original CoveredTracedPath assembled once from that same actual acquisition spine. -/
@[expose] def covered : CoveredTracedPath path owner := retained.2.val

/-- The retained spine is the whole original per-edge acquisition factory on the same width assignment and geometry. -/
theorem spine_eq : retained.spine = Spine.build width path within owner := retained.1.property

/-- The retained covered path is the exact assembly of those same whole acquisition and trace caches. -/
theorem covered_eq : retained.covered = Spine.assemble width path within owner retained.spine := retained.2.property

end Acquisition

end CoveredTracedPath

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels
