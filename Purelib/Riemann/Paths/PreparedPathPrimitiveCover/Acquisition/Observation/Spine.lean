module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Observation
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Append
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Complete old segment observations on the same acquired physical path

Only the original acquisition spine and ClearPath are matched. Each actual
head/suffix split reuses the whole old observation caches. The literal head
Segment, its prepared subdivision and terminal Owner remain the original
inputs. Neither a primitive request nor a physical preparation is executed.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {polynomial : Coefficients} {ambient : Box} {start finish : Canonical}
variable {path : ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
variable {expression : Expression polynomial} {accuracy : AccuracyRequest}

namespace Observation

/-- Exact whole-Covered identity transports the entire old spine, including its dependent final Owner index. -/
@[expose, macro_inline] def cast {first last : CoveredTracedPath path owner} (same : first = last)
    (observed : Primitive.Spine expression accuracy first.traced.trace.get) :
    Primitive.Spine expression accuracy last.traced.trace.get := same ▸ observed

/-- Whole-Covered transport preserves every field of the complete supplied old observation execution. -/
theorem cast_heq {first last : CoveredTracedPath path owner} (same : first = last)
    (observed : Primitive.Spine expression accuracy first.traced.trace.get) :
    HEq (cast same observed) observed := by cases same; rfl

/-- The literal old source vertex is unchanged under exact whole-Covered transport. -/
theorem cast_first {first last : CoveredTracedPath path owner} (same : first = last)
    (observed : Primitive.Spine expression accuracy first.traced.trace.get) :
    (cast same observed).first = observed.first := by cases same; rfl

/-- The whole old returned vertex survives the original finishing-Owner reindex heterogeneously. -/
theorem cast_last_heq {first last : CoveredTracedPath path owner} (same : first = last)
    (observed : Primitive.Spine expression accuracy first.traced.trace.get) :
    HEq (cast same observed).last observed.last := by cases same; rfl

/-- The exact source index transport preserves its original selected scalar value. -/
theorem cast_first_value {first last : CoveredTracedPath path owner} (same : first = last)
    (observed : Primitive.Spine expression accuracy first.traced.trace.get) :
    (cast same observed).first.value = observed.first.value := by cases same; rfl

/-- The original finishing observation keeps its selected scalar value through the whole-Covered transport. -/
theorem cast_last_value {first last : CoveredTracedPath path owner} (same : first = last)
    (observed : Primitive.Spine expression accuracy first.traced.trace.get) :
    (cast same observed).last.value = observed.last.value := by cases same; rfl

end Observation

namespace Acquisition.Spine

variable (expression : Expression polynomial) (accuracy : AccuracyRequest)
variable (width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest)

/-- Each original physical segment retains its actual full head/suffix split and the same old suffix recursively.

The complete split stores both entire old spines and their literal shared
Vertex identity. Its factory consumes only the original supplied whole
spine. The original acquisition and endpoint Owner handoffs remain indices.
-/
@[expose] def Segments (expression : Expression polynomial) (accuracy : AccuracyRequest)
    (width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest) :
    {start finish : Canonical} →
    (path : ClearPath polynomial ambient start finish) → (within : path.WithinAmbient) →
    (owner : Owner (polynomial.eval start)) → (retained : Spine width path within owner) →
    Primitive.Spine expression accuracy (assemble width path within owner retained).traced.trace.get → Type 1
  | _, _, .nil _, _, _, _, _ => PUnit
  | _, _, .cons _head tail, within, _owner, retained, observed =>
      Σ divided : { cached : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
            retained.1.traced.trace.get
            (assemble width tail within.tail retained.1.traced.finishOwner retained.2).traced.trace.get //
          cached = Primitive.Spine.split retained.1.traced.trace.get
            (assemble width tail within.tail retained.1.traced.finishOwner retained.2).traced.trace.get observed },
        Segments expression accuracy width tail within.tail retained.1.traced.finishOwner retained.2 divided.val.after
termination_by structural _ _ path _ _ _ _ => path

namespace Segments

/-- Materialize the actual old segment views once while following the identical original physical acquisition spine. -/
def build (expression : Expression polynomial) (accuracy : AccuracyRequest)
    (width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest) :
    {start finish : Canonical} →
    (path : ClearPath polynomial ambient start finish) → (within : path.WithinAmbient) →
    (owner : Owner (polynomial.eval start)) → (retained : Spine width path within owner) →
    (observed : Primitive.Spine expression accuracy
      (assemble width path within owner retained).traced.trace.get) →
    Segments expression accuracy width path within owner retained observed
  | _, _, .nil _, _, _, _, _ => PUnit.unit
  | _, _, .cons _head tail, within, _owner, retained, observed =>
      let divided := Primitive.Spine.split retained.1.traced.trace.get
        (assemble width tail within.tail retained.1.traced.finishOwner retained.2).traced.trace.get observed
      let following := build expression accuracy width tail within.tail retained.1.traced.finishOwner
        retained.2 divided.after
      ⟨⟨divided, rfl⟩, following⟩
termination_by structural _ _ path _ _ _ _ => path

variable {expression accuracy width}
variable {middle : Canonical} {headSegment : ClearSegment polynomial ambient start middle}
variable {tailPath : ClearPath polynomial ambient middle finish}
variable {within : (ClearPath.cons headSegment tailPath).WithinAmbient}
variable {retained : Spine width (.cons headSegment tailPath) within owner}
variable {observed : Primitive.Spine expression accuracy
  (assemble width (.cons headSegment tailPath) within owner retained).traced.trace.get}
variable (views : Segments expression accuracy width (.cons headSegment tailPath) within owner retained observed)

/-- Read the actual stored full head/suffix split of this SAME old assembled observation spine. -/
@[expose] def divided : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    retained.1.traced.trace.get
    (assemble width tailPath within.tail retained.1.traced.finishOwner retained.2).traced.trace.get := views.1.val

/-- Read the complete old observation spine on this literal original physical Segment. -/
@[expose] def head : Primitive.Spine expression accuracy retained.1.traced.trace.get := views.divided.before

/-- Read the entire unchanged old suffix observation spine handed to the identical acquisition tail. -/
@[expose] def following : Primitive.Spine expression accuracy
    (assemble width tailPath within.tail retained.1.traced.finishOwner retained.2).traced.trace.get :=
  views.divided.after

/-- Read the same actual recursive view cache on the exact retained physical acquisition tail and old suffix. -/
@[expose] def tail : Segments expression accuracy width tailPath within.tail retained.1.traced.finishOwner
    retained.2 views.following := views.2

/-- The full split is the original split factory on the SAME stored head trace, tail trace and complete old spine. -/
theorem divided_eq : views.divided = Primitive.Spine.split retained.1.traced.trace.get
    (assemble width tailPath within.tail retained.1.traced.finishOwner retained.2).traced.trace.get observed :=
  views.1.property

/-- The old head and following suffix retain the SAME literal source/target observation cache. -/
theorem shared : views.following.first = views.head.last := views.divided.shared

/-- Splitting the original assembly preserves its entire literal old first vertex. -/
theorem head_first : views.head.first = observed.first :=
  (congrArg (fun divided : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    retained.1.traced.trace.get
    (assemble width tailPath within.tail retained.1.traced.finishOwner retained.2).traced.trace.get =>
      divided.before.first) views.divided_eq).trans (Primitive.Spine.split_first observed)

/-- The complete old suffix preserves the whole literal old returned vertex of the assembled physical path. -/
theorem following_last : views.following.last = observed.last :=
  (congrArg (fun divided : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    retained.1.traced.trace.get
    (assemble width tailPath within.tail retained.1.traced.finishOwner retained.2).traced.trace.get =>
      divided.after.last) views.divided_eq).trans (Primitive.Spine.split_last observed)

end Segments

/-- Count the exact original prepared moving requests across this SAME finite physical acquisition spine. -/
@[expose] def requestCount
    (width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest) :
    {start finish : Canonical} → (path : ClearPath polynomial ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner (polynomial.eval start)) →
    Spine width path within owner → Nat
  | _, _, .nil _, _, _, _ => 0
  | _, _, .cons _ tail, within, _owner, retained =>
      retained.1.traced.prepared.subdivision.requests.length +
        requestCount width tail within.tail retained.1.traced.finishOwner retained.2
termination_by structural _ _ path _ _ _ => path

end Acquisition.Spine

namespace Acquisition

variable {width : {start finish : Canonical} → ClearSegment polynomial ambient start finish → AccuracyRequest}
variable {within : path.WithinAmbient}
variable (retained : Acquisition width path within owner)
variable (observed : Primitive.Spine expression accuracy retained.covered.traced.trace.get)

/-- The SAME complete old physical spine and the actual segment split execution are retained with whole factory laws. -/
@[expose] def Observations :=
  Σ original : { old : Primitive.Spine expression accuracy retained.covered.traced.trace.get //
      old = observed },
    Σ aligned : { old : Primitive.Spine expression accuracy
          (Spine.assemble width path within owner retained.spine).traced.trace.get //
        old = Observation.cast retained.covered_eq original.val },
      { segments : Spine.Segments expression accuracy width path within owner retained.spine aligned.val //
        segments = Spine.Segments.build expression accuracy width path within owner retained.spine aligned.val }

namespace Observations

/-- Transport the complete old physical input once, then split its SAME stored acquisitions without observing again. -/
def build : Observations retained observed :=
  let aligned := Observation.cast retained.covered_eq observed
  let segments := Spine.Segments.build expression accuracy width path within owner retained.spine aligned
  ⟨⟨observed, rfl⟩, ⟨aligned, rfl⟩, ⟨segments, rfl⟩⟩

variable {observed}
variable (views : Observations retained observed)

/-- Read the complete supplied old physical observation execution, unchanged. -/
@[expose] def original : Primitive.Spine expression accuracy retained.covered.traced.trace.get :=
  views.1.val

/-- Read the identical old cache at its actual retained whole assembly index. -/
@[expose] def aligned : Primitive.Spine expression accuracy
    (Spine.assemble width path within owner retained.spine).traced.trace.get := views.2.1.val

/-- Read the complete actual segment-view cache on those SAME original acquisitions and old observations. -/
@[expose] def segments : Spine.Segments expression accuracy width path within owner retained.spine views.aligned :=
  views.2.2.val

/-- The old physical spine is the identical complete supplied input. -/
theorem original_eq : views.original = observed := views.1.property

/-- The whole aligned input is the exact original whole-Covered identity transport. -/
theorem aligned_eq : views.aligned = Observation.cast retained.covered_eq views.original := views.2.1.property

/-- The full segment split execution is its original factory on the SAME old input and retained acquisition spine. -/
theorem segments_eq : views.segments = Spine.Segments.build expression accuracy width path within owner
    retained.spine views.aligned := views.2.2.property

/-- The complete aligned observation cache is the supplied old physical input under exact nominal index transport. -/
theorem aligned_heq : HEq views.aligned observed :=
  (heq_of_eq views.aligned_eq).trans ((Observation.cast_heq retained.covered_eq views.original).trans
    (heq_of_eq views.original_eq))

/-- The source scalar is that of the SAME literal old physical source observation. -/
theorem first_value : views.aligned.first.value = observed.first.value :=
  (congrArg (fun old : Primitive.Spine expression accuracy
    (Spine.assemble width path within owner retained.spine).traced.trace.get => old.first.value) views.aligned_eq).trans
    ((Observation.cast_first_value retained.covered_eq views.original).trans
      (congrArg (fun old : Primitive.Spine expression accuracy
        retained.covered.traced.trace.get => old.first.value) views.original_eq))

/-- The returned scalar is that of the SAME original physical finish observation. -/
theorem last_value : views.aligned.last.value = observed.last.value :=
  (congrArg (fun old : Primitive.Spine expression accuracy
    (Spine.assemble width path within owner retained.spine).traced.trace.get => old.last.value) views.aligned_eq).trans
    ((Observation.cast_last_value retained.covered_eq views.original).trans
      (congrArg (fun old : Primitive.Spine expression accuracy
        retained.covered.traced.trace.get => old.last.value) views.original_eq))

end Observations

end Acquisition

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
