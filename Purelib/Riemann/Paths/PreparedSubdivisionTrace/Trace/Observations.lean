module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootPath
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Head
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Paid old observations at one actual source/moving/reset occurrence

The retained View supplies three literal dropLink equations. The old
observation spine follows those exact constructors once, exposing every
original Vertex and Stationary.Step. No suffix is inferred from parent
coordinates, and no source, moving or reset cache is prepared again.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace.View

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest Endpoint)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
variable {first last current : Endpoint} {budget : PreparedTraceBudget segment first last}
variable {inherited : Owner (polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits}
variable (view : View budget current inherited request cached ordered small remaining fits trace)
variable {expression : Expression polynomial} {accuracy : AccuracyRequest}
variable (observed : Primitive.Spine expression accuracy trace.path)

/-- Three complete original head splits share the SAME old View, expression, accuracy and observation execution.

Each head stores its actual link and split factory. The moving and reset
readers receive the exact preceding old suffix, not a newly built path or
an independently sampled endpoint. The old tail remains at its literal
stored Suffix indices.
-/
@[expose] def Observations :=
  Σ source : {value : Primitive.Spine.Head observed view.source view.1.property //
    value = observed.atHead view.source view.1.property},
  Σ moving : {value : Primitive.Spine.Head source.val.after view.moving view.2.1.property //
    value = source.val.after.atHead view.moving view.2.1.property},
  {value : Primitive.Spine.Head moving.val.after view.tail view.2.2.property //
    value = moving.val.after.atHead view.tail view.2.2.property}

/-- Read the original source, moving and reset observations once from this actual retained View and old spine. -/
def observations : view.Observations observed :=
  let source := observed.atHead view.source view.1.property
  let moving := source.after.atHead view.moving view.2.1.property
  let reset := moving.after.atHead view.tail view.2.2.property
  ⟨⟨source, rfl⟩, ⟨moving, rfl⟩, ⟨reset, rfl⟩⟩

namespace Observations

variable {view observed} (kept : view.Observations observed)

/-- Read the original complete source-handoff observation and unchanged following spine. -/
abbrev source : Primitive.Spine.Head observed view.source view.1.property := kept.1.val

/-- Read the original moving-link observation, preserving both old endpoint Vertices. -/
abbrev moving : Primitive.Spine.Head kept.source.after view.moving view.2.1.property := kept.2.1.val

/-- Read the distinct original retention-reset observation on the same actual moving and tail Owners. -/
abbrev reset : Primitive.Spine.Head kept.moving.after view.tail view.2.2.property := kept.2.2.val

/-- Read the complete unchanged old suffix after the actual retention link. -/
abbrev tail : Primitive.Spine expression accuracy view.tail.path := kept.reset.after

/-- The entire source split is its original reader on this SAME old observation and View occurrence. -/
theorem source_eq : kept.source = observed.atHead view.source view.1.property := kept.1.property

/-- The moving split consumes the identical old suffix already retained by the source split. -/
theorem moving_eq : kept.moving = kept.source.after.atHead view.moving view.2.1.property := kept.2.1.property

/-- The reset split consumes the identical old suffix retained at the moving observation. -/
theorem reset_eq : kept.reset = kept.moving.after.atHead view.tail view.2.2.property := kept.2.2.property

/-- The final old Vertex survives all three exact source/moving/reset splits without resampling. -/
theorem last_eq : kept.tail.last = observed.last :=
  kept.reset.last_eq.trans (kept.moving.last_eq.trans kept.source.last_eq)

/-- Transport the SAME whole old suffix to the exact following materialized Trace index.

The original whole-suffix equation moves its point, source Owner and path
together. Every old Vertex and Stationary.Step crosses unchanged; the
operation constructs neither an observation nor a continuation cache.
-/
def following : Primitive.Spine expression accuracy view.tailTrace.path :=
  Eq.mpr (congrArg (fun suffix : Suffix remaining.terminalOwner =>
    Primitive.Spine expression accuracy suffix.path) view.tailTrace_suffix_eq) kept.tail

/-- The whole following observation execution remains the same original old suffix heterogeneously. -/
theorem following_heq : HEq kept.following kept.tail := by
  unfold following
  exact cast_heq _ _

/-- Exact suffix transport retains the literal old terminal Vertex, including its original observation request. -/
private theorem transport_last {first second : Suffix remaining.terminalOwner} (same : first = second)
    (old : Primitive.Spine expression accuracy second.path) :
    (Eq.mpr (congrArg (fun suffix : Suffix remaining.terminalOwner =>
      Primitive.Spine expression accuracy suffix.path) same) old).last = old.last := by
  cases same
  rfl

/-- Whole original suffix transport preserves the exact old source value without re-observing its Owner. -/
private theorem transport_first_value {first second : Suffix remaining.terminalOwner} (same : first = second)
    (old : Primitive.Spine expression accuracy second.path) :
    (Eq.mpr (congrArg (fun suffix : Suffix remaining.terminalOwner =>
      Primitive.Spine expression accuracy suffix.path) same) old).first.value = old.first.value := by
  cases same
  rfl

/-- The actual following Trace keeps the SAME literal old source value through its whole suffix/Owner identity. -/
theorem following_first_value : kept.following.first.value = kept.tail.first.value :=
  transport_first_value view.tailTrace_suffix_eq kept.tail

/-- The following materialized Trace carries the unchanged original final Vertex of the whole supplied old Spine. -/
theorem following_last : kept.following.last = observed.last :=
  (transport_last view.tailTrace_suffix_eq kept.tail).trans kept.last_eq

end Observations

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace.View

end
