module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace
public import Purelib.Riemann.Paths.OwnerTracePath.Suffix
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # Root comparison caches on the same materialized subdivision trace

The original OwnerPath factory equality aligns three actual links with each
original accepted request: source preparation, moving transport and reserve
retention. Their actual suffixes supply the moving Owner and unchanged
following trace. No transport or advance is executed to recover those
Owners. Comparison data follow the same original subdivision and cache a
shared independent reference once at each actual endpoint.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest Endpoint)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath (Suffix)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} (budget : PreparedTraceBudget segment first last)

/-- A materialized actual OwnerPath with the whole original subdivision-trace factory equality. -/
@[expose] def Trace {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (fits : budget.RequestsFit current subdivision.requests) :=
  { path : OwnerPath polynomial (segment.pointAt current.parameter) owner
      (segment.pointAt subdivision.endpoint.parameter) subdivision.terminalOwner //
    path = ownerPath budget subdivision fits }

namespace Trace

variable {budget} {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current owner} {fits : budget.RequestsFit current subdivision.requests}

/-- Complete original factory certificates identify the SAME whole materialized Trace value.

Both input Traces retain their actual whole OwnerPath and original
subdivision/budget factory. This equality executes neither canonical
path factory and infers no Owner identity from coordinates or labels.
-/
theorem eq_of_factories (first last : Trace budget subdivision fits) : first = last := by
  rcases first with ⟨first, firstFactory⟩
  rcases last with ⟨last, lastFactory⟩
  have same : first = last := firstFactory.trans lastFactory.symm
  cases same
  rfl

/-- Retain an already materialized original path and its exact factory identity without executing that factory. -/
@[expose] def ofCompleted
    (path : OwnerPath polynomial (segment.pointAt current.parameter) owner
      (segment.pointAt subdivision.endpoint.parameter) subdivision.terminalOwner)
    (path_eq : path = ownerPath budget subdivision fits) : Trace budget subdivision fits := ⟨path, path_eq⟩

/-- Read the entire same materialized original trace. -/
@[expose] def path (trace : Trace budget subdivision fits) := trace.val

/-- The actual complete trace is the original factory on this SAME subdivision, budget and fit certificate. -/
theorem path_eq (trace : Trace budget subdivision fits) : trace.path = ownerPath budget subdivision fits :=
  trace.property

end Trace

/-- Read the actual successful suffix value, with its exact original Option equation.

The presence proof is derived from the complete trace-factory equality.
Only the original Option is inspected; no expected suffix value or factory
is an executable argument to this extraction.
-/
private def takeSuffix {point : Canonical} {owner : Owner (polynomial.eval point)}
    (actual : Option (Suffix owner)) (present : actual.isSome = true) :
    { suffix : Suffix owner // actual = some suffix } :=
  match actual with
  | none => False.elim (by cases present)
  | some suffix => ⟨suffix, rfl⟩

namespace Trace

section Accepted

variable (current : Endpoint) (inherited : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (cached : CachedSource segment current inherited request)
    (ordered : current.parameter ≤ request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within current inherited request small))
    (fits : budget.RequestsFit current
      (Subdivision.next current inherited request cached ordered small remaining).requests)

/-- The first original canonical suffix, used only to certify the actual materialized trace's head shape. -/
private def canonicalSource :=
  (takeSuffix
    ((ownerPath budget (Subdivision.next current inherited request cached ordered small remaining) fits).dropLink)
    (by rfl)).val

/-- The second original canonical suffix, used only in exact moving-index readbacks. -/
private def canonicalMoving :=
  (takeSuffix ((canonicalSource budget current inherited request cached ordered small remaining fits).path.dropLink)
    (by rfl)).val

/-- The third original canonical suffix, used only in the exact retained-tail readback. -/
private def canonicalTail :=
  (takeSuffix ((canonicalMoving budget current inherited request cached ordered small remaining fits).path.dropLink)
    (by rfl)).val

/-- Three actual suffix caches of the SAME original trace at one original accepted request.

The first follows source preparation, the second retains the moving Owner,
and the third is the exact original following trace. Every equality links
an actual stored suffix to the original constructor projection, rather
than accepting a free owner-alignment or endpoint-equivalence certificate.
-/
@[expose] def View
    (trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits) :=
  (source : { suffix : Suffix remaining.terminalOwner // trace.path.dropLink = some suffix }) ×
  (moving : { suffix : Suffix remaining.terminalOwner // source.val.path.dropLink = some suffix }) ×
  { tail : Suffix remaining.terminalOwner // moving.val.path.dropLink = some tail }

namespace View

variable {budget current inherited request cached ordered small remaining fits}

/-- Extract each actual source, moving and retained-tail suffix once from the SAME materialized original trace. -/
def build (trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits) :
    View budget current inherited request cached ordered small remaining fits trace := by
  let source := takeSuffix trace.path.dropLink (by rewrite [trace.path_eq]; rfl)
  have source_eq : source.val =
      canonicalSource budget current inherited request cached ordered small remaining fits := by
    apply Option.some.inj
    exact source.property.symm.trans (by rewrite [trace.path_eq]; rfl)
  let moving := takeSuffix source.val.path.dropLink (by rewrite [source_eq]; rfl)
  have moving_eq : moving.val =
      canonicalMoving budget current inherited request cached ordered small remaining fits := by
    apply Option.some.inj
    exact moving.property.symm.trans (by rewrite [source_eq]; rfl)
  let tail := takeSuffix moving.val.path.dropLink (by rewrite [moving_eq]; rfl)
  exact ⟨source, moving, tail⟩

variable {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits}
    (view : View budget current inherited request cached ordered small remaining fits trace)

/-- Read the complete actual source suffix after the original source-preparation link. -/
@[expose] def source : Suffix remaining.terminalOwner := view.1.val

/-- Read the complete actual suffix at the original moving/retention seam, including its actual moving Owner. -/
@[expose] def moving : Suffix remaining.terminalOwner := view.2.1.val

/-- Read the SAME original tail after the actual reserve-retention link. -/
@[expose] def tail : Suffix remaining.terminalOwner := view.2.2.val

/-- The stored original source suffix has the complete original canonical constructor identity. -/
private theorem source_eq : view.source =
    canonicalSource budget current inherited request cached ordered small remaining fits := by
  apply Option.some.inj
  exact view.1.property.symm.trans (by rewrite [trace.path_eq]; rfl)

/-- The stored moving suffix has the complete original canonical constructor identity. -/
private theorem moving_eq : view.moving =
    canonicalMoving budget current inherited request cached ordered small remaining fits := by
  apply Option.some.inj
  exact view.2.1.property.symm.trans
    ((congrArg (fun suffix : Suffix remaining.terminalOwner => suffix.path.dropLink) view.source_eq).trans (by rfl))

/-- The stored following suffix has the complete original canonical constructor identity. -/
private theorem tail_eq : view.tail =
    canonicalTail budget current inherited request cached ordered small remaining fits := by
  apply Option.some.inj
  exact view.2.2.property.symm.trans
    ((congrArg (fun suffix : Suffix remaining.terminalOwner => suffix.path.dropLink) view.moving_eq).trans (by rfl))

/-- The actual source suffix remains at the same original prepared-source physical point. -/
theorem source_point : view.source.point = segment.pointAt current.parameter :=
  (congrArg Suffix.point view.source_eq).trans (by rfl)

/-- The source suffix carries exactly the original cached prepared Owner's root name. -/
theorem source_name_eq : ownerRootName view.source.owner.parameterNonzero view.source.owner =
    ownerRootName cached.preparedOwner.parameterNonzero cached.preparedOwner := by
  have equal := congrArg (fun suffix : Suffix remaining.terminalOwner =>
    ownerRootName suffix.owner.parameterNonzero suffix.owner) view.source_eq
  exact equal.trans (by rfl)

/-- The whole actual source-suffix Owner is the original cached prepared Owner up to its exact point index. -/
private theorem packaged_source_owner_heq : HEq view.source.owner cached.preparedOwner := by
  have aligned := Suffix.ownerCast_eq view.source_eq
  exact (Purelib.RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ _).symm.trans
    (heq_of_eq aligned)

/-- The whole actual source-suffix Owner is the original cached prepared Owner up to its exact point index. -/
theorem source_owner_heq : HEq view.source.owner cached.preparedOwner := packaged_source_owner_heq view

/-- The following actual tail starts at the literal accepted-request endpoint. -/
theorem tail_point : view.tail.point = segment.pointAt request.endpoint.parameter :=
  (congrArg Suffix.point view.tail_eq).trans (by rfl)

/-- The following actual tail carries the same stored remaining subdivision source Owner's root name. -/
theorem tail_name_eq : ownerRootName view.tail.owner.parameterNonzero view.tail.owner =
    ownerRootName remaining.sourceOwner.parameterNonzero remaining.sourceOwner := by
  have equal := congrArg (fun suffix : Suffix remaining.terminalOwner =>
    ownerRootName suffix.owner.parameterNonzero suffix.owner) view.tail_eq
  have stored := congrArg (fun owner => ownerRootName owner.parameterNonzero owner) remaining.sourceOwner_eq
  exact equal.trans (by exact stored.symm)

/-- The actual moving suffix remains at the literal original request endpoint. -/
theorem moving_point : view.moving.point = segment.pointAt request.endpoint.parameter :=
  (congrArg Suffix.point view.moving_eq).trans (by rfl)

/-- Read the actual moving Owner, changing only its exact physical-point index. -/
def movingOwner : Owner (polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
  castOwnerParameter (congrArg polynomial.eval view.moving_point) view.moving.owner

/-- The complete moving Owner is the original transported occurrence from this SAME source/request. -/
theorem movingOwner_eq : view.movingOwner =
    PreparedSheetContinuation.transported segment within current inherited request small := by
  unfold movingOwner
  exact Suffix.ownerCast_eq view.moving_eq

/-- The original moving-Owner index transport retains the entire actual input Owner. -/
theorem movingOwner_heq : HEq view.movingOwner view.moving.owner :=
  Purelib.RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ _

/-- Read the unchanged actual following trace at its original subdivision index.

Only the exact whole-suffix equality transports its nominal endpoint and
Owner indices. The original OwnerPath value is reused; the canonical
ownerPath factory occurs solely in its retained correctness equality.
-/
def tailTrace : Trace budget remaining fits.2.2 :=
  ⟨Suffix.pathCast view.tail_eq, Suffix.pathCast_eq view.tail_eq⟩

/-- The following trace retains the entire literal original suffix, including every Owner and link. -/
theorem tailTrace_heq : HEq view.tailTrace.path view.tail.path := Suffix.pathCast_heq view.tail_eq

/-- The following trace retains the complete original point/Owner/path suffix under its exact nominal reindex.

This whole tuple equation is stronger ownership evidence than endpoint
coordinates or path vertices. Its proof uses the same private original
suffix identity already consumed by tailTrace; no trace or Owner factory
is run to recover the source of the following trace.
-/
theorem tailTrace_suffix_eq :
    (⟨segment.pointAt request.endpoint.parameter,
      PreparedSheetContinuation.advance segment within current inherited request small,
      view.tailTrace.path⟩ : Suffix remaining.terminalOwner) = view.tail := by
  unfold tailTrace
  exact Suffix.pathCast_suffix view.tail_eq

end View

end Accepted

variable {budget}

/-- The original accepted-request trace views in their exact ordered spine.

Each head retains the existing three-suffix View and the unchanged actual
tail Trace. This reducible view contains no independent reference Owner,
RootPath or replacement continuation certificate.
-/
@[expose] def Views :
    ∀ {current : Endpoint}
      {inherited : Owner (polynomial.eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current inherited)
      (fits : budget.RequestsFit current subdivision.requests)
      (_trace : Trace budget subdivision fits), Type
  | _, _, .stop _ _, _, _ => PUnit
  | _, _, .next current inherited request cached ordered small remaining, fits, trace =>
      (view : View budget current inherited request cached ordered small remaining fits trace) ×
      Views remaining fits.2.2 view.tailTrace
termination_by structural _ _ subdivision _ _ => subdivision

namespace Views

/-- Retain the actual three-suffix views once on the same materialized original trace.

Only existing dropLink observations and their certified present values are
read. Recursion follows the original accepted-request subdivision and the
literal stored suffix; no continuation or root preparation is executed.
-/
def build {current : Endpoint}
    {inherited : Owner (polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current inherited)
    (fits : budget.RequestsFit current subdivision.requests)
    (trace : Trace budget subdivision fits) : Views subdivision fits trace :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) → Views subdivision fits trace)
    subdivision
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ remaining fits trace =>
      let view := View.build trace
      let tail := build remaining fits.2.2 view.tailTrace
      ⟨view, tail⟩)
    fits trace
termination_by structural subdivision

end Views

/-- An exact existing budget, fit certificate, materialized Trace and its retained ordered Views.

Only original owners occur in this dependent view. The budget endpoints
remain stored indices, while each accepted subdivision request and its
actual suffix data remain tied to the same supplied Trace.
-/
@[expose] def RootViews {current : Endpoint}
    {inherited : Owner (polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current inherited) :=
  (first : Endpoint) × (last : Endpoint) ×
  (budget : PreparedTraceBudget segment first last) ×
  (fits : PLift (budget.RequestsFit current subdivision.requests)) ×
  (trace : Trace budget subdivision fits.down) × Views subdivision fits.down trace

/-- Retain this same complete Trace and build its original suffix views once.

The existing budget, subdivision and fit certificate are passed literally;
no root Owner, trace path or numerical continuation is constructed again.
-/
def rootViews {current : Endpoint}
    {inherited : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits) : RootViews subdivision :=
  ⟨first, last, budget, ⟨fits⟩, trace, Views.build subdivision fits trace⟩

/-- The retained root-view input keeps the entire supplied original materialized Trace. -/
theorem rootViews_trace {current : Endpoint}
    {inherited : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits) : HEq trace.rootViews.2.2.2.2.1 trace := by
  unfold rootViews
  rfl

end Trace

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget

end
