module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootPath
import Purelib.Riemann.Paths.OwnerTracePath.Suffix
public import Purelib.Riemann.Paths.OwnerTracePath.Split
public import Purelib.Riemann.Paths.OwnerTracePath.StationaryHead
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic

/-! # The three original pieces at one retained accepted Trace occurrence

The original View supplies three actual suffix equations. Direct head
readback retains the two stationary links and the moving link separately,
with their exact whole factories. The original stationary-link comparison
operations supply their root signs; no primitive offset is cancelled.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace.View

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest Endpoint)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] RootContinuation.CertifiedSquareRoot.rawRoot

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last current : Endpoint} {budget : PreparedTraceBudget segment first last}
    {inherited : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {cached : CachedSource segment current inherited request}
    {ordered : current.parameter ≤ request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
    {remaining : Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within current inherited request small)}
    {fits : budget.RequestsFit current
      (Subdivision.next current inherited request cached ordered small remaining).requests}
    {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits}
    (view : View budget current inherited request cached ordered small remaining fits trace)

/-- The original three actual head certificates, two stationary signs and their exact literal prefix.

Every head retains the SAME original path/suffix equation and its complete
headLink factory. The prefix is a literal constructor on those retained
links; its equality to the original path followed by tail is derived.
-/
@[expose] def Pieces :=
  (source : {value : {link : OwnerLink polynomial (segment.pointAt current.parameter) view.source.point
      inherited view.source.owner // trace.path = .cons link view.source.path} //
    value = trace.path.headLink view.source view.1.property}) ×
  (moving : {value : {link : OwnerLink polynomial view.source.point view.moving.point
      view.source.owner view.moving.owner // view.source.path = .cons link view.moving.path} //
    value = view.source.path.headLink view.moving view.2.1.property}) ×
  (retained : {value : {link : OwnerLink polynomial view.moving.point view.tail.point
      view.moving.owner view.tail.owner // view.moving.path = .cons link view.tail.path} //
    value = view.moving.path.headLink view.tail view.2.2.property}) ×
  (_sourceSign : {value : NamedEquivalent (ownerName inherited) (ownerName view.source.owner) //
    value = trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point}) ×
  (_retainedSign : {value : NamedEquivalent (ownerName view.moving.owner) (ownerName view.tail.owner) //
    value = view.moving.path.stationaryHeadEquivalent view.tail view.2.2.property
      (view.tail_point.trans view.moving_point.symm)}) ×
  {value : OwnerPath polynomial (segment.pointAt current.parameter) inherited view.tail.point view.tail.owner //
    value = .cons source.val.val (.cons moving.val.val
      (.cons retained.val.val (.nil view.tail.point view.tail.owner)))}

/-- Read each actual head once and retain both original stationary comparisons and the literal same-link prefix.

Only original direct constructor readers and signed stationary-link
operations execute. The supplied View/Owners/tail are unchanged; no query,
continuation, reserve reset, join or primitive observation is acquired.
-/
def pieces : view.Pieces :=
  let source := trace.path.headLink view.source view.1.property
  let moving := view.source.path.headLink view.moving view.2.1.property
  let retained := view.moving.path.headLink view.tail view.2.2.property
  let sourceSign := trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point
  let retainedSign := view.moving.path.stationaryHeadEquivalent view.tail view.2.2.property
    (view.tail_point.trans view.moving_point.symm)
  let front := OwnerPath.cons source.val (.cons moving.val
    (.cons retained.val (.nil view.tail.point view.tail.owner)))
  ⟨⟨source, rfl⟩, ⟨moving, rfl⟩, ⟨retained, rfl⟩, ⟨sourceSign, rfl⟩, ⟨retainedSign, rfl⟩, ⟨front, rfl⟩⟩

namespace Pieces

variable {view} (kept : view.Pieces)

/-- Read the SAME actual source-preparation link, including its original tails and realization certificate. -/
@[expose] def source : OwnerLink polynomial (segment.pointAt current.parameter) view.source.point
    inherited view.source.owner := kept.1.val.val

/-- Read the SAME actual moving link before the retained moving suffix. -/
@[expose] def moving : OwnerLink polynomial view.source.point view.moving.point
    view.source.owner view.moving.owner := kept.2.1.val.val

/-- Read the SAME actual reserve-retention link, without discarding its separate endpoint Owners. -/
@[expose] def retained : OwnerLink polynomial view.moving.point view.tail.point
    view.moving.owner view.tail.owner := kept.2.2.1.val.val

/-- Read the actual source stationary-sign comparison retained by its original factory. -/
@[expose] def sourceSign : NamedEquivalent (ownerName inherited) (ownerName view.source.owner) := kept.2.2.2.1.val

/-- Read the separate actual retention-sign comparison on the original two Owners. -/
@[expose] def retainedSign : NamedEquivalent (ownerName view.moving.owner) (ownerName view.tail.owner) :=
  kept.2.2.2.2.1.val

/-- Read the literal original three-link prefix. -/
@[expose] def front : OwnerPath polynomial (segment.pointAt current.parameter) inherited
    view.tail.point view.tail.owner := kept.2.2.2.2.2.val

/-- The complete first head result is its original direct same-path reader. -/
theorem source_eq : kept.1.val = trace.path.headLink view.source view.1.property := kept.1.property

/-- The complete moving head result is its original reader on the SAME source suffix. -/
theorem moving_eq : kept.2.1.val = view.source.path.headLink view.moving view.2.1.property := kept.2.1.property

/-- The complete retention head result is its original reader on the SAME moving suffix. -/
theorem retained_eq : kept.2.2.1.val = view.moving.path.headLink view.tail view.2.2.property := kept.2.2.1.property

/-- The retained source sign uses the actual stationary head, not a coordinate-derived Owner identity. -/
theorem sourceSign_eq : kept.sourceSign =
    trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point := kept.2.2.2.1.property

/-- The retained retention sign is the original actual-link comparison. -/
theorem retainedSign_eq : kept.retainedSign =
    view.moving.path.stationaryHeadEquivalent view.tail view.2.2.property
      (view.tail_point.trans view.moving_point.symm) := kept.2.2.2.2.1.property

/-- The original whole path starts with its SAME retained source link and source suffix. -/
theorem source_path : trace.path = .cons kept.source view.source.path := kept.1.val.property

/-- The original source suffix starts with the SAME retained moving link. -/
theorem moving_path : view.source.path = .cons kept.moving view.moving.path := kept.2.1.val.property

/-- The original moving suffix starts with the SAME retained retention link and actual tail. -/
theorem retained_path : view.moving.path = .cons kept.retained view.tail.path := kept.2.2.1.val.property

/-- The retained prefix is exactly the three original links in their original order. -/
theorem front_eq : kept.front = .cons kept.source (.cons kept.moving
    (.cons kept.retained (.nil view.tail.point view.tail.owner))) := kept.2.2.2.2.2.property

/-- The SAME prefix and original actual tail recover the complete original trace path. -/
theorem rejoin : trace.path = kept.front.append view.tail.path := by
  have moving := congrArg (OwnerPath.cons kept.source) kept.moving_path
  have retained := congrArg (fun after => OwnerPath.cons kept.source (OwnerPath.cons kept.moving after))
    kept.retained_path
  have rejoined := congrArg (fun front => front.append view.tail.path) kept.front_eq
  exact kept.source_path.trans (moving.trans (retained.trans rejoined.symm))

/-- Every retained prefix vertex is an actual original source/moving/retention occurrence. -/
theorem vertices : kept.front.vertices = [view.source.point, view.moving.point, view.tail.point] :=
  (congrArg OwnerPath.vertices kept.front_eq).trans rfl

/-- Split the SAME original trace immediately after its actual source-preparation link. -/
def sourceSplit : OwnerPath.Split trace.path :=
  ⟨view.source.point, view.source.owner, .cons kept.source (.nil view.source.point view.source.owner),
    ⟨view.source.path, kept.source_path.symm⟩⟩

/-- The source split retains the entire actual source suffix and its Owner, not merely its coordinate. -/
theorem sourceSplit_suffix : kept.sourceSplit.suffix = view.source := by
  unfold sourceSplit
  rfl

/-- Split the SAME trace after its actual moving link and before the distinct reserve-retention link. -/
def movingSplit : OwnerPath.Split trace.path :=
  ⟨view.moving.point, view.moving.owner,
    .cons kept.source (.cons kept.moving (.nil view.moving.point view.moving.owner)),
    ⟨view.moving.path,
      (kept.source_path.trans (congrArg (OwnerPath.cons kept.source) kept.moving_path)).symm⟩⟩

/-- The moving split preserves its whole actual moving Owner and unchanged original following path. -/
theorem movingSplit_suffix : kept.movingSplit.suffix = view.moving := by
  unfold movingSplit
  rfl

/-- Split the SAME trace after the original retention link, preserving the literal original tail. -/
def retainedSplit : OwnerPath.Split trace.path :=
  ⟨view.tail.point, view.tail.owner, kept.front, ⟨view.tail.path, kept.rejoin.symm⟩⟩

/-- The retention split preserves the complete original post-retention suffix tuple. -/
theorem retainedSplit_suffix : kept.retainedSplit.suffix = view.tail := by
  unfold retainedSplit
  rfl

end Pieces

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace.View

end
