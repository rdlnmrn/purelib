module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Acquisition
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Entry.Corner.Transport
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Data.Nat.Order
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Actual full-cubic comparison on a particular paid sharp route

The zero-, one- and two-edge cases follow the original stored ClearPath.
The existing Source attachment supplies only the initial Owner. Complete
factor folds consume the same retained paid edge acquisitions; the corner
passes its exact preceding terminal Reading and Samples unchanged. The
result compares this particular stored Covered.finishOwner with its actual
retained physical output channel, without a target-equivalence input.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

namespace Route.Acquisition.Comparison

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint ownerAtStart)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Segment.Reading.Payment

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {prepared : Division.Prepared source.lift.value}
variable (attachment : Spatial.Source source prepared)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

section Edge

variable {edgeStart edgeFinish : Canonical}
variable {edge : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) edgeStart edgeFinish}
variable {edgeWithin : edge.WithinAmbient} {edgeOwner : Owner ((Paths.polynomial parameter).eval edgeStart)}
variable (paid : CoveredTracedPath.Acquisition.Segment
  (segment := edge) (within := edgeWithin) (owner := edgeOwner) (widthRequest anchor edge))

/-- The same actual paid edge supplies its original trace-fit certificate without another request acquisition. -/
theorem traceFit : Fold.TraceFits paid.prepared.budget.trace paid.prepared.acquired.prepared.subdivision := by
  unfold Fold.TraceFits
  exact paid.prepared.fits

/-- The same actual retained edge supplies its internally computed factor-width payment. -/
theorem widthFit : Fold.Widths (anchor := anchor) paid.prepared.acquired.prepared.subdivision := by
  unfold Fold.Widths
  exact paid.prepared.widths

end Edge

section FirstEdge

variable {middle : Canonical}
variable {head : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  (Spatial.coordinate site parameter 2 quarter positive first) middle}
variable {headWithin : head.WithinAmbient}
variable (headFactors : Segment budgets head headWithin)
variable (headPaid : CoveredTracedPath.Acquisition.Segment (segment := head) (within := headWithin)
  (owner := attachment.attached.owner) (widthRequest anchor head))

/-- The original initial factor-fold result on the same first acquired edge and physical preparation. -/
@[expose] def First := Fold.Acquisition.Result (completed := headFactors) attachment headPaid.prepared.paid

namespace First

/-- Derive initial factor agreement from the existing attachment and fold its identical actual subdivision. -/
def build : First attachment headFactors headPaid :=
  Fold.Acquisition.Result.build (completed := headFactors) attachment headPaid.prepared.paid

variable {headFactors : Segment budgets head headWithin}
variable {headPaid : CoveredTracedPath.Acquisition.Segment (segment := head) (within := headWithin)
  (owner := attachment.attached.owner) (widthRequest anchor head)}
variable (retained : First attachment headFactors headPaid)

/-- Read the unchanged whole terminal Reading, Samples and derived first subdivision comparison. -/
@[expose] def terminal := Fold.Cache.terminal (completed := headFactors) headPaid.prepared.budget.trace
  (Fold.Acquisition.Result.fold (completed := headFactors) (attachment := attachment)
    (paid := headPaid.prepared.paid) retained)

/-- Read the original complete physical root channel at the first acquired edge's actual terminal query. -/
@[expose] def channel : CoherentNamed := (terminal attachment retained).1.values.value

/-- The actual stored first trace finish Owner agrees with that unchanged original terminal root channel. -/
def equivalent : NamedEquivalent (ownerRootName headPaid.traced.finishOwner.parameterNonzero
    headPaid.traced.finishOwner) (channel attachment retained).name :=
  NamedEquivalent.transport headPaid.finishName_eq.symm rfl (terminal attachment retained).2.2

end First

section SecondEdge

variable {finish : Canonical}
variable {second : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) middle finish}
variable {secondWithin : second.WithinAmbient}
variable (secondFactors : Segment budgets second secondWithin)
variable (secondPaid : CoveredTracedPath.Acquisition.Segment (segment := second) (within := secondWithin)
  (owner := headPaid.traced.finishOwner) (widthRequest anchor second))
variable (initial : First attachment headFactors headPaid)

/-- The original cached first trace's finish equation is the exact source handoff for the second acquisition. -/
theorem handoff_eq : headPaid.traced.finishOwner = headPaid.prepared.acquired.prepared.finishOwner :=
  headPaid.traced_finishOwner_eq.trans headPaid.prepared.acquired.finishOwner_eq

/-- The complete second-edge entry-cache type retains the actual preceding terminal observations unchanged. -/
@[expose] def Following (terminal : Fold.Terminal (completed := headFactors)
    headPaid.prepared.acquired.prepared.subdivision) :=
  Fold.Entry.Cache (completed := secondFactors) terminal.1 terminal.2.1 secondPaid.prepared.budget.trace
    secondPaid.prepared.acquired.prepared.subdivision
    (Fold.Entry.Corner.point_eq (segment := second) headPaid.prepared.acquired.prepared)
    (Fold.Entry.Corner.sourceAgreementOfOwnerEq (segment := second)
      headPaid.prepared.acquired.prepared headPaid.traced.finishOwner (handoff_eq attachment headPaid) terminal)
    (traceFit secondPaid) (widthFit secondPaid)

/-- The completed second entry is the original cross-segment factory on the same stored first terminal cache. -/
@[irreducible, expose] def FollowingCache
    (terminal : Fold.Terminal (completed := headFactors) headPaid.prepared.acquired.prepared.subdivision)
    (following : Following attachment headFactors headPaid secondFactors secondPaid terminal) : Prop :=
  following = Fold.Entry.Corner.fromTerminalOfOwnerEq (completed := secondFactors)
    headPaid.prepared.acquired.prepared headPaid.traced.finishOwner (handoff_eq attachment headPaid)
    secondPaid.prepared.acquired.prepared secondPaid.prepared.budget.trace
    (traceFit secondPaid) (widthFit secondPaid) terminal

/-- The second entry keeps the exact first terminal getter and its whole original new-segment comparison result. -/
@[expose] def Second :=
  Σ terminal : { retained : Fold.Terminal (completed := headFactors) headPaid.prepared.acquired.prepared.subdivision //
      retained = First.terminal attachment initial },
    { following : Following attachment headFactors headPaid secondFactors secondPaid terminal.val //
      FollowingCache attachment headFactors headPaid secondFactors secondPaid terminal.val following }

namespace Second

/-- Read the preceding terminal once and pass its identical Reading/Samples to the actual second acquisition. -/
def build : Second attachment headFactors headPaid secondFactors secondPaid initial :=
  let terminal := First.terminal attachment initial
  let following := Fold.Entry.Corner.fromTerminalOfOwnerEq (completed := secondFactors)
    headPaid.prepared.acquired.prepared headPaid.traced.finishOwner (handoff_eq attachment headPaid)
    secondPaid.prepared.acquired.prepared secondPaid.prepared.budget.trace
    (traceFit secondPaid) (widthFit secondPaid) terminal
  ⟨⟨terminal, rfl⟩, ⟨following, by unfold FollowingCache; rfl⟩⟩

variable {headFactors : Segment budgets head headWithin}
variable {headPaid : CoveredTracedPath.Acquisition.Segment (segment := head) (within := headWithin)
  (owner := attachment.attached.owner) (widthRequest anchor head)}
variable {secondFactors : Segment budgets second secondWithin}
variable {secondPaid : CoveredTracedPath.Acquisition.Segment (segment := second) (within := secondWithin)
  (owner := headPaid.traced.finishOwner) (widthRequest anchor second)}
variable {initial : First attachment headFactors headPaid}
variable (retained : Second attachment headFactors headPaid secondFactors secondPaid initial)

/-- Read the exact complete first terminal cache stored before constructing the second entry. -/
@[expose] def terminal := retained.1.val

/-- Read the actual second entry's retained origin-sensitive output without another query or sample. -/
@[expose] def output := Fold.Entry.Cache.output (completed := secondFactors)
  (terminal attachment retained).1 (terminal attachment retained).2.1 secondPaid.prepared.budget.trace
  (subdivision := secondPaid.prepared.acquired.prepared.subdivision)
  (point_eq := Fold.Entry.Corner.point_eq (segment := second) headPaid.prepared.acquired.prepared)
  (agreement := Fold.Entry.Corner.sourceAgreementOfOwnerEq (segment := second)
    headPaid.prepared.acquired.prepared headPaid.traced.finishOwner (handoff_eq attachment headPaid)
      (terminal attachment retained))
  (fits := traceFit secondPaid) (widths := widthFit secondPaid) retained.2.val

/-- Read the unchanged original physical output channel, preserving the preceding origin on immediate stop. -/
@[expose] def channel : CoherentNamed := (output attachment retained).channel

/-- The actual cached second trace finish Owner agrees with the retained origin-sensitive physical channel. -/
def equivalent : NamedEquivalent (ownerRootName secondPaid.traced.finishOwner.parameterNonzero
    secondPaid.traced.finishOwner) (channel attachment retained).name :=
  NamedEquivalent.transport secondPaid.finishName_eq.symm rfl (output attachment retained).equivalent

end Second
end SecondEdge
end FirstEdge

/-- Actual zero-, one- and two-edge comparison caches on the original finite path shape. -/
@[expose] def Cache : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive first) finish) →
    (within : path.WithinAmbient) → (_factors : Path budgets path within) →
    (_paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within attachment.attached.owner) → Type 1
 := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid
      exact PUnit
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within factors paid
          exact First attachment factors.1.val paid.1
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within factors paid
              exact Σ initial : First attachment factors.1.val paid.1,
                Second attachment factors.1.val paid.1 factors.2.1.val paid.2.1 initial
          | cons _third _tail =>
              intro _within _factors _paid
              exact PEmpty

namespace Cache

/-- Derive comparisons on each actual sharp-route edge, with no final equivalence supplied by the consumer. -/
def build : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive first) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within attachment.attached.owner) → path.segmentCount ≤ 2 → Cache attachment path within factors paid
 := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _short
      exact PUnit.unit
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within factors paid _short
          exact First.build attachment factors.1.val paid.1
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within factors paid _short
              let initial := First.build attachment factors.1.val paid.1
              let following := Second.build attachment factors.1.val paid.1 factors.2.1.val paid.2.1 initial
              exact ⟨initial, following⟩
          | cons _third tail =>
              intro _within _factors _paid short
              have lower : 3 ≤ ((tail.segmentCount + 1) + 1) + 1 :=
                Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le tail.segmentCount)))
              exact False.elim ((by decide +kernel : ¬ (3 : Nat) ≤ 2) (lower.trans short))

/-- Read the actual original full-cubic channel retained by the corresponding path-shape comparison. -/
@[expose] def channel : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive first) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within attachment.attached.owner) → Cache attachment path within factors paid → CoherentNamed
 := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _cache
      exact source.lift.value
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors _paid cache
          exact First.channel attachment cache
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid cache
              exact Second.channel attachment cache.2
          | cons _third _tail =>
              intro _within _factors _paid cache
              exact nomatch cache

/-- Compare the original assembled paid finishing Owner with the same retained physical output channel. -/
def equivalent : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive first) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within attachment.attached.owner) → (cache : Cache attachment path within factors paid) →
    NamedEquivalent
      (ownerRootName
        (CoveredTracedPath.Acquisition.Spine.assemble (fun {_start _finish} segment => widthRequest anchor segment)
          path within attachment.attached.owner paid).traced.finishOwner.parameterNonzero
        (CoveredTracedPath.Acquisition.Spine.assemble (fun {_start _finish} segment => widthRequest anchor segment)
          path within attachment.attached.owner paid).traced.finishOwner)
      (channel attachment path within factors paid cache).name
 := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _cache
      have initial : NamedEquivalent
          (ownerRootName attachment.attached.owner.parameterNonzero attachment.attached.owner)
          source.lift.value.name := by
        unfold ownerRootName
        exact attachment.agrees.symm
      exact initial
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors _paid cache
          exact First.equivalent attachment cache
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid cache
              exact Second.equivalent attachment cache.2
          | cons _third _tail =>
              intro _within _factors _paid cache
              exact nomatch cache

end Cache

variable {last : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside last}
variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {geometry : Parallel.Geometry source targetReading anchor.regular payment}
variable {factors : Route budgets geometry}
variable (retained : Route.Acquisition factors attachment.attached.owner)

/-- The comparison retains its whole original path-shape construction on the same stored factors and paid spine. -/
@[expose] def Result :=
  { cache : Cache attachment geometry.route.path geometry.route.within retained.factors.path retained.spine //
    cache = Cache.build attachment geometry.route.path geometry.route.within retained.factors.path retained.spine
      geometry.route.short }

namespace Result

/-- Derive the full actual sharp-route comparison once, retaining the entire original comparison cache. -/
def build : Result attachment retained :=
  let cache := Cache.build attachment geometry.route.path geometry.route.within retained.factors.path retained.spine
    geometry.route.short
  ⟨cache, rfl⟩

variable {attachment : Spatial.Source source prepared}
variable {retained : Route.Acquisition factors attachment.attached.owner}
variable (result : Result attachment retained)

/-- Read the actual unchanged physical product channel retained at the end of this particular paid route. -/
@[expose] def channel : CoherentNamed :=
  Cache.channel attachment geometry.route.path geometry.route.within retained.factors.path retained.spine result.val

/-- This particular stored Covered.finishOwner agrees with its unchanged original retained physical output channel.

The whole stored covered-path factory equation transports only the same
assembled finishing Owner. The comparison itself was derived on its actual
paid edge spine, using the original attachment and unchanged corner Samples.
No independent target-root agreement or closed-cycle identity is assumed.
-/
def equivalent : NamedEquivalent (ownerRootName retained.finishOwner.parameterNonzero retained.finishOwner)
    result.channel.name := by
  have names := congrArg
    (fun covered : CoveredTracedPath geometry.route.path attachment.attached.owner =>
      ownerRootName covered.traced.finishOwner.parameterNonzero covered.traced.finishOwner) retained.covered_eq
  exact NamedEquivalent.transport names.symm rfl
    (Cache.equivalent attachment geometry.route.path geometry.route.within
      retained.factors.path retained.spine result.val)

end Result

end Route.Acquisition.Comparison

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
