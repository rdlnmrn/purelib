module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison
import Purelib.Data.Nat.Order
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Division.Prepared.Basic

/-! # Supplied-owner comparison on an actual paid sharp route

An initial compatibility view retains an original source Owner and its
complete source-Lift comparison. The actual zero-, one- and two-edge cases
consume the original paid Covered spine and physical factor preparations.
First entry uses the shared supplied-owner construction; subsequent edges
reuse the unchanged original corner caches. No Source attachment is acquired.
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
variable {budgets : Budgets anchor}

/-- An original full-cubic source Owner and its retained operational comparison with the exact source Lift.

The sigma retains the whole nominal Owner and Type-valued comparison.
It does not attach a new root or replace either original compared channel.
-/
@[expose] def Initial (source : Transport.Reading actual first firstInside) :=
  Σ owner : Owner ((Paths.polynomial parameter).eval
      (Spatial.coordinate site parameter 2 quarter positive first)),
    NamedEquivalent source.lift.value.name (ownerRootName owner.parameterNonzero owner)

namespace Initial

/-- Retain a supplied original Owner and already derived source-Lift comparison without preparing either channel. -/
@[expose] def ofOwner (owner : Owner ((Paths.polynomial parameter).eval
    (Spatial.coordinate site parameter 2 quarter positive first)))
    (equivalent : NamedEquivalent source.lift.value.name (ownerRootName owner.parameterNonzero owner)) :
    Initial source := ⟨owner, equivalent⟩

/-- Read the identical original nominal Owner retained by this initial compatibility view. -/
@[expose] def owner (entry : Initial source) := entry.1

/-- Read the identical Type-valued source-Lift comparison, including its actual operational schedules. -/
@[expose] def equivalent (entry : Initial source) := entry.2

variable (entry : Initial source)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

section FirstEdge

variable {middle : Canonical}
variable {head : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  (Spatial.coordinate site parameter 2 quarter positive first) middle}
variable {headWithin : head.WithinAmbient}
variable (headFactors : Segment budgets head headWithin)
variable (headPaid : CoveredTracedPath.Acquisition.Segment (segment := head) (within := headWithin)
  (owner := entry.owner) (widthRequest anchor head))

/-- The supplied-owner initial factor-fold result on the same first acquired edge and physical preparation. -/
@[expose] def First := Fold.Acquisition.Initial.Result (completed := headFactors)
  entry.owner (Fold.Acquisition.Initial.ownerAgreement entry.owner entry.equivalent) headPaid.prepared.paid

namespace First

/-- Derive factor-source agreement from the retained initial view and fold its identical actual subdivision. -/
def build : First entry headFactors headPaid :=
  Fold.Acquisition.Initial.Result.ofOwner (completed := headFactors)
    entry.owner headPaid.prepared.paid entry.equivalent

variable {headFactors : Segment budgets head headWithin}
variable {headPaid : CoveredTracedPath.Acquisition.Segment (segment := head) (within := headWithin)
  (owner := entry.owner) (widthRequest anchor head)}
variable (retained : First entry headFactors headPaid)

/-- Read the unchanged whole terminal Reading, Samples and derived first subdivision comparison. -/
@[expose] def terminal := Fold.Cache.terminal (completed := headFactors) headPaid.prepared.budget.trace
  (Fold.Acquisition.Initial.Result.fold (completed := headFactors) (suppliedOwner := entry.owner)
    (suppliedAgreement := Fold.Acquisition.Initial.ownerAgreement entry.owner entry.equivalent)
    (suppliedPaid := headPaid.prepared.paid) retained)

/-- Read the original complete physical root channel at the first acquired edge's actual terminal query. -/
@[expose] def channel : CoherentNamed := (terminal entry retained).1.values.value

/-- The actual stored first trace finish Owner agrees with that unchanged original terminal root channel. -/
def equivalent : NamedEquivalent (ownerRootName headPaid.traced.finishOwner.parameterNonzero
    headPaid.traced.finishOwner) (channel entry retained).name :=
  NamedEquivalent.transport headPaid.finishName_eq.symm rfl (terminal entry retained).2.2

end First

section SecondEdge

variable {finish : Canonical}
variable {second : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) middle finish}
variable {secondWithin : second.WithinAmbient}
variable (secondFactors : Segment budgets second secondWithin)
variable (secondPaid : CoveredTracedPath.Acquisition.Segment (segment := second) (within := secondWithin)
  (owner := headPaid.traced.finishOwner) (widthRequest anchor second))
variable (firstResult : First entry headFactors headPaid)

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
      headPaid.prepared.acquired.prepared headPaid.traced.finishOwner (handoff_eq entry headPaid) terminal)
    (traceFit secondPaid) (widthFit secondPaid)

/-- The completed second entry is the original cross-segment factory on the same stored first terminal cache. -/
@[irreducible, expose] def FollowingCache
    (terminal : Fold.Terminal (completed := headFactors) headPaid.prepared.acquired.prepared.subdivision)
    (following : Following entry headFactors headPaid secondFactors secondPaid terminal) : Prop :=
  following = Fold.Entry.Corner.fromTerminalOfOwnerEq (completed := secondFactors)
    headPaid.prepared.acquired.prepared headPaid.traced.finishOwner (handoff_eq entry headPaid)
    secondPaid.prepared.acquired.prepared secondPaid.prepared.budget.trace
    (traceFit secondPaid) (widthFit secondPaid) terminal

/-- The second entry keeps the exact first terminal getter and its whole original new-segment comparison result. -/
@[expose] def Second :=
  Σ terminal : { retained : Fold.Terminal (completed := headFactors) headPaid.prepared.acquired.prepared.subdivision //
      retained = First.terminal entry firstResult },
    { following : Following entry headFactors headPaid secondFactors secondPaid terminal.val //
      FollowingCache entry headFactors headPaid secondFactors secondPaid terminal.val following }

namespace Second

/-- Read the preceding terminal once and pass its identical Reading/Samples to the actual second acquisition. -/
def build : Second entry headFactors headPaid secondFactors secondPaid firstResult :=
  let terminal := First.terminal entry firstResult
  let following := Fold.Entry.Corner.fromTerminalOfOwnerEq (completed := secondFactors)
    headPaid.prepared.acquired.prepared headPaid.traced.finishOwner (handoff_eq entry headPaid)
    secondPaid.prepared.acquired.prepared secondPaid.prepared.budget.trace
    (traceFit secondPaid) (widthFit secondPaid) terminal
  ⟨⟨terminal, rfl⟩, ⟨following, by unfold FollowingCache; rfl⟩⟩

variable {headFactors : Segment budgets head headWithin}
variable {headPaid : CoveredTracedPath.Acquisition.Segment (segment := head) (within := headWithin)
  (owner := entry.owner) (widthRequest anchor head)}
variable {secondFactors : Segment budgets second secondWithin}
variable {secondPaid : CoveredTracedPath.Acquisition.Segment (segment := second) (within := secondWithin)
  (owner := headPaid.traced.finishOwner) (widthRequest anchor second)}
variable {firstResult : First entry headFactors headPaid}
variable (retained : Second entry headFactors headPaid secondFactors secondPaid firstResult)

/-- Read the exact complete first terminal cache stored before constructing the second entry. -/
@[expose] def terminal := retained.1.val

/-- Read the actual second entry's retained origin-sensitive output without another query or sample. -/
@[expose] def output := Fold.Entry.Cache.output (completed := secondFactors)
  (terminal entry retained).1 (terminal entry retained).2.1 secondPaid.prepared.budget.trace
  (subdivision := secondPaid.prepared.acquired.prepared.subdivision)
  (point_eq := Fold.Entry.Corner.point_eq (segment := second) headPaid.prepared.acquired.prepared)
  (agreement := Fold.Entry.Corner.sourceAgreementOfOwnerEq (segment := second)
    headPaid.prepared.acquired.prepared headPaid.traced.finishOwner (handoff_eq entry headPaid)
      (terminal entry retained))
  (fits := traceFit secondPaid) (widths := widthFit secondPaid) retained.2.val

/-- Read the unchanged original physical output channel, preserving the preceding origin on immediate stop. -/
@[expose] def channel : CoherentNamed := (output entry retained).channel

/-- The actual cached second trace finish Owner agrees with the retained origin-sensitive physical channel. -/
def equivalent : NamedEquivalent (ownerRootName secondPaid.traced.finishOwner.parameterNonzero
    secondPaid.traced.finishOwner) (channel entry retained).name :=
  NamedEquivalent.transport secondPaid.finishName_eq.symm rfl (output entry retained).equivalent

end Second
end SecondEdge
end FirstEdge

/-- Actual zero-, one- and two-edge comparison caches on the original finite path shape. -/
@[expose] def Cache : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive first) finish) →
    (within : path.WithinAmbient) → (_factors : Path budgets path within) →
    (_paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner) → Type 1
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
          exact First entry factors.1.val paid.1
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within factors paid
              exact Σ firstResult : First entry factors.1.val paid.1,
                Second entry factors.1.val paid.1 factors.2.1.val paid.2.1 firstResult
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
      path within entry.owner) → path.segmentCount ≤ 2 → Cache entry path within factors paid
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
          exact First.build entry factors.1.val paid.1
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within factors paid _short
              let firstResult := First.build entry factors.1.val paid.1
              let following := Second.build entry factors.1.val paid.1 factors.2.1.val paid.2.1 firstResult
              exact ⟨firstResult, following⟩
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
      path within entry.owner) → Cache entry path within factors paid → CoherentNamed
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
          exact First.channel entry cache
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid cache
              exact Second.channel entry cache.2
          | cons _third _tail =>
              intro _within _factors _paid cache
              exact nomatch cache

/-- Compare the original assembled paid finishing Owner with the same retained physical output channel. -/
def equivalent : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive first) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner) → (cache : Cache entry path within factors paid) →
    NamedEquivalent
      (ownerRootName
        (CoveredTracedPath.Acquisition.Spine.assemble (fun {_start _finish} segment => widthRequest anchor segment)
          path within entry.owner paid).traced.finishOwner.parameterNonzero
        (CoveredTracedPath.Acquisition.Spine.assemble (fun {_start _finish} segment => widthRequest anchor segment)
          path within entry.owner paid).traced.finishOwner)
      (channel entry path within factors paid cache).name
 := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _cache
      exact entry.equivalent.symm
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors _paid cache
          exact First.equivalent entry cache
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid cache
              exact Second.equivalent entry cache.2
          | cons _third _tail =>
              intro _within _factors _paid cache
              exact nomatch cache

end Cache

variable {last : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside last}
variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {geometry : Parallel.Geometry source targetReading anchor.regular payment}
variable {factors : Route budgets geometry}
variable (retained : Route.Acquisition factors entry.owner)

/-- The comparison retains its whole original path-shape construction on the same stored factors and paid spine. -/
@[expose] def Result :=
  { cache : Cache entry geometry.route.path geometry.route.within retained.factors.path retained.spine //
    cache = Cache.build entry geometry.route.path geometry.route.within retained.factors.path retained.spine
      geometry.route.short }

namespace Result

/-- Derive the full actual sharp-route comparison once, retaining the entire original comparison cache. -/
def build : Result entry retained :=
  let cache := Cache.build entry geometry.route.path geometry.route.within retained.factors.path retained.spine
    geometry.route.short
  ⟨cache, rfl⟩

variable {entry : Initial source}
variable {retained : Route.Acquisition factors entry.owner}
variable (result : Result entry retained)

/-- Read the actual unchanged physical product channel retained at the end of this particular paid route. -/
@[expose] def channel : CoherentNamed :=
  Cache.channel entry geometry.route.path geometry.route.within retained.factors.path retained.spine result.val

/-- This particular stored Covered.finishOwner agrees with its unchanged original retained physical output channel.

The whole stored covered-path factory equation transports only the same
assembled finishing Owner. The comparison itself was derived on its actual
paid edge spine, using the retained initial view and unchanged corner Samples.
No independent target-root agreement or closed-cycle identity is assumed.
-/
def equivalent : NamedEquivalent (ownerRootName retained.finishOwner.parameterNonzero retained.finishOwner)
    result.channel.name := by
  have names := congrArg
    (fun covered : CoveredTracedPath geometry.route.path entry.owner =>
      ownerRootName covered.traced.finishOwner.parameterNonzero covered.traced.finishOwner) retained.covered_eq
  exact NamedEquivalent.transport names.symm rfl
    (Cache.equivalent entry geometry.route.path geometry.route.within
      retained.factors.path retained.spine result.val)

end Result

end Initial

end Route.Acquisition.Comparison

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
