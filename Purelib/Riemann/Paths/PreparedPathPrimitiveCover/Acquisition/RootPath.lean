module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Observation
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Suffix
public import Purelib.Riemann.Paths.OwnerTracePath.Split.Append
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Data.Gaussian.Norm.Basic

/-! # Root comparison of the same retained complete-segment trace

The input is the actual materialized trace from the original acquisition,
with its whole stored TraceCache equation. Reversing only the original
finish-Owner reindex and endpoint casts gives the identical internal trace.
The original subdivision comparison cache then derives finish agreement
with one independent fixed-box reference, including reconditioned owners.
No acquisition, continuation or primitive observation is executed again.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart zeroEndpoint)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_initial_box)

attribute [local irreducible] CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

section Materialized

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {sourceOwner : Owner (polynomial.eval start)} {request : AccuracyRequest}
    (retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request)
    (actual : OwnerPath polynomial start sourceOwner finish retained.traced.finishOwner)
    (actual_eq : actual = retained.traced.trace.get)

/-- Undo only the original stored finishing-Owner reindex on the actual materialized path. -/
def preparedTrace : OwnerPath polynomial start sourceOwner finish retained.traced.prepared.finishOwner :=
  actual.reindexOwners rfl retained.traced.finishOwner_eq

include actual_eq in
/-- The reindexed actual path has the entire original CompleteSegment ownerPath factory identity. -/
theorem preparedTrace_eq : retained.preparedTrace actual =
    PreparedPathTrace.CompleteSegment.ownerPath retained.traced.prepared retained.traced.budget
      retained.traced.fits := by
  have factory := actual_eq.trans retained.trace_eq
  have castFactory := congrArg (fun path : OwnerPath polynomial start sourceOwner finish retained.traced.finishOwner =>
    path.reindexOwners rfl retained.traced.finishOwner_eq) factory
  exact castFactory.trans (OwnerPath.reindexOwners_inverse rfl retained.traced.finishOwner_eq.symm _)

/-- The actual internal trace preserves all original physical links and Owners through exact endpoint casts. -/
def internalTrace : OwnerPath polynomial (segment.pointAt zeroEndpoint.parameter) (ownerAtStart segment sourceOwner)
    (segment.pointAt retained.traced.prepared.subdivision.endpoint.parameter)
    retained.traced.prepared.subdivision.terminalOwner :=
  (retained.preparedTrace actual).castEndpoints
    retained.traced.prepared.start_eq.symm retained.traced.prepared.finish_eq.symm
    (by
      unfold ownerAtStart
      exact (RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ _).symm)
    retained.traced.prepared.finishOwner_heq_terminalOwner

include actual_eq in
/-- The complete internal trace is the original factory on the SAME retained subdivision, budget and fits. -/
theorem internalTrace_eq : retained.internalTrace actual =
    ownerPath retained.traced.budget retained.traced.prepared.subdivision retained.traced.fits := by
  unfold internalTrace
  rewrite [retained.preparedTrace_eq actual actual_eq]
  unfold PreparedPathTrace.CompleteSegment.ownerPath
  exact OwnerPath.castEndpoints_inverse _ _ _ _ _

/-- The internal index transport retains the whole actual materialized physical path heterogeneously. -/
theorem internalTrace_heq : HEq (retained.internalTrace actual) actual := by
  unfold internalTrace
  have first := OwnerPath.castEndpoints_heq
    (nextStart := segment.pointAt zeroEndpoint.parameter)
    (nextFinish := segment.pointAt retained.traced.prepared.subdivision.endpoint.parameter)
    (nextFirst := ownerAtStart segment sourceOwner)
    (nextLast := retained.traced.prepared.subdivision.terminalOwner)
    retained.traced.prepared.start_eq.symm retained.traced.prepared.finish_eq.symm
    (by
      unfold ownerAtStart
      exact (RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ _).symm)
    retained.traced.prepared.finishOwner_heq_terminalOwner (retained.preparedTrace actual)
  have second : HEq (retained.preparedTrace actual) actual := by
    unfold preparedTrace OwnerPath.reindexOwners
    exact OwnerPath.castEndpoints_heq _ _ _ _ actual
  exact first.trans second

/-- Retain the same internal path and its original complete subdivision-factory equation. -/
@[expose] def rootTrace : Trace retained.traced.budget retained.traced.prepared.subdivision retained.traced.fits :=
  Trace.ofCompleted (retained.internalTrace actual) (retained.internalTrace_eq actual actual_eq)

/-- The SAME internal endpoint-index transport preserves every actual original physical trace vertex.

Only the original finishing-Owner reindex and complete endpoint/Owner
casts are eliminated. No path factory or root continuation is executed.
-/
theorem rootTrace_vertices : (retained.rootTrace actual actual_eq).path.vertices = actual.vertices := by
  have startOwnerEq : HEq sourceOwner (ownerAtStart segment sourceOwner) := by
    unfold ownerAtStart
    exact (RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ _).symm
  have internal := OwnerPath.castEndpoints_vertices
    retained.traced.prepared.start_eq.symm retained.traced.prepared.finish_eq.symm startOwnerEq
    retained.traced.prepared.finishOwner_heq_terminalOwner (retained.preparedTrace actual)
  have prepared := OwnerPath.reindexOwners_vertices rfl retained.traced.finishOwner_eq actual
  change (retained.internalTrace actual).vertices = actual.vertices
  change ((retained.preparedTrace actual).castEndpoints
    retained.traced.prepared.start_eq.symm retained.traced.prepared.finish_eq.symm startOwnerEq
    retained.traced.prepared.finishOwner_heq_terminalOwner).vertices = actual.vertices
  exact internal.trans prepared

/-- Restore a GIVEN actual internal-trace split to the SAME original materialized path.

Only the exact original endpoint/whole-Owner casts are reversed. The
selected middle Owner and all split links remain the original retained
data; no path, trace, root comparison or continuation is reconstructed.
-/
def restoreSplit (divided : OwnerPath.Split (retained.rootTrace actual actual_eq).path) :
    OwnerPath.Split actual := by
  have startOwnerEq : HEq sourceOwner (ownerAtStart segment sourceOwner) := by
    unfold ownerAtStart
    exact (RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ _).symm
  let first := OwnerPath.Split.castEndpoints retained.traced.prepared.start_eq retained.traced.prepared.finish_eq
    startOwnerEq.symm retained.traced.prepared.finishOwner_heq_terminalOwner.symm divided
  have firstPath : ((retained.rootTrace actual actual_eq).path.castEndpoints
      retained.traced.prepared.start_eq retained.traced.prepared.finish_eq startOwnerEq.symm
      retained.traced.prepared.finishOwner_heq_terminalOwner.symm) = retained.preparedTrace actual := by
    change ((retained.preparedTrace actual).castEndpoints
      retained.traced.prepared.start_eq.symm retained.traced.prepared.finish_eq.symm startOwnerEq
      retained.traced.prepared.finishOwner_heq_terminalOwner).castEndpoints
        retained.traced.prepared.start_eq retained.traced.prepared.finish_eq startOwnerEq.symm
        retained.traced.prepared.finishOwner_heq_terminalOwner.symm = retained.preparedTrace actual
    exact OwnerPath.castEndpoints_inverse _ _ _ _ (retained.preparedTrace actual)
  let prepared := OwnerPath.Split.castPath firstPath first
  let last := OwnerPath.Split.castEndpoints rfl rfl (HEq.refl sourceOwner)
    (heq_of_eq retained.traced.finishOwner_eq.symm) prepared
  have lastPath : (retained.preparedTrace actual).castEndpoints rfl rfl (HEq.refl sourceOwner)
      (heq_of_eq retained.traced.finishOwner_eq.symm) = actual := by
    change (actual.reindexOwners rfl retained.traced.finishOwner_eq).reindexOwners
      rfl retained.traced.finishOwner_eq.symm = actual
    exact OwnerPath.reindexOwners_inverse rfl retained.traced.finishOwner_eq actual
  exact OwnerPath.Split.castPath lastPath last

/-- Restoring an internal split preserves its exact selected original point and whole Owner. -/
theorem restoreSplit_vertex (divided : OwnerPath.Split (retained.rootTrace actual actual_eq).path) :
    (retained.restoreSplit actual actual_eq divided).vertex = divided.vertex := by
  unfold restoreSplit
  exact (OwnerPath.Split.castPath_vertex _ _).trans
    ((OwnerPath.Split.castEndpoints_vertex _ _ _ _ _).trans
      ((OwnerPath.Split.castPath_vertex _ _).trans (OwnerPath.Split.castEndpoints_vertex _ _ _ _ _)))

end Materialized

section Comparisons

variable {genus : Nat} (curve : HyperellipticCurve genus) (differential : Differential genus)
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
    (retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request)
    (actual : OwnerPath curve.polynomial start sourceOwner finish retained.traced.finishOwner)
    (actual_eq : actual = retained.traced.trace.get) (sheet : Fin 2)
    {referenceSource : Canonical} {referenceOwner : Owner referenceSource}
    (second : FixedRootBoxBudget.Budget referenceOwner)
    (movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (referenceSource - curve.polynomial.eval (segment.pointAt time)) ≤ second.movement)

/-- The actual subdivision comparison cache uses the same materialized trace and every original accepted request. -/
@[expose] def RootComparisons :=
  Comparison.Cache curve differential retained.traced.budget sheet second movement
    retained.traced.prepared.subdivision retained.traced.fits (retained.rootTrace actual actual_eq)

namespace RootComparisons

variable {curve differential retained actual actual_eq sheet second movement}

/-- Cache one original-edge root comparison and one shared endpoint reference per actual accepted request. -/
def build : RootComparisons curve differential retained actual actual_eq sheet second movement :=
  Comparison.Cache.build retained.traced.prepared.subdivision retained.traced.fits
    (retained.rootTrace actual actual_eq)

variable (comparisons : RootComparisons curve differential retained actual actual_eq sheet second movement)
    (firstReference : Owner (curve.polynomial.eval start))

/-- Read the same cached final reference at the original physical finish coordinate. -/
def finishReference : Owner (curve.polynomial.eval finish) :=
  castOwnerParameter (congrArg curve.polynomial.eval retained.traced.prepared.finish_eq)
    (Comparison.Cache.finishReference comparisons (ownerAtStart segment firstReference))

/-- An exact original-box starting reference leaves the SAME box at the displayed cached finish. -/
theorem finishReference_box
    (first_box : firstReference.track.initial.box = referenceOwner.track.initial.box) :
    (finishReference comparisons firstReference).track.initial.box = referenceOwner.track.initial.box := by
  unfold finishReference
  rewrite [castOwnerParameter_initial_box]
  exact Comparison.Cache.finishReference_box comparisons (ownerAtStart segment firstReference) (by
    unfold ownerAtStart
    rewrite [castOwnerParameter_initial_box]
    exact first_box)

/-- The actual acquisition's finishing Owner agrees with the retained independent finishing reference.

The original start comparison is transported through the source index cast,
then the cached local fold pays every actual moving and retention link.
Only exact original endpoint and stored finish-Owner identities transport
its result back to the displayed physical finish. No independently queried
finish or presumed returning relation is used.
-/
def finishEquivalent
    (refines : firstReference.track.initial.box.Refines referenceOwner.track.initial.box)
    (initial : NamedEquivalent (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName firstReference.parameterNonzero firstReference)) :
    NamedEquivalent (ownerRootName retained.traced.finishOwner.parameterNonzero retained.traced.finishOwner)
      (ownerRootName (finishReference comparisons firstReference).parameterNonzero
        (finishReference comparisons firstReference)) := by
  have sourceName := SquareRootTrackEquivalence.ownerRootName_castOwnerParameter
    (congrArg curve.polynomial.eval retained.traced.prepared.start_eq.symm) sourceOwner
  have firstName := SquareRootTrackEquivalence.ownerRootName_castOwnerParameter
    (congrArg curve.polynomial.eval retained.traced.prepared.start_eq.symm) firstReference
  have starting : NamedEquivalent
      (ownerRootName (ownerAtStart segment sourceOwner).parameterNonzero (ownerAtStart segment sourceOwner))
      (ownerRootName (ownerAtStart segment firstReference).parameterNonzero
        (ownerAtStart segment firstReference)) :=
    NamedEquivalent.transport sourceName.symm firstName.symm initial
  have bounded : (ownerAtStart segment firstReference).track.initial.box.Refines
      referenceOwner.track.initial.box := by
    unfold ownerAtStart
    rewrite [castOwnerParameter_initial_box]
    exact refines
  have compared := Comparison.Cache.equivalent comparisons (ownerAtStart segment firstReference) bounded starting
  have finishName : ownerRootName retained.traced.finishOwner.parameterNonzero retained.traced.finishOwner =
      ownerRootName retained.traced.prepared.subdivision.terminalOwner.parameterNonzero
        retained.traced.prepared.subdivision.terminalOwner := by
    have retainedName := congrArg (fun owner : Owner (curve.polynomial.eval finish) =>
      ownerRootName owner.parameterNonzero owner) retained.traced.finishOwner_eq
    have preparedName := SquareRootTrackEquivalence.ownerRootName_castOwnerParameter
      (congrArg curve.polynomial.eval retained.traced.prepared.finish_eq)
      retained.traced.prepared.subdivision.terminalOwner
    exact retainedName.trans preparedName
  have referenceName := SquareRootTrackEquivalence.ownerRootName_castOwnerParameter
    (congrArg curve.polynomial.eval retained.traced.prepared.finish_eq)
    (Comparison.Cache.finishReference comparisons (ownerAtStart segment firstReference))
  exact NamedEquivalent.transport finishName.symm referenceName.symm compared

end RootComparisons

end Comparisons

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment

end
