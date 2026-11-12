module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition
public import Purelib.Riemann.Paths.PreparedPathTrace
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Same-cache internal observations of an actual physical traced segment

The retained original TraceCache identifies the literal stored thunk result
with the original CompleteSegment path and its exact finish-Owner reindex.
Reversing that reindex and the original endpoint casts transports the whole
old primitive spine to the SAME internal subdivision. No trace, Owner,
observation or continuation producer is executed by these transports.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart zeroEndpoint)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {polynomial : Coefficients} {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (polynomial.eval start)} {request : AccuracyRequest}
variable (retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request)
variable {expression : Expression polynomial} {accuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The literal stored physical trace is the original whole factory on its SAME retained preparation and fit cache.

This uses the actual stored TraceCache, not winding or vertex equality.
The displayed finish Owner is reindexed by that same stored field witness.
-/
theorem trace_eq : retained.traced.trace.get =
    (PreparedPathTrace.CompleteSegment.ownerPath retained.traced.prepared
      retained.traced.budget retained.traced.fits).reindexOwners rfl retained.traced.finishOwner_eq.symm := by
  rewrite [retained.traced_eq]
  rfl

/-- View the unchanged old cache at the exact retained physical trace-factory index.

The index-only adapter expands inside its consumer so executable compilation
does not normalize the recursive observation family at the intermediate
reindexed path. Its complete input cache and exact path equality are retained.
-/
@[macro_inline] private def factorySpine (traced : PreparedPathTrace.TracedSegment segment within sourceOwner)
    (same : traced.trace.get = (PreparedPathTrace.CompleteSegment.ownerPath traced.prepared traced.budget
      traced.fits).reindexOwners rfl traced.finishOwner_eq.symm)
    (observed : Primitive.Spine expression accuracy traced.trace.get) :
    Primitive.Spine expression accuracy
      ((PreparedPathTrace.CompleteSegment.ownerPath traced.prepared traced.budget
        traced.fits).reindexOwners rfl traced.finishOwner_eq.symm) :=
  @Primitive.Spine.castPath polynomial expression accuracy start finish sourceOwner traced.finishOwner
    traced.trace.get
    ((PreparedPathTrace.CompleteSegment.ownerPath traced.prepared traced.budget
      traced.fits).reindexOwners rfl traced.finishOwner_eq.symm)
    same observed

/-- Reverse only the stored finishing-Owner reindex while preserving the whole original observation cache. -/
private def preparedSpine (observed : Primitive.Spine expression accuracy retained.traced.trace.get) :
    Primitive.Spine expression accuracy
      (PreparedPathTrace.CompleteSegment.ownerPath retained.traced.prepared retained.traced.budget
        retained.traced.fits) :=
  Primitive.Spine.uncastEndpoints rfl rfl (heq_of_eq (Eq.refl sourceOwner))
    (heq_of_eq retained.traced.finishOwner_eq.symm) (factorySpine retained.traced retained.trace_eq observed)

/-- Transport the complete actual physical observation spine to its SAME retained internal subdivision trace.

Both exact original endpoint coordinates and original Owner casts are
reversed. The original source, all old target observations and stationary
comparison caches cross together; only their nominal indices change.
-/
def internalSpine (observed : Primitive.Spine expression accuracy retained.traced.trace.get) :
    Primitive.Spine expression accuracy
      (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath retained.traced.budget
        retained.traced.prepared.subdivision retained.traced.fits) :=
  Primitive.Spine.uncastEndpoints retained.traced.prepared.start_eq retained.traced.prepared.finish_eq
    (by unfold ownerAtStart; exact RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ _)
    retained.traced.prepared.finishOwner_heq_terminalOwner.symm (preparedSpine retained observed)

/-- The internal view retains the entire literal old physical observation execution heterogeneously. -/
theorem internalSpine_heq (observed : Primitive.Spine expression accuracy retained.traced.trace.get) :
    HEq (retained.internalSpine observed) observed := by
  unfold internalSpine
  exact (Primitive.Spine.uncastEndpoints_heq _ _ _ _ (preparedSpine retained observed)).trans
    ((Primitive.Spine.uncastEndpoints_heq _ _ _ _ (factorySpine retained.traced retained.trace_eq observed)).trans
      (Primitive.Spine.castPath_heq retained.trace_eq observed))

/-- The whole internal view has the SAME old scalar values in their exact original physical order. -/
theorem internalSpine_values (observed : Primitive.Spine expression accuracy retained.traced.trace.get) :
    (retained.internalSpine observed).values = observed.values := by
  unfold internalSpine
  exact (Primitive.Spine.uncastEndpoints_values _ _ _ _ (preparedSpine retained observed)).trans
    ((Primitive.Spine.uncastEndpoints_values _ _ _ _ (factorySpine retained.traced retained.trace_eq observed)).trans
      (Primitive.Spine.castPath_values retained.trace_eq observed))

/-- The internal source is the complete original old physical source vertex with its unchanged request data. -/
theorem internalSpine_first_heq (observed : Primitive.Spine expression accuracy retained.traced.trace.get) :
    HEq (retained.internalSpine observed).first observed.first := by
  unfold internalSpine
  exact (Primitive.Spine.uncastEndpoints_first_heq _ _ _ _ (preparedSpine retained observed)).trans
    ((Primitive.Spine.uncastEndpoints_first_heq _ _ _ _ (factorySpine retained.traced retained.trace_eq observed)).trans
      (heq_of_eq (Primitive.Spine.castPath_first retained.trace_eq observed)))

/-- The internal finish is the complete original old physical final vertex with its unchanged request data. -/
theorem internalSpine_last_heq (observed : Primitive.Spine expression accuracy retained.traced.trace.get) :
    HEq (retained.internalSpine observed).last observed.last := by
  unfold internalSpine
  exact (Primitive.Spine.uncastEndpoints_last_heq _ _ _ _ (preparedSpine retained observed)).trans
    ((Primitive.Spine.uncastEndpoints_last_heq _ _ _ _ (factorySpine retained.traced retained.trace_eq observed)).trans
      (heq_of_eq (Primitive.Spine.castPath_last retained.trace_eq observed)))

/-- The initial scalar value is that of the SAME actual old physical source observation. -/
theorem internalSpine_first_value (observed : Primitive.Spine expression accuracy retained.traced.trace.get) :
    (retained.internalSpine observed).first.value = observed.first.value := by
  unfold internalSpine
  exact (Primitive.Spine.uncastEndpoints_first_value _ _ _ _ (preparedSpine retained observed)).trans
    ((Primitive.Spine.uncastEndpoints_first_value _ _ _ _
      (factorySpine retained.traced retained.trace_eq observed)).trans
      (Primitive.Spine.castPath_first_value retained.trace_eq observed))

/-- The final scalar value is that of the SAME actual old physical target observation. -/
theorem internalSpine_last_value (observed : Primitive.Spine expression accuracy retained.traced.trace.get) :
    (retained.internalSpine observed).last.value = observed.last.value := by
  unfold internalSpine
  exact (Primitive.Spine.uncastEndpoints_last_value _ _ _ _ (preparedSpine retained observed)).trans
    ((Primitive.Spine.uncastEndpoints_last_value _ _ _ _
      (factorySpine retained.traced retained.trace_eq observed)).trans
      (Primitive.Spine.castPath_last_value retained.trace_eq observed))

end Acquisition.Segment

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
