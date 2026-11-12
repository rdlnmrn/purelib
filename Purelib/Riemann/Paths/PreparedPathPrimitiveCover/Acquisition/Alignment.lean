module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.RootPath
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Alignment
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # Interior source alignment on the same complete acquisition comparison cache

The original acquisition already retains its actual subdivision, trace and
RootComparisons. This construction derives its new finite alignment spine
from the original physical starting comparison. Exact original endpoint
casts preserve the same first reference and source Owner; no acquisition,
trace, source preparation, advancement or center observation is rebuilt.
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
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter_initial_box)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
    {retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request}
    {actual : OwnerPath curve.polynomial start sourceOwner finish retained.traced.finishOwner}
    {actual_eq : actual = retained.traced.trace.get} {sheet : Fin 2}
    {referenceSource : Canonical} {referenceOwner : Owner referenceSource}
    {second : FixedRootBoxBudget.Budget referenceOwner}
    {movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (referenceSource - curve.polynomial.eval (segment.pointAt time)) ≤ second.movement}

namespace RootComparisons

variable (comparisons : RootComparisons curve differential retained actual actual_eq sheet second movement)
    (firstReference : Owner (curve.polynomial.eval start))

/-- The exact original-subdivision alignment family on the SAME cached complete acquisition and first reference. -/
@[expose] def Alignment := Comparison.Cache.Alignment comparisons (ownerAtStart segment firstReference)

/-- Derive interior source/reference alignments from the original actual cache and starting relation.

The physical source/reference names are transported by the same original
start_eq and ownerAtStart laws used by the original finish comparison.
The cache's actual stationary links and moving Owners supply all later
handoffs; no retained advancement or root query is replayed.
-/
def align (refines : firstReference.track.initial.box.Refines referenceOwner.track.initial.box)
    (initial : NamedEquivalent (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName firstReference.parameterNonzero firstReference)) :
    Alignment comparisons firstReference := by
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
  exact Comparison.Cache.Alignment.build comparisons (ownerAtStart segment firstReference) bounded starting

end RootComparisons

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment

end
