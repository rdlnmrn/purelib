module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
public import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.RootPath
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.RootChain
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Original root chains on the same retained paid subdivision and center cache

The actual Parents supplies its unchanged selected center states. The SAME
materialized trace and its original complete factory identity supply the
source/moving/retention views. No continuation or preparation is replayed;
the displayed endpoints remain the literal paid source and finish.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget (Trace)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
variable {paid : Segment (segment := segment) (within := within) (owner := sourceOwner) request}
variable {sheet : Fin 2} {count : Nat}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Read the original signed root chain of these SAME prepared cells and retained center states.

The original materialized trace supplies every accepted source and reserve
retention link. Whole parent-list equality and the original exact finish-owner
name law transport only endpoints and list indices. Neither a continuation,
source preparation, center nor endpoint observation is executed again.
-/
def subdivisionRoots (parents : Parents differential sheet count paid) :
    RootChain parents.covered.parents (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName paid.traced.finishOwner.parameterNonzero paid.traced.finishOwner) := by
  let trace := paid.rootTrace paid.traced.trace.get rfl
  let internal := Trace.rootChain (curve := curve) (differential := differential) (sheet := sheet)
    trace parents.centers
  have first := PreparedBankRootChains.ownerAtStart_name segment sourceOwner
  have last := PreparedBankRootChains.finishOwner_name paid.traced.prepared
  have displayed := congrArg (fun owner : Owner (curve.polynomial.eval finish) =>
    ownerRootName owner.parameterNonzero owner) paid.traced.finishOwner_eq
  let physical := PreparedBankRootChains.RootChain.castNames first (last.trans displayed.symm) internal
  exact PreparedBankRootChains.RootChain.castChildren parents.parents_eq.symm physical

end Acquisition.Segment.Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
