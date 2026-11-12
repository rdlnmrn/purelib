module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.RootPath
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootChain
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Open root chains of the same materialized acquisition parents

This consumer takes the original Parents and actual materialized trace
views, optionally retained by the original root-comparison cache. Its center family and covered parent list are reused
literally. Only their stored whole-factory and exact endpoint-name laws
transport the resulting open chain to the acquisition's physical Owners.
There is no new acquisition, source query, advancement or center factory.
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
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
    {retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request}
    {sheet : Fin 2} {count : Nat}

attribute [local irreducible] CertifiedSquareRoot.rawRoot
attribute [local irreducible] SquareRootTrackEquivalence.ownerRootName

namespace Parents

/-- Build the open root chain on this same covered parent list using its retained centers and actual trace views.

Both displayed endpoints are the original physical acquisition Owners.
The stored Parents factory equation transports the actual centered list;
the original start/finish casts transport only their nominal root names.
The default retains views from the same materialized original trace;
a supplied cache contributes its literal stored views. No target allocation,
bank position or existing source preparation changes.
-/
def rootChain (parents : Parents differential sheet count retained)
    (views : PreparedSubdivisionTrace.PreparedTraceBudget.Trace.RootViews retained.traced.prepared.subdivision :=
      (retained.rootTrace retained.traced.trace.get rfl).rootViews) :
    RootChain parents.covered.parents (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName retained.traced.finishOwner.parameterNonzero retained.traced.finishOwner) := by
  let internal := PreparedBankRootChains.subdivisionRootChain curve differential segment within sheet
    retained.traced.prepared.subdivision parents.centers (some views)
  have firstName := PreparedBankRootChains.ownerAtStart_name segment sourceOwner
  have lastName := PreparedBankRootChains.finishOwner_name retained.traced.prepared
  have displayed := congrArg (fun owner : Owner (curve.polynomial.eval finish) =>
    ownerRootName owner.parameterNonzero owner) retained.traced.finishOwner_eq
  let physical := PreparedBankRootChains.RootChain.castNames firstName (lastName.trans displayed.symm) internal
  exact PreparedBankRootChains.RootChain.castChildren parents.parents_eq.symm physical

end Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment

end
