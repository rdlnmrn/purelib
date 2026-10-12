module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.RootOwnerNegation
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Riemann.RootContinuation.ClearBoxRootNegation
public import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

@[expose] public section

/-!
# Opposite roots at actual prepared face queries

The existing reachability certificates contain finite owner prefixes with
the face's winding potential. A single return path proves that the two
queries occupy opposite endpoint occurrences. Only endpoint classification
and negation caches are executed; the prefix witnesses remain erased.
-/

namespace Purelib.RootIsolation.SquareRoot.Preparation.FaceNegation

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {box : Box} {start finish :
  Gaussian.Basic.Canonical}
  {source : Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval start)} {sheet : Fin 2}
  {first last : Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval finish)}

/-- Both endpoint queries keep their actual owners. Their classification in
the supplied shared frame is retained once, with an operational negative-root
comparison obtained without a caller sign or winding hypothesis. -/
def oppositeOfReached (frame : Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval finish))
    (clearance : Clearance.Box.Region.RegionClearance polynomial box)
    (degreePositive : 0 < polynomial.natDegree) (reference : Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial
      start)
    (startInside : box.Contains start) (finishInside : box.Contains finish)
    (firstReached : Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached box (source.owners
      sheet) first)
    (lastReached : Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached box (source.owners
      (Curves.Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)) last) :
    Riemann.RootContinuation.ClearBoxRootNegation.SquareRootTrace.OwnerFrame.OppositeOwners frame first last := by
  let left := frame.select first
  let right := frame.select last
  refine ⟨left, right, ?_,
    Riemann.RootContinuation.RootOwnerNegation.negation frame left.index⟩
  obtain ⟨firstPath, firstWinding⟩ := firstReached
  obtain ⟨lastPath, lastWinding⟩ := lastReached
  let route := Riemann.Paths.ClearBoxPaths.Route.build clearance finish start finishInside startInside
  let backward := Riemann.RootContinuation.RootPathTransport.PathTransport.build route.path route.within frame source
  have returnWinding := Riemann.Paths.ClearBoxPathWinding.Route.winding
    clearance degreePositive route finishInside
  apply Riemann.RootContinuation.ClearBoxRootNegation.SquareRootTrace.OwnerPath.selections_opposite
    firstPath reference lastPath left right backward
  · rw [firstWinding, returnWinding]
    omega0
  · rw [lastWinding, returnWinding]
    omega0

end Purelib.RootIsolation.SquareRoot.Preparation.FaceNegation
