module
import Purelib.Data.List.Map
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.Paths.PreparedPathSources
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
import Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Sample
import Purelib.RootIsolation.State.WindingOne.Basic

public section

/-!
# Source grouping of the actual four-leg standard tours

The forward connector, right boundary, reversed connector and left boundary
retain their own original ambient boxes and sheet labels. Their source
certificates follow the actual initial banks and directed scheduler stages.
-/

section

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Riemann.Paths.PreparedPathSources (PathSources)
open Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements (DirectedRefinement)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

namespace Purelib.Riemann.Paths.PreparedTourSources

open Purelib.Curves.Hyperelliptic.Branches in
/-- Original path-source witnesses for the four ordered segments of a closed double tour.

Forward and right segments retain sheet zero; reversed connector and left segments retain sheet one, with their exact
concatenated parent list. -/
inductive TourSources (tour : ClosedBoundaryDoublePath curve) :
    List (CenteredEdge curve source) → Prop
  /-- Combine the four original path-source witnesses in forward, right, backward and left order. -/ | mk {forward right
    backward left : List (CenteredEdge curve source)}
      (forwardSource : PathSources 0 tour.joined.data.connector forward)
      (rightSource : PathSources 0 tour.joined.data.rightBoundaryPath right)
      (backwardSource : PathSources 1 (BranchCutLifts.ClearPath.reverse tour.joined.data.connector) backward)
      (leftSource : PathSources 1 tour.joined.data.leftBoundaryPath left) :
      TourSources tour (((forward ++ right) ++ backward) ++ left)

end Purelib.Riemann.Paths.PreparedTourSources

namespace Purelib.Riemann.Paths.PreparedTourSources.TourSources

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- The original root-closed initial tour retains its four checked path-source witnesses. -/
theorem initial (tour : ClosedBoundaryDoublePath curve) (source : Differentials.Basic.Differential genus) :
    TourSources tour (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tour source).state.parents
      := by
  change TourSources tour (PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.schedule tour
    source).toDifferential.initial.parents
  rw [PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.schedule_initial_parents]
  exact .mk (PathSources.ofDyadicBank source 0 tour.joined.data.forwardChecked)
    (PathSources.ofDyadicBank source 0 tour.joined.data.rightBoundaryChecked)
    (PathSources.ofDyadicBank source 1 tour.joined.data.backwardChecked)
    (PathSources.ofDyadicBank source 1 tour.joined.data.leftBoundaryChecked)

/-- Directed refinement preserves the original four-segment tour-source decomposition.

The retained child list is split at the three original segment boundaries, and each actual directed refinement
transports the corresponding source witness. -/
theorem refine {tour : ClosedBoundaryDoublePath curve} {parents children : List (CenteredEdge curve source)}
    (sources : TourSources tour parents) (refinement : DirectedRefinement parents children) : TourSources tour children
      := by
  cases sources with
  | @mk forward right backward left forwardSource rightSource backwardSource leftSource =>
      obtain ⟨firstThree, last, equal, firstThreePart, lastPart⟩ := refinement.split ((forward ++ right) ++ backward)
      obtain ⟨firstTwo, third, firstThreeEq, firstTwoPart, thirdPart⟩ := firstThreePart.split (forward ++ right)
      obtain ⟨first, second, firstTwoEq, firstPart, secondPart⟩ := firstTwoPart.split forward
      rw [equal, firstThreeEq, firstTwoEq]
      exact .mk (forwardSource.refine firstPart) (rightSource.refine secondPart)
        (backwardSource.refine thirdPart) (leftSource.refine lastPart)

end Purelib.Riemann.Paths.PreparedTourSources.TourSources

namespace Purelib.Riemann.Paths.PreparedTourSources.TourSources

open Purelib.Curves.Hyperelliptic in
/-- Differential recasting preserves the original tour geometry and ordered source decomposition. -/
theorem recast {tour : ClosedBoundaryDoublePath curve} {parents : List (CenteredEdge curve source)}
    (sources : TourSources tour parents) (target : Differentials.Basic.Differential genus) :
    TourSources tour (parents.map (recastCenteredEdge target)) := by
  cases sources with
  | mk forwardSource rightSource backwardSource leftSource =>
      simp only [Map.map_append, -eq_self, -iff_self]
      exact .mk (forwardSource.recast target) (rightSource.recast target)
        (backwardSource.recast target) (leftSource.recast target)

end Purelib.Riemann.Paths.PreparedTourSources.TourSources

end
