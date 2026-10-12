module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Polynomial.Geometry.Grid.Winding
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Geometry.Grid.Winding

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration.PreparedOwnerClosedBridges

open Purelib.Riemann.Paths.PreparedPathClosure

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PreparedBoundaryClosure

open Purelib.RootIsolation.State

@[expose] public section

/-!
# Actual owner-closed A/B tours on the common grid

Split all four retained geometric legs, including both branch boundaries.
Their concatenation is an endpoint-closed walk on adjacent grid edges, stays
in the original ambient rectangle, and has the original winding.  This is
geometric subdivision of the existing tours, not a replacement period bank
or a claim about geometric intersection numbers.
-/

namespace Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Riemann.Integration.PreparedOwnerClosedBridges (OwnerClosedCyclePair)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid (branchGrid branchGrid_aTour branchGrid_bTour)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)

namespace Grid

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box}

/-- Split the actual four legs once, in their original traversal order. -/
def splitTour (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient) (tour :
  PreparedBoundaryClosure.ClosedBoundaryDoublePath
  curve)
    (onGrid : Grid.ContainsTourVertices grid tour) :
    Walks.Walk grid tour.joined.data.leftState.box.anchor tour.joined.data.leftState.box.anchor :=
  let forward := Walks.splitPath grid tour.joined.data.connector onGrid.1
  let right := Walks.splitPath grid tour.joined.data.rightBoundaryPath onGrid.2.1
  let backward := Walks.splitPath grid (ClearPath.reverse tour.joined.data.connector) onGrid.2.2.1
  let left := Walks.splitPath grid tour.joined.data.leftBoundaryPath onGrid.2.2.2
  forward.append (right.append (backward.append left))

/-- Connector winding cancels after the actual grid subdivision, leaving exactly the two original boundary
contributions. -/
theorem splitTour_winding (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient) (tour :
  PreparedBoundaryClosure.ClosedBoundaryDoublePath curve)
    (onGrid : Grid.ContainsTourVertices grid tour) :
    ClearPath.rawWinding (splitTour grid tour onGrid).path =
      ClearPath.rawWinding tour.joined.data.rightBoundaryPath +
        ClearPath.rawWinding tour.joined.data.leftBoundaryPath := by
  dsimp only [splitTour]
  rw [Walk.append_winding, Walk.append_winding, Walk.append_winding,
    Winding.splitPath_winding, Winding.splitPath_winding, Winding.splitPath_winding, Winding.splitPath_winding,
    ClearPath.rawWinding_reverse]
  omega

/-- The original four-leg tour remains within the ambient box after its grid subdivision. -/
theorem splitTour_withinAmbient (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient) (tour :
  PreparedBoundaryClosure.ClosedBoundaryDoublePath curve)
    (onGrid : Grid.ContainsTourVertices grid tour) : (splitTour grid
      tour onGrid).path.WithinAmbient :=
  (splitTour grid tour onGrid).withinAmbient

/-- Every vertex of the subdivided original four-leg tour belongs to the retained grid. -/
theorem splitTour_vertices (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient) (tour :
  PreparedBoundaryClosure.ClosedBoundaryDoublePath curve)
    (onGrid : Grid.ContainsTourVertices grid tour) : Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid
      (splitTour grid tour onGrid).path :=
  (splitTour grid tour onGrid).vertices
    (Polynomial.Geometry.Grid.FromStates.ContainsPathVertices.start
    grid _ onGrid.1)

end Grid

/-- Subdivide the actual canonical A tour on the one shared branch grid. -/
def aTourWalkOfData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (index : Fin genus) :
    Walks.Walk (BranchGrid.branchGrid curve (BranchConfiguration.configurationOfData curve branches).branches higher 0)
      (OwnerClosedCyclePair.ofData curve branches index).aTour.joined.data.leftState.box.anchor
      (OwnerClosedCyclePair.ofData curve branches index).aTour.joined.data.leftState.box.anchor :=
  Curves.Hyperelliptic.Branches.BranchGridPaths.Grid.splitTour _ _ (BranchGrid.branchGrid_aTour curve branches higher
    index)

/-- The reference B bridge includes the same actual branch-boundary loops as the root-closed period program; it is not
the old connector-only path. -/
def bTourWalkOfData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (index : Fin genus) :
    Walks.Walk (BranchGrid.branchGrid curve (BranchConfiguration.configurationOfData curve branches).branches higher 0)
      (OwnerClosedCyclePair.ofData curve branches index).bTour.joined.data.leftState.box.anchor
      (OwnerClosedCyclePair.ofData curve branches index).bTour.joined.data.leftState.box.anchor :=
  Curves.Hyperelliptic.Branches.BranchGridPaths.Grid.splitTour _ _ (BranchGrid.branchGrid_bTour curve branches higher
    index)

/-- The return check preserves the two supplied winding-one boundaries. -/
private theorem total_boundaryWinding {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {leftAmbient rightAmbient connectorAmbient : Rational.Box}
    (leftState : WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient)
    (owner : PreparedSheetContinuation.Owner (curve.polynomial.eval leftState.box.anchor)) :
    ClearPath.rawWinding (ClosedBoundaryDoublePath.total leftState
      rightState connector within owner).joined.data.rightBoundaryPath +
      ClearPath.rawWinding (ClosedBoundaryDoublePath.total leftState
        rightState connector within owner).joined.data.leftBoundaryPath = 8 := by
  unfold ClosedBoundaryDoublePath.total
  dsimp only
  split
  · rename_i closed accepted
    rw [ClosedBoundaryDoublePath.checkReturn_joined _ closed accepted]
    change ClearPath.rawWinding (BranchCutLifts.ownerBoundaryPath rightState) +
      ClearPath.rawWinding (BranchCutLifts.ownerBoundaryPath leftState) = 8
    rw [BranchCutLifts.ownerBoundaryPath_rawWinding, BranchCutLifts.ownerBoundaryPath_rawWinding]
    rfl
  · change ClearPath.rawWinding (BranchCutLifts.ownerBoundaryPath rightState) +
      ClearPath.rawWinding (BranchCutLifts.ownerBoundaryPath leftState) = 8
    rw [BranchCutLifts.ownerBoundaryPath_rawWinding, BranchCutLifts.ownerBoundaryPath_rawWinding]
    rfl

/-- The subdivided canonical A tour retains raw winding eight from its two original branch boundaries. -/
theorem aTourWalkOfData_winding {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (index : Fin genus) :
    ClearPath.rawWinding (aTourWalkOfData curve branches higher
      index).path = 8 := by
  dsimp only [aTourWalkOfData]
  rw [Curves.Hyperelliptic.Branches.BranchGridPaths.Grid.splitTour_winding]
  exact total_boundaryWinding _ _ _ _ _

/-- The subdivided canonical B tour retains raw winding eight from its two original branch boundaries. -/
theorem bTourWalkOfData_winding {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (index : Fin genus) :
    ClearPath.rawWinding (bTourWalkOfData curve branches higher
      index).path = 8 := by
  dsimp only [bTourWalkOfData]
  rw [Curves.Hyperelliptic.Branches.BranchGridPaths.Grid.splitTour_winding]
  exact total_boundaryWinding _ _ _ _ _

end Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths
