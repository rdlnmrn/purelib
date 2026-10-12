module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.FromStates
public import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Init.Data.List.OfFn
import Purelib.Data.List.OfFn.Basic
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.Topology.PreparedCycleModels

public section

/-!
# The common clear-line grid of the actual branch tours

The grid retains all four ambient line certificates of every selected branch
box.  Thus every original connector and branch-boundary corner lies on one
shared finite coordinate grid, and every branch box is covered.  These facts
do not classify the grid's interior faces or assert symplectic intersections.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid

open Purelib
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Riemann.Integration.PreparedOwnerClosedBridges
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.PreparedBoundaryClosure
open Purelib.Riemann.Topology
open Purelib.RootIsolation.State
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (build build_vertical_coordinates build_horizontal_coordinates)
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGridCoverage (Located)
open Purelib.Polynomial.Geometry.Grid.FromStates (BranchState verticalSides horizontalSides)

open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

/-- The original shrinking states, materialized once for the finite branch family. Both period tours and this grid use
the same refinement index. -/
@[expose] def branchStates {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (refinement : Nat) : List (FromStates.BranchState curve.polynomial
      (Cuts.Ambient curve)) :=
  List.ofFn fun index => Cuts.refinedState branches higher index refinement

/-- Every original branch occurrence contributes its exact refined state to the shared finite state list. -/
theorem refinedState_mem_branchStates {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (refinement : Nat) (index : Data.Index branches) :
    Cuts.refinedState branches higher index refinement ∈
      branchStates curve branches higher refinement :=
  Purelib.Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩

/-- Construct one clear-line grid from the original branch states at their shared refinement index. -/
@[expose] def branchGrid {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (refinement : Nat) : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
      (Cuts.Ambient curve)
      :=
  Polynomial.Geometry.Grid.FromStates.ofStates (branchStates curve
    branches higher refinement)

/-- Both bends and endpoints of every standard connector are in this one grid, independently of which branch indices are
paired. -/
theorem branchGrid_connector {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (refinement : Nat) (left right : Data.Index branches) :
    Polynomial.Geometry.Grid.FromStates.ContainsPathVertices
      (branchGrid curve branches higher
      refinement)
      (Cuts.connectorAt branches higher left right refinement) := by
  let states := branchStates curve branches higher refinement
  have leftMember := refinedState_mem_branchStates curve branches
    higher refinement left
  have rightMember := refinedState_mem_branchStates curve branches
    higher refinement right
  have leftX := (Polynomial.Geometry.Grid.FromStates.ofStates_x_bounds states leftMember).1
  have rightX := (Polynomial.Geometry.Grid.FromStates.ofStates_x_bounds states rightMember).1
  have leftY := (Polynomial.Geometry.Grid.FromStates.ofStates_y_bounds states leftMember).1
  have rightY := (Polynomial.Geometry.Grid.FromStates.ofStates_y_bounds states rightMember).1
  exact ⟨⟨leftX, leftY⟩, ⟨rightX, leftY⟩, rightX, rightY⟩

/-- Every original refined branch-box boundary vertex belongs to the shared clear-line grid. -/
theorem branchGrid_boundary {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (refinement : Nat) (index : Data.Index branches) :
    Polynomial.Geometry.Grid.FromStates.ContainsPathVertices
      (branchGrid curve branches higher
      refinement)
      (BranchCutLifts.ownerBoundaryPath (Cuts.refinedState branches higher index refinement)) :=
  Polynomial.Geometry.Grid.FromStates.ofStates_boundary _
    (refinedState_mem_branchStates curve
    branches higher refinement index)

namespace Grid

/-- All original connector and boundary corners of a retained owner-closed tour lie in one grid. Reversing the connector
introduces no new coordinates. -/
@[expose] def ContainsTourVertices {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {gridAmbient :
  Rational.Box}
    (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial gridAmbient) (tour :
      PreparedBoundaryClosure.ClosedBoundaryDoublePath curve)
      : Prop :=
  Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid tour.joined.data.connector ∧
    Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid tour.joined.data.rightBoundaryPath ∧
    Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid (ClearPath.reverse tour.joined.data.connector) ∧
    Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid tour.joined.data.leftBoundaryPath

/-- Both return-check outcomes retain the supplied connector and boundary paths. Grid membership therefore uses their
geometry without unfolding the chosen preparation banks. -/
theorem containsTourVertices_total {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {gridAmbient leftAmbient rightAmbient connectorAmbient : Rational.Box}
    (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial gridAmbient)
    (leftState : WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient)
    (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval leftState.box.anchor))
    (connectorOn : Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid connector)
    (rightOn : Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid (BranchCutLifts.ownerBoundaryPath
      rightState))
    (leftOn : Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid (BranchCutLifts.ownerBoundaryPath
      leftState)) :
    ContainsTourVertices grid
      (Purelib.Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath.total leftState rightState connector
        within owner) := by
  unfold ClosedBoundaryDoublePath.total
  dsimp only
  split
  · rename_i closed accepted
    unfold ContainsTourVertices
    rw [ClosedBoundaryDoublePath.checkReturn_joined _ closed accepted]
    exact ⟨connectorOn, rightOn, Polynomial.Geometry.Grid.FromStates.ContainsPathVertices.reverse grid connector
      connectorOn, leftOn⟩
  · exact ⟨connectorOn, rightOn, Polynomial.Geometry.Grid.FromStates.ContainsPathVertices.reverse grid connector
      connectorOn, leftOn⟩

end Grid

/-- The paired A construction uses precisely the geometry present in the common branch grid, not a separately acquired
path with matching labels. -/
theorem branchGrid_aTour {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (index : Fin genus) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid.ContainsTourVertices
      (branchGrid curve (BranchConfiguration.configurationOfData
      curve branches).branches higher 0)
      (OwnerClosedCyclePair.ofData curve branches index).aTour := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid.containsTourVertices_total
  · exact branchGrid_connector curve _ higher 0 _ _
  · exact branchGrid_boundary curve _ higher 0 _
  · exact branchGrid_boundary curve _ higher 0 _

/-- Every paired B reference bridge uses the very same grid as A, including the additional actual branch-boundary loops
needed for root closure. -/
theorem branchGrid_bTour {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) (index : Fin genus) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid.ContainsTourVertices
      (branchGrid curve (BranchConfiguration.configurationOfData
      curve branches).branches higher 0)
      (OwnerClosedCyclePair.ofData curve branches index).bTour := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid.containsTourVertices_total
  · exact branchGrid_connector curve _ higher 0 _ _
  · exact branchGrid_boundary curve _ higher 0 _
  · exact branchGrid_boundary curve _ higher 0 _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid

end
