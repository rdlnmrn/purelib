module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

public section

/-! Read exactly the hole part of a retained physical neighbor. -/

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces (SideNeighbor)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {faces : PuncturedFaces bank} {face : RegularFace bank} {side : GridSide}

/-- The retained geometric side neighbor is a physical hole. -/
@[expose] def HasHole
    (neighbor : SideNeighbor faces face side) : Prop :=
  match neighbor with
  | .exterior _ => False
  | .neighbor _ _ _ location =>
    match location with
    | .regular _ _ => False
    | .hole _ _ => True

/-- Retain the supplied value exactly when the original side neighbor is a hole. -/
@[expose] def holeValue
    (neighbor : SideNeighbor faces face side) (value : Gaussian.Basic.Canonical) : Gaussian :=
  match neighbor with
  | .exterior _ => 0
  | .neighbor _ _ _ location =>
    match location with
    | .regular _ _ => 0
    | .hole _ _ => value

/-- An actual geometric match with an original hole certifies that the retained neighbor is a hole. -/
theorem hasHole_of_matches
    (neighbor : SideNeighbor faces face side)
    (hole : Fin faces.holes.length)
    (matching : side.Matches face.cell.box (faces.holes[hole.val]'hole.isLt).cell.box) : SideNeighbor.HasHole neighbor
      := by
  cases neighbor with
  | exterior exterior =>
    exact GridSide.exterior_no_match exterior (faces.holes[hole.val]'hole.isLt).cell.box_proper
      (faces.holes[hole.val]'hole.isLt).cell.box_refines matching
  | neighbor cell member matched location =>
    have equal := GridSide.matches_unique side (faces.holes[hole.val]'hole.isLt).member member matching matched
    cases location with
    | hole found foundEq => trivial
    | regular found foundEq =>
      exact (faces.regulars[found.val]'found.isLt).unassigned (faces.holes[hole.val]'hole.isLt).index
        (foundEq.trans (equal.symm.trans (faces.holes[hole.val]'hole.isLt).cell_eq))

/-- An actual match with an original hole preserves the whole supplied hole-side value. -/
theorem holeValue_of_matches
    (neighbor : SideNeighbor faces face side)
    (hole : Fin faces.holes.length)
    (matching : side.Matches face.cell.box (faces.holes[hole.val]'hole.isLt).cell.box) (value :
      Gaussian.Basic.Canonical) :
    SideNeighbor.holeValue neighbor value = value := by
  have supported := SideNeighbor.hasHole_of_matches neighbor hole matching
  cases neighbor with
  | exterior _ => exact supported.elim
  | neighbor _ _ _ location =>
    cases location with
    | regular _ _ => exact supported.elim
    | hole _ _ => rfl

/-- The retained hole-side value equals the finite sum of its individual original hole-component values. -/
theorem holeValue_components
    (neighbor : SideNeighbor faces face side) (value : Gaussian.Basic.Canonical) :
    SideNeighbor.holeValue neighbor value = FiniteSum.Fin.sumFin (fun hole =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor (.hole hole)
        value) := by
  cases neighbor with
  | exterior _ => exact FiniteSum.Fin.sumFin_zero.symm
  | neighbor _ _ _ location =>
    cases location with
    | regular _ _ => exact FiniteSum.Fin.sumFin_zero.symm
    | hole position _ => exact (FiniteSum.Fin.sumFin_ite_eq position (fun _ => value)).symm

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor
