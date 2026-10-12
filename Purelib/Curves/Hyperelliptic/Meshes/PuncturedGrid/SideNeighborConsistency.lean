module
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

@[expose] public section

/-! Exact exclusivity, reversal, and uniqueness of physical side neighbors. -/
namespace Purelib.Riemann.Meshes
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces (SideNeighbor)

namespace GridLiftedDualSteps.GridSide

/-- Reverse the original directed rectangle side. -/
def opposite : GridSide → GridSide
  | .bottom => .top
  | .top => .bottom
  | .left => .right
  | .right => .left

/-- Exact original side matching reverses along the opposite directed side. -/
theorem Matches.reverse {side : GridSide} {first next :
  Rational.Box} (matching : side.Matches first next) :
    side.opposite.Matches next first := by
  cases side <;> exact ⟨matching.1.symm, matching.2.1.symm, matching.2.2.symm⟩

/-- An original ambient-boundary side cannot match a proper box contained in the same ambient rectangle. -/
theorem exterior_no_match {side : GridSide} {face next
  ambient : Rational.Box}
    (exterior : side.Exterior face ambient) (proper : next.Proper) (inside : next.Refines ambient) :
    ¬ side.Matches face next := by
  intro matching
  cases side with
  | bottom =>
      exact (not_lt_of_ge ((matching.2.2.symm.trans exterior).trans_le inside.2.2.1)) proper.2
  | top =>
      exact (not_lt_of_ge (inside.2.2.2.trans_eq (exterior.symm.trans matching.2.2))) proper.2
  | left =>
      exact (not_lt_of_ge ((matching.2.2.symm.trans exterior).trans_le inside.1)) proper.1
  | right =>
      exact (not_lt_of_ge (inside.2.1.trans_eq (exterior.symm.trans matching.2.2))) proper.1

/-- Two retained grid cells matching the same original directed face side are equal. -/
theorem matches_unique {polynomial :
  ClearPath.GaussianPolynomial} {ambient source : Rational.Box}
    {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {first second : ClearGrid.Cell polynomial ambient}
      (side : GridSide)
    (firstMember : first ∈ grid.cells) (secondMember : second ∈ grid.cells)
    (left : side.Matches source first.box) (right : side.Matches source second.box) : first = second := by
  cases side with
  | bottom =>
      exact Cell.eq_of_left_top firstMember secondMember
        (left.1.symm.trans right.1) (left.2.2.symm.trans right.2.2)
  | top =>
      exact Cell.eq_of_lower firstMember secondMember
        (left.1.symm.trans right.1) (left.2.2.symm.trans right.2.2)
  | left =>
      exact Cell.eq_of_right_bottom firstMember secondMember
        (left.2.2.symm.trans right.2.2) (left.1.symm.trans right.1)
  | right =>
      exact Cell.eq_of_lower firstMember secondMember
        (left.2.2.symm.trans right.2.2) (left.1.symm.trans right.1)

end GridLiftedDualSteps.GridSide
namespace PuncturedGridFaces.PuncturedFaces.SideNeighbor
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {face : RegularFace bank} {side : GridSide}

/-- The retained side-neighbor certificate identifies the exact requested original regular-face position. -/
def RegularAt (neighbor : SideNeighbor
  faces face side) (position : Fin faces.regulars.length) : Prop :=
  match neighbor with
  | .neighbor _ _ _ (.regular found _) => found = position
  | .neighbor _ _ _ (.hole _ _) => False
  | .exterior _ => False

/-- Geometric matching with an original regular face identifies that exact retained neighbor position. -/
theorem regular_of_matches (neighbor :
  SideNeighbor faces face side)
    (position : Fin faces.regulars.length) (matching : side.Matches face.cell.box faces.regulars[position.val].cell.box)
      :
    neighbor.RegularAt position := by
  cases neighbor with
  | neighbor cell member neighborMatches location =>
      have equal := GridSide.matches_unique side faces.regulars[position.val].member member matching neighborMatches
      cases location with
      | regular found foundEq => exact faces.position_eq_of_cell found position (foundEq.trans equal.symm)
      | hole found foundEq =>
          exact faces.regulars[position.val].unassigned faces.holes[found.val].index
            (equal.trans (foundEq.symm.trans faces.holes[found.val].cell_eq))
  | exterior exterior =>
      exact GridSide.exterior_no_match exterior faces.regulars[position.val].cell.box_proper
        faces.regulars[position.val].cell.box_refines matching

/-- The retained regular-neighbor position supplies exact matching of the original face side. -/
theorem matches_of_regular (neighbor :
  SideNeighbor faces face side)
    (position : Fin faces.regulars.length) (regular : neighbor.RegularAt position) :
    side.Matches face.cell.box faces.regulars[position.val].cell.box := by
  cases neighbor with
  | neighbor cell member matching location =>
      cases location with
      | regular found equal =>
          change found = position at regular
          subst position
          rw [equal]
          exact matching
      | hole found equal => exact regular.elim
  | exterior exterior => exact regular.elim

/-- The retained regular-neighbor index is equivalent to exact geometric matching of the original directed side. -/
theorem regular_iff (neighbor :
  SideNeighbor faces face side) (position : Fin faces.regulars.length) :
    neighbor.RegularAt position ↔ side.Matches face.cell.box faces.regulars[position.val].cell.box :=
  ⟨neighbor.matches_of_regular position, neighbor.regular_of_matches position⟩

end PuncturedGridFaces.PuncturedFaces.SideNeighbor
end Purelib.Riemann.Meshes
