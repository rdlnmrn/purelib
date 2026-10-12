module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FramedAxisNeighbors
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection
public import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

public section

/-! Every side of an interior isolated hole has an actual retained regular
neighbor. All indices and adjacency witnesses are constructed from the grid. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

namespace HoleAdjacentFaces

/-- Boxes with a matching side share its anchor and therefore cannot be separated. -/
private theorem matching_not_separated {side : Meshes.GridLiftedDualSteps.GridSide} {first last :
  Rational.Box}
    (matching : side.Matches first last) : ¬ first.Separated last := by
  intro separated
  cases side with
  | bottom =>
    have inside : last.Contains first.anchor :=
      ⟨matching.1.symm.le, matching.1.trans_le last.x_valid, last.y_valid.trans_eq matching.2.2.symm, matching.2.2.le⟩
    exact separated.points_ne first.contains_anchor inside rfl
  | top =>
    have inside : first.Contains last.anchor :=
      ⟨matching.1.le, matching.1.symm.trans_le first.x_valid, first.y_valid.trans_eq matching.2.2, matching.2.2.symm.le⟩
    exact separated.points_ne inside last.contains_anchor rfl
  | left =>
    have inside : last.Contains first.anchor :=
      ⟨last.x_valid.trans_eq matching.2.2.symm, matching.2.2.le, matching.1.symm.le, matching.1.trans_le last.y_valid⟩
    exact separated.points_ne first.contains_anchor inside rfl
  | right =>
    have inside : first.Contains last.anchor :=
      ⟨first.x_valid.trans_eq matching.2.2, matching.2.2.symm.le, matching.1.le, matching.1.symm.trans_le first.y_valid⟩
    exact separated.points_ne inside last.contains_anchor rfl

/-- A retained side match rules out separation of its two boxes. -/
theorem matching_not_separated_for_face {side : Meshes.GridLiftedDualSteps.GridSide} {first last :
  Rational.Box}
    (matching : side.Matches first last) : ¬ first.Separated last := by
  intro separated
  cases side with
  | bottom =>
    have inside : last.Contains first.anchor :=
      ⟨matching.1.symm.le, matching.1.trans_le last.x_valid, last.y_valid.trans_eq matching.2.2.symm, matching.2.2.le⟩
    exact separated.points_ne first.contains_anchor inside rfl
  | top =>
    have inside : first.Contains last.anchor :=
      ⟨matching.1.le, matching.1.symm.trans_le first.x_valid, first.y_valid.trans_eq matching.2.2, matching.2.2.symm.le⟩
    exact separated.points_ne inside last.contains_anchor rfl
  | left =>
    have inside : last.Contains first.anchor :=
      ⟨last.x_valid.trans_eq matching.2.2.symm, matching.2.2.le, matching.1.symm.le, matching.1.trans_le last.y_valid⟩
    exact separated.points_ne first.contains_anchor inside rfl
  | right =>
    have inside : first.Contains last.anchor :=
      ⟨first.x_valid.trans_eq matching.2.2, matching.2.2.symm.le, matching.1.le, matching.1.symm.trans_le first.y_valid⟩
    exact separated.points_ne inside last.contains_anchor rfl

/-- A proper box cannot match one of its sides against itself. -/
private theorem matching_not_self {side : Meshes.GridLiftedDualSteps.GridSide} {box : Rational.Box}
  (proper : box.Proper) : ¬ side.Matches box box := by
  intro matching
  cases side with
  | bottom => exact (ne_of_lt proper.2) matching.2.2
  | top => exact (ne_of_lt proper.2) matching.2.2.symm
  | left => exact (ne_of_lt proper.1) matching.2.2
  | right => exact (ne_of_lt proper.1) matching.2.2.symm

/-- A retained proper face box has no side match with itself. -/
theorem matching_not_self_for_face {side : Meshes.GridLiftedDualSteps.GridSide} {box : Rational.Box}
  (proper : box.Proper) : ¬ side.Matches box box := by
  intro matching
  cases side with
  | bottom => exact (ne_of_lt proper.2) matching.2.2
  | top => exact (ne_of_lt proper.2) matching.2.2.symm
  | left => exact (ne_of_lt proper.1) matching.2.2
  | right => exact (ne_of_lt proper.1) matching.2.2.symm

end HoleAdjacentFaces

section FramedPuncturedGrid
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}

namespace HoleAdjacentFaces.FramedPuncturedGrid

set_option genInjectivity false in
/-- An actual grid cell adjoining a retained hole on a specified side.

Its membership and side match refer to the original grid and hole box. -/
structure AdjacentCell (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (side :
  Meshes.GridLiftedDualSteps.GridSide) where
  /-- The adjacent original grid cell. -/ cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
    (Hyperelliptic.Branches.Cuts.Ambient curve)
  /-- The adjacent cell belongs to the original grid cell list. -/ member : cell ∈ base.bank.grid.cells
  /-- The specified side of the hole matches the retained cell. -/ matching : side.Matches hole.cell.box cell.box

constructive_injectivity AdjacentCell

/-- A pair of original axis intervals determines a member of the original grid cell list. -/
private theorem cell_member (horizontal : Geometry.Grid.ClearGrid.Interval
  (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial := curve.polynomial) (ambient :=
  Hyperelliptic.Branches.Cuts.Ambient curve)))
    (vertical : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial :=
      curve.polynomial) (ambient := Hyperelliptic.Branches.Cuts.Ambient curve)))
    (hMember : horizontal ∈ base.bank.grid.xIntervals) (vMember : vertical ∈ base.bank.grid.yIntervals) :
    (⟨horizontal, vertical⟩ : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))
      ∈ base.bank.grid.cells :=

  open Purelib in Data.List.Flatten.mem_flatMap.mpr ⟨horizontal, hMember, Data.List.Map.mem_map.mpr ⟨vertical, vMember,
    rfl⟩⟩

end HoleAdjacentFaces.FramedPuncturedGrid

namespace HoleAdjacentFaces.FramedPuncturedGrid

/-- The retained horizontal and vertical interval memberships certify their grid cell. -/
theorem cell_member_for_adjacent (horizontal : Geometry.Grid.ClearGrid.Interval
  (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial := curve.polynomial) (ambient :=
  Hyperelliptic.Branches.Cuts.Ambient curve)))
    (vertical : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial :=
      curve.polynomial) (ambient := Hyperelliptic.Branches.Cuts.Ambient curve)))
    (hMember : horizontal ∈ base.bank.grid.xIntervals) (vMember : vertical ∈ base.bank.grid.yIntervals) :
    (⟨horizontal, vertical⟩ : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))
      ∈ base.bank.grid.cells :=

  open Purelib in Data.List.Flatten.mem_flatMap.mpr ⟨horizontal, hMember, Data.List.Map.mem_map.mpr ⟨vertical, vMember,
    rfl⟩⟩

end HoleAdjacentFaces.FramedPuncturedGrid

namespace HoleAdjacentFaces.FramedPuncturedGrid

/-- Find the original predecessor or successor cell adjoining the specified hole side.

Hole interiority excludes the outer-frame fallback and preserves the original axis membership and matching endpoint. -/
private def adjacentCell (base : Meshes.FramedPuncturedGrid curve branches higher)
    (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) : (side :
      Meshes.GridLiftedDualSteps.GridSide) →
      Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.AdjacentCell hole side
  | .bottom =>
      match Geometry.Grid.FramedAxisNeighbors.Predecessor.build hole.cell.vertical
        (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).2
        (Hyperelliptic.Branches.Cuts.Ambient curve).yLower base.bank.frame.yLower (fun line _ => line.inside.1) with
      | .previous found =>
          ⟨⟨hole.cell.horizontal, found.interval⟩,
            Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.cell_member hole.cell.horizontal
              found.interval (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).1
              found.member,
            ⟨rfl, rfl, found.endpoint_eq.symm⟩⟩
      | .exterior equal => False.elim ((ne_of_lt (base.hole_interior hole).bottom) equal.symm)
  | .top =>
      match Geometry.Grid.FramedAxisNeighbors.Successor.build hole.cell.vertical
        (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).2
        (Hyperelliptic.Branches.Cuts.Ambient curve).yUpper base.bank.frame.yUpper (fun line _ => line.inside.2) with
      | .next found =>
          ⟨⟨hole.cell.horizontal, found.interval⟩,
            Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.cell_member hole.cell.horizontal
              found.interval (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).1
              found.member,
            ⟨rfl, rfl, found.endpoint_eq.symm⟩⟩
      | .exterior equal => False.elim ((ne_of_lt (base.hole_interior hole).top) equal)
  | .left =>
      match Geometry.Grid.FramedAxisNeighbors.Predecessor.build hole.cell.horizontal
        (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).1
        (Hyperelliptic.Branches.Cuts.Ambient curve).xLower base.bank.frame.xLower (fun line _ => line.inside.1) with
      | .previous found =>
          ⟨⟨found.interval, hole.cell.vertical⟩,
            Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.cell_member found.interval
              hole.cell.vertical found.member (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem
              hole.cell hole.member).2,
            ⟨rfl, rfl, found.endpoint_eq.symm⟩⟩
      | .exterior equal => False.elim ((ne_of_lt (base.hole_interior hole).left) equal.symm)
  | .right =>
      match Geometry.Grid.FramedAxisNeighbors.Successor.build hole.cell.horizontal
        (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).1
        (Hyperelliptic.Branches.Cuts.Ambient curve).xUpper base.bank.frame.xUpper (fun line _ => line.inside.2) with
      | .next found =>
          ⟨⟨found.interval, hole.cell.vertical⟩,
            Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.cell_member found.interval
              hole.cell.vertical found.member (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem
              hole.cell hole.member).2,
            ⟨rfl, rfl, found.endpoint_eq.symm⟩⟩
      | .exterior equal => False.elim ((ne_of_lt (base.hole_interior hole).right) equal)

/-- Construct the actual cell adjoining an interior hole on the specified side.

The retained axis intervals and endpoint equalities certify original grid membership and the side match. -/
@[expose] def adjacentCell_for_hole (base : Meshes.FramedPuncturedGrid curve branches higher)
    (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) : (side :
      Meshes.GridLiftedDualSteps.GridSide) →
      Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.AdjacentCell hole side
  | .bottom =>
      match Geometry.Grid.FramedAxisNeighbors.Predecessor.build hole.cell.vertical
        (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).2
        (Hyperelliptic.Branches.Cuts.Ambient curve).yLower base.bank.frame.yLower (fun line _ => line.inside.1) with
      | .previous found =>
          ⟨⟨hole.cell.horizontal, found.interval⟩,
            Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.cell_member_for_adjacent
              hole.cell.horizontal found.interval (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem
              hole.cell hole.member).1 found.member,
            ⟨rfl, rfl, found.endpoint_eq.symm⟩⟩
      | .exterior equal => False.elim ((ne_of_lt (base.hole_interior hole).bottom) equal.symm)
  | .top =>
      match Geometry.Grid.FramedAxisNeighbors.Successor.build hole.cell.vertical
        (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).2
        (Hyperelliptic.Branches.Cuts.Ambient curve).yUpper base.bank.frame.yUpper (fun line _ => line.inside.2) with
      | .next found =>
          ⟨⟨hole.cell.horizontal, found.interval⟩,
            Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.cell_member_for_adjacent
              hole.cell.horizontal found.interval (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem
              hole.cell hole.member).1 found.member,
            ⟨rfl, rfl, found.endpoint_eq.symm⟩⟩
      | .exterior equal => False.elim ((ne_of_lt (base.hole_interior hole).top) equal)
  | .left =>
      match Geometry.Grid.FramedAxisNeighbors.Predecessor.build hole.cell.horizontal
        (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).1
        (Hyperelliptic.Branches.Cuts.Ambient curve).xLower base.bank.frame.xLower (fun line _ => line.inside.1) with
      | .previous found =>
          ⟨⟨found.interval, hole.cell.vertical⟩,
            Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.cell_member_for_adjacent
              found.interval hole.cell.vertical found.member
              (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).2,
            ⟨rfl, rfl, found.endpoint_eq.symm⟩⟩
      | .exterior equal => False.elim ((ne_of_lt (base.hole_interior hole).left) equal.symm)
  | .right =>
      match Geometry.Grid.FramedAxisNeighbors.Successor.build hole.cell.horizontal
        (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).1
        (Hyperelliptic.Branches.Cuts.Ambient curve).xUpper base.bank.frame.xUpper (fun line _ => line.inside.2) with
      | .next found =>
          ⟨⟨found.interval, hole.cell.vertical⟩,
            Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.cell_member_for_adjacent
              found.interval hole.cell.vertical found.member
              (Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell.intervals_mem hole.cell hole.member).2,
            ⟨rfl, rfl, found.endpoint_eq.symm⟩⟩
      | .exterior equal => False.elim ((ne_of_lt (base.hole_interior hole).right) equal)

set_option genInjectivity false in
/-- The original regular face adjoining a retained hole on one specified side. -/
structure HoleAdjacentFace (base : Meshes.FramedPuncturedGrid curve branches higher)
    (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (side :
      Meshes.GridLiftedDualSteps.GridSide) where
  /-- The position of the adjacent face in the original regular-face list. -/ position : Fin base.faces.regulars.length
  /-- The original hole side matches that regular face. -/ matching : side.Matches hole.cell.box
    base.faces.regulars[position.val].cell.box

constructive_injectivity HoleAdjacentFace

end HoleAdjacentFaces.FramedPuncturedGrid

namespace HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace

/-- Strict interiority excludes the frame; branch separation excludes every
other hole, and properness excludes the original hole itself. -/
@[expose] def build (base : Meshes.FramedPuncturedGrid curve branches higher)
    (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (side :
      Meshes.GridLiftedDualSteps.GridSide) :
      Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace base hole side := by
  let next := Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.adjacentCell_for_hole base hole
    side
  cases base.faces.locate next.cell next.member with
  | regular position equal => exact ⟨position, by rw [equal]; exact next.matching⟩
  | hole position equal =>
      let other := base.faces.holes[position.val]
      have matching : side.Matches hole.cell.box other.cell.box := by rw [equal]; exact next.matching
      by_cases same : hole.index = other.index
      · have cells : hole.cell = other.cell := hole.cell_eq.trans ((congrArg base.bank.toBranchCellBank.cell same).trans
          other.cell_eq.symm)
        rw [← cells] at matching
        exact (Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.matching_not_self_for_face hole.cell.box_proper
          matching).elim
      · have separated := base.holes_separated hole other same
        exact (Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.matching_not_separated_for_face matching
          separated).elim

end HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace

set_option genInjectivity false in
/-- The four original regular faces adjoining a retained hole.

Each named side retains its actual position and matching relation in the same framed grid. -/
structure HoleAdjacentFaces (base : Meshes.FramedPuncturedGrid curve branches higher)
    (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) where
  /-- The retained regular face adjoining the bottom hole side. -/ bottom :
    Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace base hole .bottom
  /-- The retained regular face adjoining the top hole side. -/ top :
    Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace base hole .top
  /-- The retained regular face adjoining the left hole side. -/ left :
    Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace base hole .left
  /-- The retained regular face adjoining the right hole side. -/ right :
    Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace base hole .right

constructive_injectivity HoleAdjacentFaces

namespace HoleAdjacentFaces

/-- Construct all four original adjacent regular faces from hole interiority and separation. -/
@[expose] def build (base : Meshes.FramedPuncturedGrid curve branches higher)
    (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) :
      HoleAdjacentFaces base hole :=
  ⟨FramedPuncturedGrid.HoleAdjacentFace.build base hole .bottom,
    Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace.build base hole .top,
    Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace.build base hole .left,
      Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace.build base hole .right⟩

end HoleAdjacentFaces

end FramedPuncturedGrid
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
