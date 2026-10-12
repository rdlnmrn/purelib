module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Riemann.Meshes.GridLiftedEdgeUniqueness
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data.List

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.CellBoundary

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Riemann.Meshes

@[expose] public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

/-! Uniqueness concerns retained face positions, not merely equal boxes. -/
section
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace PuncturedFaces)

section
variable {polynomial : GaussianPolynomial} {ambient :
  Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}
  {first second : Cell polynomial ambient}

namespace Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell

/-- Two cells of the same clear grid with equal lower-left coordinates are equal. -/
theorem eq_of_lower (firstMember : first ∈ grid.cells)
  (secondMember : second ∈ grid.cells)
    (horizontal : first.box.xLower = second.box.xLower)
    (vertical : first.box.yLower = second.box.yLower) : first = second :=
  congrArg₂ Cell.mk
    (AxisNeighbors.eq_of_lower grid.vertical_ordered (Cell.intervals_mem first firstMember).1
      (Cell.intervals_mem second secondMember).1 horizontal)
    (AxisNeighbors.eq_of_lower grid.horizontal_ordered (Cell.intervals_mem first firstMember).2
      (Cell.intervals_mem second secondMember).2 vertical)

/-- Two cells of the same clear grid with equal left and top coordinates are equal. -/
theorem eq_of_left_top (firstMember : first ∈ grid.cells)
  (secondMember : second ∈ grid.cells)
    (horizontal : first.box.xLower = second.box.xLower)
    (vertical : first.box.yUpper = second.box.yUpper) : first = second :=
  congrArg₂ Cell.mk
    (AxisNeighbors.eq_of_lower grid.vertical_ordered (Cell.intervals_mem first firstMember).1
      (Cell.intervals_mem second secondMember).1 horizontal)
    (AxisNeighbors.eq_of_upper grid.horizontal_ordered (Cell.intervals_mem first firstMember).2
      (Cell.intervals_mem second secondMember).2 vertical)

/-- Two cells of the same clear grid with equal right and bottom coordinates are equal. -/
theorem eq_of_right_bottom (firstMember : first ∈ grid.cells)
  (secondMember : second ∈ grid.cells)
    (horizontal : first.box.xUpper = second.box.xUpper)
    (vertical : first.box.yLower = second.box.yLower) : first = second :=
  congrArg₂ Cell.mk
    (AxisNeighbors.eq_of_upper grid.vertical_ordered (Cell.intervals_mem first firstMember).1
      (Cell.intervals_mem second secondMember).1 horizontal)
    (AxisNeighbors.eq_of_lower grid.horizontal_ordered (Cell.intervals_mem first firstMember).2
      (Cell.intervals_mem second secondMember).2 vertical)

end Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell

end
section
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness.BranchCellBank

/-- A proper original regular-face box cannot be interior-separated from itself. -/
private theorem not_self_separated (face : PuncturedGridFaces.RegularFace bank) : ¬ face.cell.box.InteriorSeparated
  face.cell.box := by
  intro separated
  rcases separated with before | after | below | above
  · exact (not_lt_of_ge before) face.cell.box_proper.1
  · exact (not_lt_of_ge after) face.cell.box_proper.1
  · exact (not_lt_of_ge below) face.cell.box_proper.2
  · exact (not_lt_of_ge above) face.cell.box_proper.2

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness.BranchCellBank

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

/-- Equal retained regular-face cells have equal positions in the original pairwise-separated classification list. -/
theorem position_eq_of_cell (faces :
  PuncturedGridFaces.PuncturedFaces bank)
    (first second : Fin faces.regulars.length)
    (equal : faces.regulars[first.val].cell = faces.regulars[second.val].cell) : first = second := by
  rcases Nat.lt_trichotomy first.val second.val with before | same | after
  · have separated := Pairwise.pairwise_getElem faces.regulars_pairwise _ _ first.isLt second.isLt before
    rw [equal] at separated
    exact (RegularNeighborUniqueness.BranchCellBank.not_self_separated _
      separated).elim
  · exact Fin.ext same
  · have separated := Pairwise.pairwise_getElem faces.regulars_pairwise _ _ second.isLt first.isLt after
    rw [equal] at separated
    exact (RegularNeighborUniqueness.BranchCellBank.not_self_separated _
      separated).elim

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

section
variable (faces : PuncturedFaces bank)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness.BranchCellBank.PuncturedFaces

/-- Equal lower-left coordinates identify the same original regular-face list position. -/
theorem position_eq_of_lower (first second : Fin faces.regulars.length)
    (horizontal : faces.regulars[first.val].cell.box.xLower = faces.regulars[second.val].cell.box.xLower)
    (vertical : faces.regulars[first.val].cell.box.yLower = faces.regulars[second.val].cell.box.yLower) : first = second
      :=
  faces.position_eq_of_cell first second (Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell.eq_of_lower
    faces.regulars[first.val].member
    faces.regulars[second.val].member horizontal vertical)

/-- Equal left and top coordinates identify the same original regular-face list position. -/
theorem position_eq_of_left_top (first second : Fin faces.regulars.length)
    (horizontal : faces.regulars[first.val].cell.box.xLower = faces.regulars[second.val].cell.box.xLower)
    (vertical : faces.regulars[first.val].cell.box.yUpper = faces.regulars[second.val].cell.box.yUpper) : first = second
      :=
  faces.position_eq_of_cell first second (Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell.eq_of_left_top
    faces.regulars[first.val].member
    faces.regulars[second.val].member horizontal vertical)

/-- Equal right and bottom coordinates identify the same original regular-face list position. -/
theorem position_eq_of_right_bottom (first second : Fin faces.regulars.length)
    (horizontal : faces.regulars[first.val].cell.box.xUpper = faces.regulars[second.val].cell.box.xUpper)
    (vertical : faces.regulars[first.val].cell.box.yLower = faces.regulars[second.val].cell.box.yLower) : first = second
      :=
  faces.position_eq_of_cell first second (Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell.eq_of_right_bottom
    faces.regulars[first.val].member
    faces.regulars[second.val].member horizontal vertical)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness.BranchCellBank.PuncturedFaces

end
end
end
