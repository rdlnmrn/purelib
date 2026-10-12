module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! The actual common-cut request constructs paired sides from its retained
meshes. No new partition or model owner is acquired for cross-face gluing. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ObservationSides

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (Meshes.PuncturedGridFaces.RegularFace
      bank)}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}

variable (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
  target)

/-- Construct a horizontal side match directly from the original common-cut request and supplied retained row bounds.

The equality of original horizontal endpoints gives the shared partition, preserving both sheets and actual source
meshes. -/
def matchedHorizontalSide (firstSheet lastSheet : Fin 2) (first last : Fin faces.length)
    (lowerEq : faces[first.val].cell.box.xLower = faces[last.val].cell.box.xLower)
    (upperEq : faces[first.val].cell.box.xUpper = faces[last.val].cell.box.xUpper)
    (firstRow : Fin ((request.entries.get firstSheet).meshes.entries.get first).partition.y.intervals.length)
    (lastRow : Fin ((request.entries.get lastSheet).meshes.entries.get last).partition.y.intervals.length)
    (height : Fraction.Rational)
    (firstInside : ((request.entries.get firstSheet).meshes.entries.get first).partition.y.intervals[firstRow].lower ≤
      height ∧
      height ≤ ((request.entries.get firstSheet).meshes.entries.get first).partition.y.intervals[firstRow].upper)
    (lastInside : ((request.entries.get lastSheet).meshes.entries.get last).partition.y.intervals[lastRow].lower ≤
      height ∧
      height ≤ ((request.entries.get lastSheet).meshes.entries.get last).partition.y.intervals[lastRow].upper) :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide ((request.entries.get
      firstSheet).meshes.entries.get first)
      ((request.entries.get lastSheet).meshes.entries.get last) firstRow lastRow height :=
  Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.build _ _ firstRow lastRow height
    (request.shared_x_mesh firstSheet lastSheet first last lowerEq upperEq).1 firstInside lastInside

/-- Construct a vertical side match directly from the original common-cut request and supplied retained column bounds.

The equality of original vertical endpoints gives the shared partition, preserving both sheets and actual source meshes.
-/
def matchedVerticalSide (firstSheet lastSheet : Fin 2) (first last : Fin faces.length)
    (lowerEq : faces[first.val].cell.box.yLower = faces[last.val].cell.box.yLower)
    (upperEq : faces[first.val].cell.box.yUpper = faces[last.val].cell.box.yUpper)
    (firstColumn : Fin ((request.entries.get firstSheet).meshes.entries.get first).partition.x.intervals.length)
    (lastColumn : Fin ((request.entries.get lastSheet).meshes.entries.get last).partition.x.intervals.length)
    (horizontal : Fraction.Rational)
    (firstInside : ((request.entries.get firstSheet).meshes.entries.get first).partition.x.intervals[firstColumn].lower
      ≤ horizontal ∧
      horizontal ≤ ((request.entries.get firstSheet).meshes.entries.get first).partition.x.intervals[firstColumn].upper)
    (lastInside : ((request.entries.get lastSheet).meshes.entries.get last).partition.x.intervals[lastColumn].lower ≤
      horizontal ∧
      horizontal ≤ ((request.entries.get lastSheet).meshes.entries.get last).partition.x.intervals[lastColumn].upper) :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide ((request.entries.get
      firstSheet).meshes.entries.get first)
      ((request.entries.get lastSheet).meshes.entries.get last) firstColumn lastColumn horizontal :=
  Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.build _ _ firstColumn lastColumn
    horizontal
    (request.shared_y_mesh firstSheet lastSheet first last lowerEq upperEq).1 firstInside lastInside

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ObservationSides
