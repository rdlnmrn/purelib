module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Data.Vector.Dependent
public import Purelib.Polynomial.Geometry.Grid.FramedAxisNeighbors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
public import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Data.List

open Purelib.Data.Vector

open Purelib.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.CellBoundary

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.FramedAxisNeighbors

open Purelib.Polynomial.Geometry.Grid.FramedClearGrid

open Purelib.Riemann.Meshes

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

/-! Every regular side has a retained regular/hole neighbor or an exact
ambient-boundary certificate. -/
section
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace BranchHole)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval VerticalLine HorizontalLine)

namespace Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide

/-- The original directed face side and neighboring box share exactly their transverse extents and boundary coordinate.
-/
@[expose] def Matches : GridLiftedDualSteps.GridSide →
  Rational.Box → Rational.Box → Prop
  | .bottom, first, next => first.xLower = next.xLower ∧ first.xUpper = next.xUpper ∧ first.yLower = next.yUpper
  | .top, first, next => first.xLower = next.xLower ∧ first.xUpper = next.xUpper ∧ first.yUpper = next.yLower
  | .left, first, next => first.yLower = next.yLower ∧ first.yUpper = next.yUpper ∧ first.xLower = next.xUpper
  | .right, first, next => first.yLower = next.yLower ∧ first.yUpper = next.yUpper ∧ first.xUpper = next.xLower

/-- The original directed face side lies exactly on the corresponding ambient boundary. -/
@[expose] def Exterior : GridLiftedDualSteps.GridSide →
  Rational.Box → Rational.Box → Prop
  | .bottom, face, ambient => face.yLower = ambient.yLower
  | .top, face, ambient => face.yUpper = ambient.yUpper
  | .left, face, ambient => face.xLower = ambient.xLower
  | .right, face, ambient => face.xUpper = ambient.xUpper

end Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide

section
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

set_option genInjectivity false in
/-- The original regular-face side has a retained adjacent cell location or an exact ambient-boundary certificate. -/
inductive SideNeighbor (faces :
  PuncturedGridFaces.PuncturedFaces bank) (face : PuncturedGridFaces.RegularFace bank) (side :
  GridLiftedDualSteps.GridSide) where
  /-- Retain the actual adjacent grid cell, exact side matching and original regular/hole location. -/ | neighbor (cell
    : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) (member : cell ∈ bank.grid.cells)
      (matching : side.Matches face.cell.box cell.box) (location : faces.Location cell)
  /-- Retain equality of the original face side with its exact ambient boundary. -/ | exterior (equal : side.Exterior
    face.cell.box (Cuts.Ambient curve))

constructive_injectivity Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

open Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces (SideNeighbor)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors.BranchCellBank.PuncturedFaces

/-- Pairing retained horizontal and vertical grid intervals gives an actual cell of the original grid. -/
public theorem cell_member (horizontal : ClearGrid.Interval (VerticalLine.coordinate (polynomial := curve.polynomial)
  (ambient := Cuts.Ambient curve)))
    (vertical : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := curve.polynomial) (ambient := Cuts.Ambient
      curve)))
    (hMember : horizontal ∈ bank.grid.xIntervals) (vMember : vertical ∈ bank.grid.yIntervals) :
    (⟨horizontal, vertical⟩ : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) ∈ bank.grid.cells :=
  Flatten.mem_flatMap.mpr ⟨horizontal, hMember, Map.mem_map.mpr ⟨vertical, vMember, rfl⟩⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors.BranchCellBank.PuncturedFaces

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor

/-- Inspect the original framed grid's adjacent axis interval and retain its exact cell location or ambient-boundary
equality. -/
@[expose] def build (faces :
  PuncturedGridFaces.PuncturedFaces bank) (frame : Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame bank.grid)
    (face : PuncturedGridFaces.RegularFace bank) : (side : GridLiftedDualSteps.GridSide) →
      Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side
  | .bottom =>
      match Predecessor.build face.cell.vertical (Cell.intervals_mem face.cell face.member).2
        (Cuts.Ambient curve).yLower frame.yLower (fun line _ => line.inside.1) with
      | .previous found =>
          let cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) := ⟨face.cell.horizontal, found.interval⟩
          let member :=
            RegularSideNeighbors.BranchCellBank.PuncturedFaces.cell_member
            face.cell.horizontal found.interval (Cell.intervals_mem face.cell face.member).1 found.member
          .neighbor cell member ⟨rfl, rfl, found.endpoint_eq.symm⟩ (faces.locate cell member)
      | .exterior equal => .exterior equal
  | .top =>
      match Successor.build face.cell.vertical (Cell.intervals_mem face.cell face.member).2
        (Cuts.Ambient curve).yUpper frame.yUpper (fun line _ => line.inside.2) with
      | .next found =>
          let cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) := ⟨face.cell.horizontal, found.interval⟩
          let member :=
            RegularSideNeighbors.BranchCellBank.PuncturedFaces.cell_member
            face.cell.horizontal found.interval (Cell.intervals_mem face.cell face.member).1 found.member
          .neighbor cell member ⟨rfl, rfl, found.endpoint_eq.symm⟩ (faces.locate cell member)
      | .exterior equal => .exterior equal
  | .left =>
      match Predecessor.build face.cell.horizontal (Cell.intervals_mem face.cell face.member).1
        (Cuts.Ambient curve).xLower frame.xLower (fun line _ => line.inside.1) with
      | .previous found =>
          let cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) := ⟨found.interval, face.cell.vertical⟩
          let member :=
            RegularSideNeighbors.BranchCellBank.PuncturedFaces.cell_member
            found.interval face.cell.vertical found.member (Cell.intervals_mem face.cell face.member).2
          .neighbor cell member ⟨rfl, rfl, found.endpoint_eq.symm⟩ (faces.locate cell member)
      | .exterior equal => .exterior equal
  | .right =>
      match Successor.build face.cell.horizontal (Cell.intervals_mem face.cell face.member).1
        (Cuts.Ambient curve).xUpper frame.xUpper (fun line _ => line.inside.2) with
      | .next found =>
          let cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) := ⟨found.interval, face.cell.vertical⟩
          let member :=
            RegularSideNeighbors.BranchCellBank.PuncturedFaces.cell_member
            found.interval face.cell.vertical found.member (Cell.intervals_mem face.cell face.member).2
          .neighbor cell member ⟨rfl, rfl, found.endpoint_eq.symm⟩ (faces.locate cell member)
      | .exterior equal => .exterior equal

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

set_option genInjectivity false in
/-- The four retained neighboring-cell or ambient-boundary certificates of one original regular face. -/
structure FaceNeighbors (faces :
  PuncturedGridFaces.PuncturedFaces bank) (face : PuncturedGridFaces.RegularFace bank) where
  /-- The retained neighbor or ambient boundary at the original lower face side. -/ bottom :
    SideNeighbor faces face .bottom
  /-- The retained neighbor or ambient boundary at the original right face side. -/ right :
    SideNeighbor faces face .right
  /-- The retained neighbor or ambient boundary at the original upper face side. -/ top :
    SideNeighbor faces face .top
  /-- The retained neighbor or ambient boundary at the original left face side. -/ left :
    SideNeighbor faces face .left

constructive_injectivity Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.FaceNeighbors

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

open Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces (FaceNeighbors)

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.FaceNeighbors

/-- Construct and cache the four side certificates of the original regular face. -/
@[expose] def build (faces :
  PuncturedGridFaces.PuncturedFaces bank) (frame : Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame bank.grid)
    (face : PuncturedGridFaces.RegularFace bank) : PuncturedFaces.FaceNeighbors faces
      face :=
  ⟨SideNeighbor.build faces frame face .bottom, PuncturedFaces.SideNeighbor.build
    faces frame face .right,
    Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor.build faces frame face .top,
      Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor.build faces frame face .left⟩

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.FaceNeighbors

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

set_option genInjectivity false in
/-- A cached dependent vector of all four side certificates for every original regular face. -/
structure NeighborBank (faces :
  PuncturedGridFaces.PuncturedFaces bank) where
  /-- The retained four-side neighbor certificates indexed by the exact original regular-face list. -/ entries :
    Data.Vector.DependentVector (fun position : Fin faces.regulars.length =>
    FaceNeighbors faces faces.regulars[position.val])

constructive_injectivity Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

open Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces (NeighborBank)

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank

/-- Cache the four-side neighbor certificates in original regular-face order. -/
@[expose] def build (faces :
  PuncturedGridFaces.PuncturedFaces bank) (frame : Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame bank.grid) :
  Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces :=
  ⟨DependentVector.ofFn (fun position => PuncturedFaces.FaceNeighbors.build faces
    frame faces.regulars[position.val])⟩

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank

end
end
