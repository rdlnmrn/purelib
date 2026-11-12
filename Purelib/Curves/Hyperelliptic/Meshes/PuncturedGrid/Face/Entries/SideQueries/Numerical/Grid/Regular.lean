module

import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.SideQueries.Numerical.Grid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Periods.StandardPeriodGridLines
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Tactic.Ring

/-! # Selected regular fragments on the same retained numerical side row

The actual centered-parent position and original full-side parameterization
derive grid-line support. The cached classification supplies its unchanged
regular location or hole payload. Only a regular branch constructs one
fragment edge and its same-cell geometry; no paid trace, query, Point,
Entry, numerical request or face lookup is executed again.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

open Purelib
open Purelib.Polynomial.Geometry
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  (FragmentGridEdge RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates centeredEdges_point)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace RegularLocation HoleLocation LocatedCell)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Periods.StandardPeriodGridLines.Grid (ParentOnLine)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Riemann.Branches
open Purelib.Riemann.Paths

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
variable {face : RegularFace base.bank.toBranchCellBank} {models : FaceModels frames face} {point : Canonical}
variable {inside : face.cell.box.Contains point} {sourceOwner : Owner (curve.polynomial.eval point)}

namespace SideQuery.Cache.Numerical

variable {acquired : Acquisition models inside sourceOwner} {side : GridSide}
variable {onSide : face.cell.OnSide point side}
variable {lifted : LiftedFace vertices edges face acquired.entry.sheet}
variable {differential : Differential genus} {notFinish : point ≠ side.finish face.cell.box}
variable {queried : SideQuery.Cache acquired side onSide lifted differential notFinish}
variable {centers : CenterStates curve differential acquired.entry.sheet
  (prepared acquired side lifted queried.connection).2.subdivision}
variable {bounds : Bounds queried.connection.forwardSegment} {mesh : Mesh bounds}
variable {covered : ∀ edge ∈ (prepared acquired side lifted queried.connection).2.subdivision.parameterEdges,
  edge ∈ mesh.edges}
variable {count : Nat} {target : Rational} {positive : 0 < target}
variable (numerics : SideQuery.Cache.Numerical queried centers bounds mesh covered count target positive)

/-- The selected numerical parent is its literal bounded occurrence in the same supplied centered family. -/
theorem parent_mem : numerics.parent ∈ numerics.parents :=
  List.getElem_mem (queried.location.centeredIndex differential acquired.entry.sheet centers).isLt

/-- The same retained numerical parent lies on an original line of the original side grid.

Every fraction is read through its stored subdivision occurrence and the
unchanged full-side segment identity. The four side cases use the actual
cell's retained axis endpoints, including reversed top and left sides.
No alternative preparation or center family is constructed. -/
theorem parent_onLine : ParentOnLine base.bank.grid numerics.parent := by
  let intervals := FragmentGridEdge.cell_intervals face.member
  have xs := Interval.endpoints_mem base.bank.grid.vertical base.bank.grid.vertical_ordered intervals.1
  have ys := Interval.endpoints_mem base.bank.grid.horizontal base.bank.grid.horizontal_ordered intervals.2
  have onOriginalSide (fraction : Rational) : numerics.parent.edge.point fraction =
      (face.side side).segment.pointAt
        (PreparedSheetContinuation.parameterAt numerics.parent.edge.left numerics.parent.edge.request fraction) :=
    (centeredEdges_point curve differential
      (segment := queried.connection.forwardSegment)
      (within := (prepared acquired side lifted queried.connection).1)
      acquired.entry.sheet (prepared acquired side lifted queried.connection).2.subdivision centers
      numerics.parent numerics.parent_mem fraction).trans (SideQuery.segment_point side queried.connection _)
  cases side with
  | bottom =>
      have fixed (fraction : Rational) :
          (numerics.parent.edge.point fraction).im = face.cell.vertical.lower.coordinate := by
        rewrite [onOriginalSide fraction, ClearPath.ClearSegment.pointAt_eq_line,
          Geometry.Rational.Affine.line, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_im,
          Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.sub_re,
          Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
        dsimp only [GridSide.start, GridSide.finish, GridSide.kind, RectangleEdge.coordinates,
          ClearGrid.Cell.box, Data.Gaussian.Basic.re, Data.Gaussian.Basic.im]
        ring1
      refine Or.inl ⟨?_, (fixed 1).trans (fixed 0).symm⟩
      rewrite [fixed 0]
      exact Data.List.Map.mem_map_of_mem ys.1
  | right =>
      have fixed (fraction : Rational) :
          (numerics.parent.edge.point fraction).re = face.cell.horizontal.upper.coordinate := by
        rewrite [onOriginalSide fraction, ClearPath.ClearSegment.pointAt_eq_line,
          Geometry.Rational.Affine.line, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.mul_re,
          Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.sub_re,
          Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
        dsimp only [GridSide.start, GridSide.finish, GridSide.kind, RectangleEdge.coordinates,
          ClearGrid.Cell.box, Data.Gaussian.Basic.re, Data.Gaussian.Basic.im]
        ring1
      refine Or.inr ⟨?_, (fixed 1).trans (fixed 0).symm⟩
      rewrite [fixed 0]
      exact Data.List.Map.mem_map_of_mem xs.2
  | top =>
      have fixed (fraction : Rational) :
          (numerics.parent.edge.point fraction).im = face.cell.vertical.upper.coordinate := by
        rewrite [onOriginalSide fraction, ClearPath.ClearSegment.pointAt_eq_line,
          Geometry.Rational.Affine.line, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_im,
          Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.sub_re,
          Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
        dsimp only [GridSide.start, GridSide.finish, GridSide.kind, RectangleEdge.coordinates,
          ClearGrid.Cell.box, Data.Gaussian.Basic.re, Data.Gaussian.Basic.im]
        ring1
      refine Or.inl ⟨?_, (fixed 1).trans (fixed 0).symm⟩
      rewrite [fixed 0]
      exact Data.List.Map.mem_map_of_mem ys.2
  | left =>
      have fixed (fraction : Rational) :
          (numerics.parent.edge.point fraction).re = face.cell.horizontal.lower.coordinate := by
        rewrite [onOriginalSide fraction, ClearPath.ClearSegment.pointAt_eq_line,
          Geometry.Rational.Affine.line, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.mul_re,
          Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.sub_re,
          Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
        dsimp only [GridSide.start, GridSide.finish, GridSide.kind, RectangleEdge.coordinates,
          ClearGrid.Cell.box, Data.Gaussian.Basic.re, Data.Gaussian.Basic.im]
        ring1
      refine Or.inr ⟨?_, (fixed 1).trans (fixed 0).symm⟩
      rewrite [fixed 0]
      exact Data.List.Map.mem_map_of_mem xs.1

namespace GridFragments.Focus

variable {numerics} {axes : PrimitiveAxes base.bank.grid}
variable {retained : GridFragments numerics axes} (selected : Focus retained)

/-- A regular fragment retains the exact original located cell, complete edge factory and selected geometric payload.

All comparisons here are literal cache/factory readbacks and dependent
cell transports. They assert no signed root, primitive normalization or
period relation. The actual regular location remains the original input.
-/
@[expose] def RegularGeometry (location : RegularLocation base.faces.regulars selected.fragment.cell) :=
  {value : RegularPrimitiveFragment axes numerics.parent retained.partition
      (retained.partition.intervals[selected.index.val]'selected.index.isLt) //
    value.located = selected.fragment ∧
    value.face.geometry.cell = selected.fragment.cell ∧
    HEq value.source (FragmentGridEdge.build selected.fragment numerics.parent_onLine) ∧
    HEq value.face.geometry
      (FragmentGridEdge.selectedCell selected.fragment numerics.parent_onLine
        (FragmentGridEdge.build selected.fragment numerics.parent_onLine) rfl).val ∧
    HEq value.face.located location}

/-- The original classification indexes same-cell regular geometry or its unchanged hole payload. -/
@[expose] def Geometry : Type :=
  match selected.classification with
  | .regular location => RegularGeometry selected location
  | .hole location => {value : HoleLocation base.faces.holes selected.fragment.cell // value = location}

/-- Consume the actual cached classification and construct only its regular branch's finite same-cell geometry.

The fragment-edge factory runs once, then its cached line/interval payload
constructs the same incident cell. The original RegularLocation is reused
with its whole dependent transport; a hole branch returns only its exact
old HoleLocation. No source, query or Entry bank is acquired.
-/
def geometry : Geometry selected := by
  unfold Geometry
  exact match selected.classification with
  | .regular location =>
      let edgeCache := FragmentGridEdge.build selected.fragment numerics.parent_onLine
      let cell := FragmentGridEdge.selectedCell selected.fragment numerics.parent_onLine edgeCache rfl
      let value := RegularPrimitiveFragment.ofSelectedCell selected.fragment edgeCache cell location
      ⟨value,
        RegularPrimitiveFragment.ofSelectedCell_located selected.fragment edgeCache cell location,
        cell.property, HEq.rfl, HEq.rfl,
        RegularPrimitiveFragment.ofSelectedCell_location_heq selected.fragment edgeCache cell location⟩
  | .hole location => ⟨location, rfl⟩

end GridFragments.Focus
end SideQuery.Cache.Numerical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

end
