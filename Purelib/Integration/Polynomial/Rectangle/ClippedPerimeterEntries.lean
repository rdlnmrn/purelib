module
import Purelib.Algebra.FiniteSum.Fin

import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.Integration.RectangularStitchedPerimeter
public import Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Data.Vector.Basic

@[expose] public section

/-! Each retained rectangular perimeter is exactly the concatenation of its
cached cell sides and corners. These readbacks allow regrouping at observation
cuts without recomputing a trace or losing its joining edges. -/

namespace Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterEntries

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly (Perimeter)
open Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas (Entry)

variable {columns rows : Nat} {geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
  {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry} {box :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
  {mesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts box}
  {values : Fin (columns + 1) → Fin (rows + 1) → Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian →
    Purelib.Topology.Polygon.Stokes.PrimitivePoint}

open Purelib.Algebra in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Topology.Polygon in
/-- Matching total area and both extreme endpoints identifies a concatenated entry with the supplied whole entry. -/
private theorem concatenate_eq {count : Nat} (entries : Fin (count + 1) → StitchedSideAreas.Entry) (whole :
  StitchedSideAreas.Entry)
    (area : FiniteSum.Fin.sumFin (fun index => (entries index).area) +
      FiniteSum.Fin.sumFin (fun index : Fin count => Stokes.edgeArea (entries index.castSucc).finish (entries
        index.succ).start) = whole.area)
    (start : (entries 0).start = whole.start)
    (finish : (entries (Fin.last count)).finish = whole.finish) :
    StitchedSideAreas.Entry.concatenate entries = whole :=
  StitchedSideAreas.Entry.eq_of_fields ((StitchedSideAreas.Entry.concatenate_area entries).trans area)
    ((StitchedSideAreas.Entry.concatenate_start entries).trans start)
    ((StitchedSideAreas.Entry.concatenate_finish entries).trans finish)

section
open Purelib.Riemann.Readings
/-- Read a bottom boundary cell's exact side area and lower corner endpoints as an area entry. -/
def bottomCells (assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values) (index : Fin
  (mesh.boundaryColumns + 1)) : Entry :=
  ⟨(assembly.sides index 0).bottom, (assembly.corners index 0).lowerLeft,
    (assembly.corners index 0).lowerRight⟩

/-- Read the retained stitched bottom perimeter area and its original extreme endpoints. -/
def Perimeter.bottomEntry {assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values}
  (perimeter : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) : Entry :=
  ⟨perimeter.bottom, (assembly.corners 0 0).lowerLeft,
    (assembly.corners (Fin.last mesh.boundaryColumns) 0).lowerRight⟩

end

open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Readings in
/-- The exact bottom cell entries concatenate to the retained stitched bottom perimeter entry. -/
def BottomEntryEq {assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values} (perimeter :
  RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) : Prop :=
  StitchedSideAreas.Entry.concatenate (ClippedPerimeterEntries.bottomCells assembly) =
    ClippedPerimeterEntries.Perimeter.bottomEntry perimeter

open Purelib.Algebra in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- The original bottom cell entries concatenate to the retained bottom perimeter entry. -/
theorem Perimeter.bottomEntry_eq {assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values}
  (perimeter : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) :
    ClippedPerimeterEntries.BottomEntryEq perimeter := by
  dsimp only [ClippedPerimeterEntries.BottomEntryEq]
  refine ClippedPerimeterEntries.concatenate_eq (ClippedPerimeterEntries.bottomCells assembly)
    (ClippedPerimeterEntries.Perimeter.bottomEntry perimeter) ?_ ?_ ?_
  · have sides : FiniteSum.Fin.sumFin (fun index => (ClippedPerimeterEntries.bottomCells assembly index).area) =
        FiniteSum.Fin.sumFin (fun column => (assembly.sides column 0).bottom) :=
      FiniteSum.Fin.sumFin_congr (fun _ => rfl)
    have joins : FiniteSum.Fin.sumFin (fun index : Fin mesh.boundaryColumns =>
        Stokes.edgeArea (ClippedPerimeterEntries.bottomCells assembly index.castSucc).finish
          (ClippedPerimeterEntries.bottomCells assembly index.succ).start) =
        FiniteSum.Fin.sumFin (fun column : Fin mesh.boundaryColumns =>
          Stokes.edgeArea (assembly.corners column.castSucc 0).lowerRight
            (assembly.corners column.succ 0).lowerLeft) :=
      FiniteSum.Fin.sumFin_congr (fun _ => rfl)
    exact (congrArg₂ (· + ·) sides joins).trans perimeter.bottom_eq.symm
  · rfl
  · rfl

section
open Purelib.Riemann.Readings
/-- Read a top boundary cell's exact side area and upper corner endpoints as an area entry. -/
def topCells (assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values) (index : Fin
  (mesh.boundaryColumns + 1)) : Entry :=
  ⟨(assembly.sides index (Fin.last mesh.boundaryRows)).top, (assembly.corners index (Fin.last
    mesh.boundaryRows)).upperLeft,
    (assembly.corners index (Fin.last mesh.boundaryRows)).upperRight⟩

/-- Read the retained stitched top perimeter area and its original extreme endpoints. -/
def Perimeter.topEntry {assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values}
  (perimeter : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) : Entry :=
  ⟨perimeter.top, (assembly.corners 0 (Fin.last mesh.boundaryRows)).upperLeft,
    (assembly.corners (Fin.last mesh.boundaryColumns) (Fin.last mesh.boundaryRows)).upperRight⟩

end

open Purelib.Algebra in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- The original top cell entries concatenate to the retained top perimeter entry. -/
theorem Perimeter.topEntry_eq {assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values}
  (perimeter : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) :
    StitchedSideAreas.Entry.concatenate (ClippedPerimeterEntries.topCells assembly) =
      ClippedPerimeterEntries.Perimeter.topEntry perimeter := by
  refine ClippedPerimeterEntries.concatenate_eq (ClippedPerimeterEntries.topCells assembly)
    (ClippedPerimeterEntries.Perimeter.topEntry perimeter) ?_ ?_ ?_
  · have sides : FiniteSum.Fin.sumFin (fun index => (ClippedPerimeterEntries.topCells assembly index).area) =
        FiniteSum.Fin.sumFin (fun column => (assembly.sides column (Fin.last mesh.boundaryRows)).top) :=
      FiniteSum.Fin.sumFin_congr (fun _ => rfl)
    have joins : FiniteSum.Fin.sumFin (fun index : Fin mesh.boundaryColumns =>
        Stokes.edgeArea (ClippedPerimeterEntries.topCells assembly index.castSucc).finish
          (ClippedPerimeterEntries.topCells assembly index.succ).start) =
        FiniteSum.Fin.sumFin (fun column : Fin mesh.boundaryColumns =>
          Stokes.edgeArea (assembly.corners column.castSucc (Fin.last mesh.boundaryRows)).upperRight
            (assembly.corners column.succ (Fin.last mesh.boundaryRows)).upperLeft) :=
      FiniteSum.Fin.sumFin_congr (fun _ => rfl)
    exact (congrArg₂ (· + ·) sides joins).trans perimeter.top_eq.symm
  · rfl
  · rfl

section
open Purelib.Riemann.Readings
/-- Read a left boundary cell's exact side area and left corner endpoints as an area entry. -/
def leftCells (assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values) (index : Fin
  (mesh.boundaryRows + 1)) : Entry :=
  ⟨(assembly.sides 0 index).left, (assembly.corners 0 index).lowerLeft,
    (assembly.corners 0 index).upperLeft⟩

/-- Read the retained stitched left perimeter area and its original extreme endpoints. -/
def Perimeter.leftEntry {assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values}
  (perimeter : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) : Entry :=
  ⟨perimeter.left, (assembly.corners 0 0).lowerLeft,
    (assembly.corners 0 (Fin.last mesh.boundaryRows)).upperLeft⟩

end

open Purelib.Algebra in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- The original left cell entries concatenate to the retained left perimeter entry. -/
theorem Perimeter.leftEntry_eq {assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values}
  (perimeter : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) :
    StitchedSideAreas.Entry.concatenate (ClippedPerimeterEntries.leftCells assembly) =
      ClippedPerimeterEntries.Perimeter.leftEntry perimeter := by
  refine ClippedPerimeterEntries.concatenate_eq (ClippedPerimeterEntries.leftCells assembly)
    (ClippedPerimeterEntries.Perimeter.leftEntry perimeter) ?_ ?_ ?_
  · have sides : FiniteSum.Fin.sumFin (fun index => (ClippedPerimeterEntries.leftCells assembly index).area) =
        FiniteSum.Fin.sumFin (fun row => (assembly.sides 0 row).left) :=
      FiniteSum.Fin.sumFin_congr (fun _ => rfl)
    have joins : FiniteSum.Fin.sumFin (fun index : Fin mesh.boundaryRows =>
        Stokes.edgeArea (ClippedPerimeterEntries.leftCells assembly index.castSucc).finish
          (ClippedPerimeterEntries.leftCells assembly index.succ).start) =
        FiniteSum.Fin.sumFin (fun row : Fin mesh.boundaryRows =>
          Stokes.edgeArea (assembly.corners 0 row.castSucc).upperLeft
            (assembly.corners 0 row.succ).lowerLeft) :=
      FiniteSum.Fin.sumFin_congr (fun _ => rfl)
    exact (congrArg₂ (· + ·) sides joins).trans perimeter.left_eq.symm
  · rfl
  · rfl

section
open Purelib.Riemann.Readings
/-- Read a right boundary cell's exact side area and right corner endpoints as an area entry. -/
def rightCells (assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values) (index : Fin
  (mesh.boundaryRows + 1)) : Entry :=
  ⟨(assembly.sides (Fin.last mesh.boundaryColumns) index).right, (assembly.corners (Fin.last mesh.boundaryColumns)
    index).lowerRight,
    (assembly.corners (Fin.last mesh.boundaryColumns) index).upperRight⟩

/-- Read the retained stitched right perimeter area and its original extreme endpoints. -/
def Perimeter.rightEntry {assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values}
  (perimeter : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) : Entry :=
  ⟨perimeter.right, (assembly.corners (Fin.last mesh.boundaryColumns) 0).lowerRight,
    (assembly.corners (Fin.last mesh.boundaryColumns) (Fin.last mesh.boundaryRows)).upperRight⟩

end

open Purelib.Algebra in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- The original right cell entries concatenate to the retained right perimeter entry. -/
theorem Perimeter.rightEntry_eq {assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values}
  (perimeter : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) :
    StitchedSideAreas.Entry.concatenate (ClippedPerimeterEntries.rightCells assembly) =
      ClippedPerimeterEntries.Perimeter.rightEntry perimeter := by
  refine ClippedPerimeterEntries.concatenate_eq (ClippedPerimeterEntries.rightCells assembly)
    (ClippedPerimeterEntries.Perimeter.rightEntry perimeter) ?_ ?_ ?_
  · have sides : FiniteSum.Fin.sumFin (fun index => (ClippedPerimeterEntries.rightCells assembly index).area) =
        FiniteSum.Fin.sumFin (fun row => (assembly.sides (Fin.last mesh.boundaryColumns) row).right) :=
      FiniteSum.Fin.sumFin_congr (fun _ => rfl)
    have joins : FiniteSum.Fin.sumFin (fun index : Fin mesh.boundaryRows =>
        Stokes.edgeArea (ClippedPerimeterEntries.rightCells assembly index.castSucc).finish
          (ClippedPerimeterEntries.rightCells assembly index.succ).start) =
        FiniteSum.Fin.sumFin (fun row : Fin mesh.boundaryRows =>
          Stokes.edgeArea (assembly.corners (Fin.last mesh.boundaryColumns) row.castSucc).upperRight
            (assembly.corners (Fin.last mesh.boundaryColumns) row.succ).lowerRight) :=
      FiniteSum.Fin.sumFin_congr (fun _ => rfl)
    exact (congrArg₂ (· + ·) sides joins).trans perimeter.right_eq.symm
  · rfl
  · rfl

end Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterEntries
