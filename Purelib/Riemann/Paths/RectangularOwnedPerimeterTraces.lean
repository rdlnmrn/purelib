module
import Purelib.Data.Gaussian.Basic

import Purelib.Integration.Path.JoinedTrace
public import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Integration.RectangularMatchedCornerReadback
import Purelib.Riemann.Readings.RectangularObservationEndpoints
public import Purelib.Riemann.Integration.RectangularExteriorCornerOwners

@[expose] public section

/-! Perimeter vertices retain their executable model owners. These traces
can be concatenated across observation pieces without discarding joins. -/
namespace Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Riemann.Integration.RectangularExteriorCornerOwners (exteriorCornerOwner)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}
  {mesh : ObservationMesh cuts box}

open Purelib.Integration in
open Purelib.Integration.Path.JoinedTrace in
/-- Retain the actual model owner of every vertex along the bottom perimeter trace.

The indexed vertex sequence preserves the original trace order and its executable owner selections. -/
def bottomOwned (traces : PerimeterTraces mesh) : Path.JoinedTrace.VertexTrace (OwnedVertex geometry) :=
  VertexTrace.ofIndexed (fun vertex => traces.bottom.leftOwner (traces.bottom.vertices.indexed vertex))

open Purelib.Data in
open Purelib.Integration.Path.JoinedTrace in
/-- The owned bottom trace has the original clipped perimeter's bottom area. -/
theorem bottomOwned_area (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    ((bottomOwned traces)).area (fun owner => values owner.column owner.row owner.point) = perimeter.bottom := by
  rw [bottomOwned, VertexTrace.ofIndexed_area]
  exact traces.bottom_area values assembly perimeter

open Purelib.Data in
open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedHorizontalSide in
/-- The first owned bottom vertex reads the actual bottom-left exterior corner. -/
theorem bottomOwned_first (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :
    let owner := ((bottomOwned traces)).first
    let corner := exteriorCornerOwner mesh false false
    values owner.column owner.row owner.point = values corner.column corner.row corner.point := by
  exact Trace.left_corner traces.bottom (above := false) values mesh.y_first false

open Purelib.Data in
open Purelib.Integration.Path.JoinedTrace in
open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedHorizontalSide in
/-- The last owned bottom vertex reads the actual bottom-right exterior corner. -/
theorem bottomOwned_last (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :
    let owner := ((bottomOwned traces)).last
    let corner := exteriorCornerOwner mesh true false
    values owner.column owner.row owner.point = values corner.column corner.row corner.point := by
  dsimp only
  rw [bottomOwned, VertexTrace.ofIndexed_last]
  exact Trace.left_corner traces.bottom (above := false) values mesh.y_first true

open Purelib.Integration in
open Purelib.Integration.Path.JoinedTrace in
/-- Retain the actual model owner of every vertex along the top perimeter trace.

The indexed vertex sequence preserves the original trace order and its executable owner selections. -/
def topOwned (traces : PerimeterTraces mesh) : Path.JoinedTrace.VertexTrace (OwnedVertex geometry) :=
  VertexTrace.ofIndexed (fun vertex => traces.top.leftOwner (traces.top.vertices.indexed vertex))

open Purelib.Data in
open Purelib.Integration.Path.JoinedTrace in
/-- The owned top trace has the original clipped perimeter's top area. -/
theorem topOwned_area (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    ((topOwned traces)).area (fun owner => values owner.column owner.row owner.point) = perimeter.top := by
  rw [topOwned, VertexTrace.ofIndexed_area]
  exact traces.top_area values assembly perimeter

open Purelib.Data in
open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedHorizontalSide in
/-- The first owned top vertex reads the actual top-left exterior corner. -/
theorem topOwned_first (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :
    let owner := ((topOwned traces)).first
    let corner := exteriorCornerOwner mesh false true
    values owner.column owner.row owner.point = values corner.column corner.row corner.point := by
  exact Trace.left_corner traces.top (above := true) values mesh.y_last false

open Purelib.Data in
open Purelib.Integration.Path.JoinedTrace in
open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedHorizontalSide in
/-- The last owned top vertex reads the actual top-right exterior corner. -/
theorem topOwned_last (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :
    let owner := ((topOwned traces)).last
    let corner := exteriorCornerOwner mesh true true
    values owner.column owner.row owner.point = values corner.column corner.row corner.point := by
  dsimp only
  rw [topOwned, VertexTrace.ofIndexed_last]
  exact Trace.left_corner traces.top (above := true) values mesh.y_last true

open Purelib.Integration in
open Purelib.Integration.Path.JoinedTrace in
/-- Retain the actual model owner of every vertex along the left perimeter trace.

The indexed vertex sequence preserves the original trace order and its executable owner selections. -/
def leftOwned (traces : PerimeterTraces mesh) : Path.JoinedTrace.VertexTrace (OwnedVertex geometry) :=
  VertexTrace.ofIndexed (fun vertex => traces.left.leftOwner (traces.left.vertices.indexed vertex))

open Purelib.Data in
open Purelib.Integration.Path.JoinedTrace in
/-- The owned left trace has the original clipped perimeter's left area. -/
theorem leftOwned_area (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    ((leftOwned traces)).area (fun owner => values owner.column owner.row owner.point) = perimeter.left := by
  rw [leftOwned, VertexTrace.ofIndexed_area]
  exact traces.left_area values assembly perimeter

open Purelib.Data in
open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedVerticalSide in
/-- The first owned left vertex reads the actual bottom-left exterior corner. -/
theorem leftOwned_first (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :
    let owner := ((leftOwned traces)).first
    let corner := exteriorCornerOwner mesh false false
    values owner.column owner.row owner.point = values corner.column corner.row corner.point := by
  exact Trace.left_corner traces.left (rightward := false) values mesh.x_first false

open Purelib.Data in
open Purelib.Integration.Path.JoinedTrace in
open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedVerticalSide in
/-- The last owned left vertex reads the actual top-left exterior corner. -/
theorem leftOwned_last (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :
    let owner := ((leftOwned traces)).last
    let corner := exteriorCornerOwner mesh false true
    values owner.column owner.row owner.point = values corner.column corner.row corner.point := by
  dsimp only
  rw [leftOwned, VertexTrace.ofIndexed_last]
  exact Trace.left_corner traces.left (rightward := false) values mesh.x_first true

open Purelib.Integration in
open Purelib.Integration.Path.JoinedTrace in
/-- Retain the actual model owner of every vertex along the right perimeter trace.

The indexed vertex sequence preserves the original trace order and its executable owner selections. -/
def rightOwned (traces : PerimeterTraces mesh) : Path.JoinedTrace.VertexTrace (OwnedVertex geometry) :=
  VertexTrace.ofIndexed (fun vertex => traces.right.leftOwner (traces.right.vertices.indexed vertex))

open Purelib.Data in
open Purelib.Integration.Path.JoinedTrace in
/-- The owned right trace has the original clipped perimeter's right area. -/
theorem rightOwned_area (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    ((rightOwned traces)).area (fun owner => values owner.column owner.row owner.point) = perimeter.right := by
  rw [rightOwned, VertexTrace.ofIndexed_area]
  exact traces.right_area values assembly perimeter

open Purelib.Data in
open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedVerticalSide in
/-- The first owned right vertex reads the actual bottom-right exterior corner. -/
theorem rightOwned_first (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :
    let owner := ((rightOwned traces)).first
    let corner := exteriorCornerOwner mesh true false
    values owner.column owner.row owner.point = values corner.column corner.row corner.point := by
  exact Trace.left_corner traces.right (rightward := true) values mesh.x_last false

open Purelib.Data in
open Purelib.Integration.Path.JoinedTrace in
open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedVerticalSide in
/-- The last owned right vertex reads the actual top-right exterior corner. -/
theorem rightOwned_last (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :
    let owner := ((rightOwned traces)).last
    let corner := exteriorCornerOwner mesh true true
    values owner.column owner.row owner.point = values corner.column corner.row corner.point := by
  dsimp only
  rw [rightOwned, VertexTrace.ofIndexed_last]
  exact Trace.left_corner traces.right (rightward := true) values mesh.x_last true

end Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
