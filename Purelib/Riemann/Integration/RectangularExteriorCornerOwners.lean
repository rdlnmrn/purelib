module
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Readings.RectangularObservationEndpoints

public section

/-! The four exterior corner readings retain their original clipped model
owners. Their containment certificates refer to the exact physical box
corners, also when another partition cut meets a model-grid boundary. -/

namespace Purelib.Riemann.Integration.RectangularExteriorCornerOwners

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}

section
open Purelib.Geometry
/-- Each selected corner of a rational box lies in that box. -/
theorem corner_contains (box : Box) (right above : Bool) :
    box.Contains (Rectangle.Partition.PreparedRectangleCuts.corner box right above) := by
  cases right <;> cases above
  · exact ⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩
  · exact ⟨le_rfl, box.x_valid, box.y_valid, le_rfl⟩
  · exact ⟨box.x_valid, le_rfl, le_rfl, box.y_valid⟩
  · exact ⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩

/-- Retain the original clipped model owner at a specified exterior box corner.

The construction uses the boundary interval's actual owner and transports its containment proof to the physical corner.
-/
@[expose] def exteriorCornerOwner (mesh : ObservationMesh cuts box) (right above : Bool) : OwnedVertex geometry :=
  let column := Fin.cast mesh.boundaryColumns_eq (if right then Fin.last mesh.boundaryColumns else 0)
  let row := Fin.cast mesh.boundaryRows_eq (if above then Fin.last mesh.boundaryRows else 0)
  let owner := mesh.ownerAt column row
  let small := Rectangle.Partition.PreparedRectangleCuts.intervalBox
    (mesh.partition.x.intervals[column.val]'column.isLt) (mesh.partition.y.intervals[row.val]'row.isLt)
  ⟨owner.column, owner.row, Rectangle.Partition.PreparedRectangleCuts.corner small right above,
    owner.refines.contains (corner_contains small right above)⟩

end

open Purelib.Data in
open Purelib.Geometry in
/-- The exterior owner's coordinate equals the specified physical box corner.

All four Boolean choices retain the first or last boundary interval at the
same physical endpoint, including coincident partition and model cuts. -/
theorem exteriorCornerOwner_point (mesh : ObservationMesh cuts box) (right above : Bool) :
    (exteriorCornerOwner mesh right above).point = Rectangle.Partition.PreparedRectangleCuts.corner box right above :=
      by
  cases right <;> cases above
  · change Gaussian.Basic.Canonical.mk _ _ = Gaussian.Basic.Canonical.mk _ _
    exact Gaussian.Basic.ext mesh.x_first mesh.y_first
  · change Gaussian.Basic.Canonical.mk _ _ = Gaussian.Basic.Canonical.mk _ _
    exact Gaussian.Basic.ext mesh.x_first mesh.y_last
  · change Gaussian.Basic.Canonical.mk _ _ = Gaussian.Basic.Canonical.mk _ _
    exact Gaussian.Basic.ext mesh.x_last mesh.y_first
  · change Gaussian.Basic.Canonical.mk _ _ = Gaussian.Basic.Canonical.mk _ _
    exact Gaussian.Basic.ext mesh.x_last mesh.y_last

open Purelib.Data in
/-- Read all four exterior clipped corner values through their original model owners.

The equalities use the actual boundary indices and preserve ownership when cuts meet model-grid boundaries. -/
theorem ClippedAssembly.exterior_corners {mesh : ObservationMesh cuts box}
    {values : Fin (columns + 1) → Fin (rows + 1) → Gaussian.Basic.Canonical → PrimitivePoint} (assembly :
      ClippedAssembly mesh values) :
    let value := fun right above =>
      let owner := exteriorCornerOwner mesh right above
      values owner.column owner.row owner.point
    (assembly.corners 0 0).lowerLeft = value false false ∧
    (assembly.corners (Fin.last mesh.boundaryColumns) 0).lowerRight = value true false ∧
    (assembly.corners 0 (Fin.last mesh.boundaryRows)).upperLeft = value false true ∧
    (assembly.corners (Fin.last mesh.boundaryColumns) (Fin.last mesh.boundaryRows)).upperRight = value true true := by
  simp only [assembly.corners_eq]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Purelib.Riemann.Integration.RectangularExteriorCornerOwners
