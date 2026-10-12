module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace

import Purelib.Riemann.Integration.RectangularMatchedPerimeter
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularObservationAssembly
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.JoinedTrace
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Complete one-face boundary traces reuse the existing owner and joining
edge machinery. No primitive model is assigned to an adjacent branch hole. -/
namespace Purelib.Riemann.Paths.RectangularPerimeterTraces

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh
  (MatchedHorizontalSide MatchedVerticalSide)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}

/-- Match the original observation mesh with itself along its exact lower horizontal boundary.

The original bottom interval supplies the horizontal coordinate and both identical model owners. Its stored endpoint
order certifies the retained side position. -/
@[expose] def bottomSelfSide (mesh : ObservationMesh cuts box) :
    MatchedHorizontalSide mesh mesh
      (Fin.cast mesh.boundaryRows_eq 0) (Fin.cast mesh.boundaryRows_eq 0)
      mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq 0].lower :=
  MatchedHorizontalSide.build mesh mesh (Fin.cast mesh.boundaryRows_eq 0) (Fin.cast mesh.boundaryRows_eq 0)
    mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq 0)].lower rfl
    ⟨le_rfl, (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq 0)]).ordered.le⟩
    ⟨le_rfl, (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq 0)]).ordered.le⟩

/-- Match the original observation mesh with itself along its exact upper horizontal boundary.

The original top interval supplies the horizontal coordinate and both identical model owners. Its stored endpoint order
certifies the retained side position. -/
@[expose] def topSelfSide (mesh : ObservationMesh cuts box) :
    MatchedHorizontalSide mesh mesh
      (Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)) (Fin.cast mesh.boundaryRows_eq (Fin.last
        mesh.boundaryRows))
      mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)].upper :=
  MatchedHorizontalSide.build mesh mesh (Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)) (Fin.cast
    mesh.boundaryRows_eq (Fin.last mesh.boundaryRows))
    mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows))].upper rfl
    ⟨(mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows))]).ordered.le, le_rfl⟩
    ⟨(mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows))]).ordered.le, le_rfl⟩

/-- Match the original observation mesh with itself along its exact lower vertical boundary.

The original left interval supplies the vertical coordinate and both identical model owners. Its stored endpoint order
certifies the retained side position. -/
@[expose] def leftSelfSide (mesh : ObservationMesh cuts box) :
    MatchedVerticalSide mesh mesh
      (Fin.cast mesh.boundaryColumns_eq 0) (Fin.cast mesh.boundaryColumns_eq 0)
      mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq 0].lower :=
  MatchedVerticalSide.build mesh mesh (Fin.cast mesh.boundaryColumns_eq 0) (Fin.cast mesh.boundaryColumns_eq 0)
    mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq 0)].lower rfl
    ⟨le_rfl, (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq 0)]).ordered.le⟩
    ⟨le_rfl, (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq 0)]).ordered.le⟩

/-- Match the original observation mesh with itself along its exact upper vertical boundary.

The original right interval supplies the vertical coordinate and both identical model owners. Its stored endpoint order
certifies the retained side position. -/
@[expose] def rightSelfSide (mesh : ObservationMesh cuts box) :
    MatchedVerticalSide mesh mesh
      (Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)) (Fin.cast mesh.boundaryColumns_eq (Fin.last
        mesh.boundaryColumns))
      mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)].upper :=
  MatchedVerticalSide.build mesh mesh (Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)) (Fin.cast
    mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns))
    mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns))].upper rfl
    ⟨(mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns))]).ordered.le,
      le_rfl⟩
    ⟨(mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns))]).ordered.le,
      le_rfl⟩

set_option genInjectivity false in
/-- The four retained dyadic perimeter traces of one original observation mesh.

Each trace keeps its exact self-matched side owner and the original mesh depth, preserving the separate horizontal and
vertical interval indices. -/
structure PerimeterTraces (mesh : ObservationMesh cuts box) where
  /-- The retained dyadic trace of the exact original bottom self-side. -/ bottom : (bottomSelfSide mesh).Trace
    mesh.depth
  /-- The retained dyadic trace of the exact original top self-side. -/ top : (topSelfSide mesh).Trace mesh.depth
  /-- The retained dyadic trace of the exact original left self-side. -/ left : (leftSelfSide mesh).Trace mesh.depth
  /-- The retained dyadic trace of the exact original right self-side. -/ right : (rightSelfSide mesh).Trace mesh.depth

constructive_injectivity PerimeterTraces

open Purelib.Riemann.Readings in
/-- Cache the four exact self-matched perimeter traces at the original observation depth.

Each side uses its retained self-matched owner and original interval index. The four cached dyadic words reuse the same
observation depth. -/
@[expose] def PerimeterTraces.build (mesh : ObservationMesh cuts box) : PerimeterTraces mesh :=
  ⟨RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.build
      (bottomSelfSide mesh) mesh.depth,
    RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.build
      (topSelfSide mesh) mesh.depth,
    RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.build
      (leftSelfSide mesh) mesh.depth,
    RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.build
      (rightSelfSide mesh) mesh.depth⟩

namespace PerimeterTraces
variable {mesh : ObservationMesh cuts box}

open Purelib.Data.Gaussian
open Purelib.Riemann.Periods
/-- The retained bottom trace area equals the original stitched bottom perimeter.

The bottom self-matched side uses the same original mesh and owner readings. Its exact side-area certificate identifies
the corresponding cached stitched perimeter value. -/
theorem bottom_area (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → PrimitivePoint)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    CenteredBilinearPath.area (fun vertex => traces.bottom.leftValue values (traces.bottom.vertices.indexed vertex)) =
      perimeter.bottom :=
  traces.bottom.left_area_eq_bottom values assembly perimeter rfl

/-- The retained top trace area equals the original stitched top perimeter.

The top self-matched side uses the same original mesh and owner readings. Its exact side-area certificate identifies the
corresponding cached stitched perimeter value. -/
theorem top_area (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → PrimitivePoint)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    CenteredBilinearPath.area (fun vertex => traces.top.leftValue values (traces.top.vertices.indexed vertex)) =
      perimeter.top :=
  traces.top.left_area_eq_top values assembly perimeter rfl

/-- The retained left trace area equals the original stitched left perimeter.

The retained vertical self-side uses the original mesh and owner readings. Its exact side-area certificate identifies
the corresponding cached stitched perimeter value. -/
theorem left_area (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → PrimitivePoint)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    CenteredBilinearPath.area (fun vertex => traces.left.leftValue values (traces.left.vertices.indexed vertex)) =
      perimeter.left :=
  traces.left.left_area_eq_left values assembly perimeter rfl

/-- The retained right trace area equals the original stitched right perimeter.

The retained vertical self-side uses the original mesh and owner readings. Its exact side-area certificate identifies
the corresponding cached stitched perimeter value. -/
theorem right_area (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → PrimitivePoint)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    CenteredBilinearPath.area (fun vertex => traces.right.leftValue values (traces.right.vertices.indexed vertex)) =
      perimeter.right :=
  traces.right.left_area_eq_right values assembly perimeter rfl

end PerimeterTraces
end Purelib.Riemann.Paths.RectangularPerimeterTraces

end
