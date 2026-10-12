module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic

public import Purelib.Riemann.Paths.RectangularPerimeterTraces
public import Purelib.Riemann.Paths.RectangularMatchedChords
import Purelib.Riemann.Readings.RectangularObservationEndpoints
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Integration.RectangularMatchedSideEndpoints

public section

/-! Cached centered samples of all four actual perimeter traces. -/
namespace Purelib.Riemann.Integration.RectangularCenteredPerimeter
open Purelib.Riemann.Paths
open Purelib.Data.Gaussian
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Paths.RectangularPerimeterTraces
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}
  {mesh : ObservationMesh cuts box}

set_option genInjectivity false in
/-- Four cached centered bilinear samples on the exact original perimeter traces.

Each sample retains its own original side's ordered primitive reading word, keeping the centered area and endpoint chord
as separate readbacks. -/
structure Centered (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → PrimitivePoint) where
  /-- The centered sample of the exact original bottom-trace reading word. -/ bottom : Sample (fun vertex =>
    traces.bottom.leftValue values (traces.bottom.vertices.indexed vertex))
  /-- The centered sample of the exact original top-trace reading word. -/ top : Sample (fun vertex =>
    traces.top.leftValue values (traces.top.vertices.indexed vertex))
  /-- The centered sample of the exact original left-trace reading word. -/ left : Sample (fun vertex =>
    traces.left.leftValue values (traces.left.vertices.indexed vertex))
  /-- The centered sample of the exact original right-trace reading word. -/ right : Sample (fun vertex =>
    traces.right.leftValue values (traces.right.vertices.indexed vertex))

constructive_injectivity Centered

namespace Centered
variable {traces : PerimeterTraces mesh}
  {values : Fin (columns + 1) → Fin (rows + 1) → Purelib.Data.Gaussian.Basic.Canonical → PrimitivePoint}

/-- Cache the centered bilinear samples for all four retained original perimeter traces. -/
@[expose] def build (traces : PerimeterTraces mesh)
    (values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → PrimitivePoint) : Centered traces values :=
  ⟨Sample.build (fun vertex => traces.bottom.leftValue values (traces.bottom.vertices.indexed vertex)),
    Sample.build (fun vertex => traces.top.leftValue values (traces.top.vertices.indexed vertex)),
    Sample.build (fun vertex => traces.left.leftValue values (traces.left.vertices.indexed vertex)),
    Sample.build (fun vertex => traces.right.leftValue values (traces.right.vertices.indexed vertex))⟩

/-- The retained bottom perimeter splits into its original centered area and endpoint term. -/
theorem bottom_eq (samples : Centered traces values)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    perimeter.bottom = samples.bottom.centeredArea + samples.bottom.endpoint :=
  (traces.bottom_area values assembly perimeter).symm.trans
    (samples.bottom.originalArea_eq.symm.trans samples.bottom.decomposition)

/-- The retained top perimeter splits into its original centered area and endpoint term. -/
theorem top_eq (samples : Centered traces values)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    perimeter.top = samples.top.centeredArea + samples.top.endpoint :=
  (traces.top_area values assembly perimeter).symm.trans
    (samples.top.originalArea_eq.symm.trans samples.top.decomposition)

/-- The retained left perimeter splits into its original centered area and endpoint term. -/
theorem left_eq (samples : Centered traces values)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    perimeter.left = samples.left.centeredArea + samples.left.endpoint :=
  (traces.left_area values assembly perimeter).symm.trans
    (samples.left.originalArea_eq.symm.trans samples.left.decomposition)

/-- The retained right perimeter splits into its original centered area and endpoint term. -/
theorem right_eq (samples : Centered traces values)
    (assembly : ClippedAssembly mesh values) (perimeter : assembly.Perimeter) :
    perimeter.right = samples.right.centeredArea + samples.right.endpoint :=
  (traces.right_area values assembly perimeter).symm.trans
    (samples.right.originalArea_eq.symm.trans samples.right.decomposition)

/-- The retained bottom endpoint term equals its original self-side chord. -/
theorem bottom_endpoint (samples : Centered traces values) :
  samples.bottom.endpoint = (RectangularPerimeterTraces.bottomSelfSide mesh).leftChord values :=
  traces.bottom.left_endpoint_eq_chord values samples.bottom (fun _ => rfl)

/-- The retained top endpoint term equals its original self-side chord. -/
theorem top_endpoint (samples : Centered traces values) :
  samples.top.endpoint = (RectangularPerimeterTraces.topSelfSide mesh).leftChord values :=
  traces.top.left_endpoint_eq_chord values samples.top (fun _ => rfl)

/-- The retained left endpoint term equals its original self-side chord. -/
theorem left_endpoint (samples : Centered traces values) :
  samples.left.endpoint = (RectangularPerimeterTraces.leftSelfSide mesh).leftChord values :=
  traces.left.left_endpoint_eq_chord values samples.left (fun _ => rfl)

/-- The retained right endpoint term equals its original self-side chord. -/
theorem right_endpoint (samples : Centered traces values) :
  samples.right.endpoint = (RectangularPerimeterTraces.rightSelfSide mesh).leftChord values :=
  traces.right.left_endpoint_eq_chord values samples.right (fun _ => rfl)

end Centered

/-- The retained bottom trace starts at the original box's lower-left corner. -/
theorem bottom_first_point (traces : PerimeterTraces mesh) :
    traces.bottom.point (traces.bottom.vertices.indexed 0) = ⟨box.xLower, box.yLower⟩ := by
  rw [traces.bottom.first_point, (RectangularPerimeterTraces.bottomSelfSide mesh).first_eq,
    mesh.x_first, mesh.y_first]

/-- The retained bottom trace finishes at the original box's lower-right corner. -/
theorem bottom_last_point (traces : PerimeterTraces mesh) :
    traces.bottom.point (traces.bottom.vertices.indexed (Fin.last traces.bottom.vertices.rest.length)) = ⟨box.xUpper,
      box.yLower⟩ := by
  rw [traces.bottom.last_point, (RectangularPerimeterTraces.bottomSelfSide mesh).last_eq,
    mesh.x_last, mesh.y_first]

/-- The retained top trace starts at the original box's upper-left corner. -/
theorem top_first_point (traces : PerimeterTraces mesh) :
    traces.top.point (traces.top.vertices.indexed 0) = ⟨box.xLower, box.yUpper⟩ := by
  rw [traces.top.first_point, (RectangularPerimeterTraces.topSelfSide mesh).first_eq,
    mesh.x_first, mesh.y_last]

/-- The retained top trace finishes at the original box's upper-right corner. -/
theorem top_last_point (traces : PerimeterTraces mesh) :
    traces.top.point (traces.top.vertices.indexed (Fin.last traces.top.vertices.rest.length)) = ⟨box.xUpper, box.yUpper⟩
      := by
  rw [traces.top.last_point, (RectangularPerimeterTraces.topSelfSide mesh).last_eq,
    mesh.x_last, mesh.y_last]

/-- The retained left trace starts at the original box's lower-left corner. -/
theorem left_first_point (traces : PerimeterTraces mesh) :
    traces.left.point (traces.left.vertices.indexed 0) = ⟨box.xLower, box.yLower⟩ := by
  rw [traces.left.first_point, (RectangularPerimeterTraces.leftSelfSide mesh).first_eq,
    mesh.x_first, mesh.y_first]

/-- The retained left trace finishes at the original box's upper-left corner. -/
theorem left_last_point (traces : PerimeterTraces mesh) :
    traces.left.point (traces.left.vertices.indexed (Fin.last traces.left.vertices.rest.length)) = ⟨box.xLower,
      box.yUpper⟩ := by
  rw [traces.left.last_point, (RectangularPerimeterTraces.leftSelfSide mesh).last_eq,
    mesh.x_first, mesh.y_last]

/-- The retained right trace starts at the original box's lower-right corner. -/
theorem right_first_point (traces : PerimeterTraces mesh) :
    traces.right.point (traces.right.vertices.indexed 0) = ⟨box.xUpper, box.yLower⟩ := by
  rw [traces.right.first_point, (RectangularPerimeterTraces.rightSelfSide mesh).first_eq,
    mesh.x_last, mesh.y_first]

/-- The retained right trace finishes at the original box's upper-right corner. -/
theorem right_last_point (traces : PerimeterTraces mesh) :
    traces.right.point (traces.right.vertices.indexed (Fin.last traces.right.vertices.rest.length)) = ⟨box.xUpper,
      box.yUpper⟩ := by
  rw [traces.right.last_point, (RectangularPerimeterTraces.rightSelfSide mesh).last_eq,
    mesh.x_last, mesh.y_last]

end Purelib.Riemann.Integration.RectangularCenteredPerimeter

end
