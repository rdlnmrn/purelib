module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
public import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Readings.RectangularOuterCornerReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Geometry.Rectangle.Partition

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularOuterCornerReadings

@[expose] public section

/-! Whole-face perimeter endpoints read the original corner cache exactly,
because the outer corner determines its containing model cell. -/
section
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners (point)
open Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts (corner)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {domain : PeriodDomain models sheet}
    {differential : Differential genus}
  {stage : Nat} {mesh : ObservationMesh domain.cuts face.cell.box}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterCornerReadback

open Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts in
/-- Any actual owner reading at an outer face corner equals the retained fixed corner value because its containing model
cell is determined. -/
private theorem reading_outer_corner_eq (cached : PrimitiveData.DomainPrimitives domain differential stage)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical} (readings :
      RectangularPointReadings.PointReadings cached.anchors cached.offsets points)
    (vertex : Fin count) (corner : Fin 4) (right above : Bool)
    (equal : points vertex = FaceCorners.point face.cell.box corner)
    (cornerPoint : FaceCorners.point face.cell.box corner = PreparedRectangleCuts.corner face.cell.box right above) :
    readings.values vertex = cached.corners.values corner :=
  (readings.value_eq vertex).trans (PointReadings.outer_corner_value cached.corners domain.patch.cell_refines
    (readings.owners vertex) corner right above ((readings.point_eq vertex).trans (equal.trans cornerPoint))
      cornerPoint)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterCornerReadback

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives

/-- The actual first reading of the retained bottom perimeter trace equals its cached lower-left corner value. -/
theorem
  perimeter_bottom_first_eq
    (cached : PrimitiveData.DomainPrimitives domain differential stage) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    (traces.bottom.leftReadings cached.anchors cached.offsets).values 0 = cached.corners.values 0 := by
  apply PuncturedGrid.PerimeterCornerReadback.reading_outer_corner_eq cached _ _ 0 false
    false _ rfl
  exact RectangularCenteredPerimeter.bottom_first_point traces

/-- The actual last reading of the retained bottom perimeter trace equals its cached lower-right corner value. -/
theorem
  perimeter_bottom_last_eq
    (cached : PrimitiveData.DomainPrimitives domain differential stage) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    (traces.bottom.leftReadings cached.anchors cached.offsets).values (Fin.last traces.bottom.vertices.rest.length) =
      cached.corners.values 1 := by
  apply PuncturedGrid.PerimeterCornerReadback.reading_outer_corner_eq cached _ _ 1 true
    false _ rfl
  exact RectangularCenteredPerimeter.bottom_last_point traces

/-- The actual first reading of the retained top perimeter trace equals its cached upper-left corner value. -/
theorem
  perimeter_top_first_eq
    (cached : PrimitiveData.DomainPrimitives domain differential stage) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    (traces.top.leftReadings cached.anchors cached.offsets).values 0 = cached.corners.values 3 := by
  apply PuncturedGrid.PerimeterCornerReadback.reading_outer_corner_eq cached _ _ 3 false
    true _ rfl
  exact RectangularCenteredPerimeter.top_first_point traces

/-- The actual last reading of the retained top perimeter trace equals its cached upper-right corner value. -/
theorem
  perimeter_top_last_eq
    (cached : PrimitiveData.DomainPrimitives domain differential stage) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    (traces.top.leftReadings cached.anchors cached.offsets).values (Fin.last traces.top.vertices.rest.length) =
      cached.corners.values 2 := by
  apply PuncturedGrid.PerimeterCornerReadback.reading_outer_corner_eq cached _ _ 2 true true
    _ rfl
  exact RectangularCenteredPerimeter.top_last_point traces

/-- The actual first reading of the retained left perimeter trace equals its cached lower-left corner value. -/
theorem
  perimeter_left_first_eq
    (cached : PrimitiveData.DomainPrimitives domain differential stage) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    (traces.left.leftReadings cached.anchors cached.offsets).values 0 = cached.corners.values 0 := by
  apply PuncturedGrid.PerimeterCornerReadback.reading_outer_corner_eq cached _ _ 0 false
    false _ rfl
  exact RectangularCenteredPerimeter.left_first_point traces

/-- The actual last reading of the retained left perimeter trace equals its cached upper-left corner value. -/
theorem
  perimeter_left_last_eq
    (cached : PrimitiveData.DomainPrimitives domain differential stage) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    (traces.left.leftReadings cached.anchors cached.offsets).values (Fin.last traces.left.vertices.rest.length) =
      cached.corners.values 3 := by
  apply PuncturedGrid.PerimeterCornerReadback.reading_outer_corner_eq cached _ _ 3 false
    true _ rfl
  exact RectangularCenteredPerimeter.left_last_point traces

/-- The actual first reading of the retained right perimeter trace equals its cached lower-right corner value. -/
theorem
  perimeter_right_first_eq
    (cached : PrimitiveData.DomainPrimitives domain differential stage) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    (traces.right.leftReadings cached.anchors cached.offsets).values 0 = cached.corners.values 1 := by
  apply PuncturedGrid.PerimeterCornerReadback.reading_outer_corner_eq cached _ _ 1 true
    false _ rfl
  exact RectangularCenteredPerimeter.right_first_point traces

/-- The actual last reading of the retained right perimeter trace equals its cached upper-right corner value. -/
theorem
  perimeter_right_last_eq
    (cached : PrimitiveData.DomainPrimitives domain differential stage) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    (traces.right.leftReadings cached.anchors cached.offsets).values (Fin.last traces.right.vertices.rest.length) =
      cached.corners.values 2 := by
  apply PuncturedGrid.PerimeterCornerReadback.reading_outer_corner_eq cached _ _ 2 true true
    _ rfl
  exact RectangularCenteredPerimeter.right_last_point traces

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives

end
