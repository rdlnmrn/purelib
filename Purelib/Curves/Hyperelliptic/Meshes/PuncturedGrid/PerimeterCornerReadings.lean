module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
public import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerReadingBounds
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerReadingBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

@[expose] public section

/-! Perimeter endpoint owners compare to the fixed period corners, with no
factor depending on the number of trace subdivisions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterCornerReadings
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {domain : PeriodDomain models sheet}
    {differential : Differential genus}
  {bounds : Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
    (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator differential)}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {mesh : ObservationMesh domain.cuts face.cell.box}

/-- The retained bottom perimeter's first owner reading differs from the fixed lower-left corner value by at most four
times the paid global overlap bound. -/
theorem perimeter_bottom_first_bound
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    Data.Gaussian.Norm.Basic.normSq ((traces.bottom.leftReadings cached.anchors cached.offsets).values 0 -
      cached.corners.values 0) ≤ 4 * request.globalBound := by
  apply DomainPrimitives.reading_corner_bound request cached
  change Trace.point traces.bottom (traces.bottom.vertices.indexed 0) =
    FaceCorners.point face.cell.box 0
  exact RectangularCenteredPerimeter.bottom_first_point traces

/-- The retained bottom perimeter's last owner reading differs from the fixed lower-right corner value by at most four
times the paid global overlap bound. -/
theorem perimeter_bottom_last_bound
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    Data.Gaussian.Norm.Basic.normSq ((traces.bottom.leftReadings cached.anchors cached.offsets).values
      (Fin.last traces.bottom.vertices.rest.length) -
      cached.corners.values 1) ≤ 4 * request.globalBound := by
  apply DomainPrimitives.reading_corner_bound request cached
  change Trace.point traces.bottom (traces.bottom.vertices.indexed (Fin.last traces.bottom.vertices.rest.length)) =
    FaceCorners.point face.cell.box 1
  exact RectangularCenteredPerimeter.bottom_last_point traces

/-- The retained top perimeter's first owner reading differs from the fixed upper-left corner value by at most four
times the paid global overlap bound. -/
theorem perimeter_top_first_bound
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    Data.Gaussian.Norm.Basic.normSq ((traces.top.leftReadings cached.anchors cached.offsets).values 0 -
      cached.corners.values 3) ≤ 4 * request.globalBound := by
  apply DomainPrimitives.reading_corner_bound request cached
  change Trace.point traces.top (traces.top.vertices.indexed 0) =
    FaceCorners.point face.cell.box 3
  exact RectangularCenteredPerimeter.top_first_point traces

/-- The retained top perimeter's last owner reading differs from the fixed upper-right corner value by at most four
times the paid global overlap bound. -/
theorem perimeter_top_last_bound
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    Data.Gaussian.Norm.Basic.normSq ((traces.top.leftReadings cached.anchors cached.offsets).values (Fin.last
      traces.top.vertices.rest.length) -
      cached.corners.values 2) ≤ 4 * request.globalBound := by
  apply DomainPrimitives.reading_corner_bound request cached
  change Trace.point traces.top (traces.top.vertices.indexed (Fin.last traces.top.vertices.rest.length)) =
    FaceCorners.point face.cell.box 2
  exact RectangularCenteredPerimeter.top_last_point traces

/-- The retained left perimeter's first owner reading differs from the fixed lower-left corner value by at most four
times the paid global overlap bound. -/
theorem perimeter_left_first_bound
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    Data.Gaussian.Norm.Basic.normSq ((traces.left.leftReadings cached.anchors cached.offsets).values 0 -
      cached.corners.values 0) ≤ 4 * request.globalBound := by
  apply DomainPrimitives.reading_corner_bound request cached
  change Trace.point traces.left (traces.left.vertices.indexed 0) =
    FaceCorners.point face.cell.box 0
  exact RectangularCenteredPerimeter.left_first_point traces

/-- The retained left perimeter's last owner reading differs from the fixed upper-left corner value by at most four
times the paid global overlap bound. -/
theorem perimeter_left_last_bound
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    Data.Gaussian.Norm.Basic.normSq ((traces.left.leftReadings cached.anchors cached.offsets).values (Fin.last
      traces.left.vertices.rest.length) -
      cached.corners.values 3) ≤ 4 * request.globalBound := by
  apply DomainPrimitives.reading_corner_bound request cached
  change Trace.point traces.left (traces.left.vertices.indexed (Fin.last traces.left.vertices.rest.length)) =
    FaceCorners.point face.cell.box 3
  exact RectangularCenteredPerimeter.left_last_point traces

/-- The retained right perimeter's first owner reading differs from the fixed lower-right corner value by at most four
times the paid global overlap bound. -/
theorem perimeter_right_first_bound
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    Data.Gaussian.Norm.Basic.normSq ((traces.right.leftReadings cached.anchors cached.offsets).values 0 -
      cached.corners.values 1) ≤ 4 * request.globalBound := by
  apply DomainPrimitives.reading_corner_bound request cached
  change Trace.point traces.right (traces.right.vertices.indexed 0) =
    FaceCorners.point face.cell.box 1
  exact RectangularCenteredPerimeter.right_first_point traces

/-- The retained right perimeter's last owner reading differs from the fixed upper-right corner value by at most four
times the paid global overlap bound. -/
theorem perimeter_right_last_bound
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index) (traces :
      RectangularPerimeterTraces.PerimeterTraces mesh) :
    Data.Gaussian.Norm.Basic.normSq ((traces.right.leftReadings cached.anchors cached.offsets).values (Fin.last
      traces.right.vertices.rest.length) -
      cached.corners.values 2) ≤ 4 * request.globalBound := by
  apply DomainPrimitives.reading_corner_bound request cached
  change Trace.point traces.right (traces.right.vertices.indexed (Fin.last traces.right.vertices.rest.length)) =
    FaceCorners.point face.cell.box 2
  exact RectangularCenteredPerimeter.right_last_point traces

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterCornerReadings
