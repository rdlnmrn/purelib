module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularHorizontalTraceLengths
public import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularVerticalTraceLengths
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PerimeterGeometry
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

@[expose] public section

/-! All fine vertices, including duplicate owner junctions, lie on the
certified rectangle side of the retained source occurrence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterSideBoundary
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry (OnSide)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (bottom_first_point top_first_point left_first_point
  right_first_point)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace bank} {models :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face}
  {sheet : Fin 2} (domain : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet)
  {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts domain.geometry}
  {mesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts face.cell.box}

/-- Every owned bottom perimeter vertex lies on the original regular face's bottom side. -/
theorem bottom_onSide (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (vertex :
  (RectangularPerimeterTraces.bottomSelfSide mesh).Vertex mesh.depth) :
    SideBoundaryGeometry.OnSide face.cell.box .bottom (traces.bottom.point vertex) := by
  have inside := (domain.patch.cell_refines (traces.bottom.leftOwner vertex).column
    (traces.bottom.leftOwner vertex).row).contains (traces.bottom.leftOwner vertex).contains
  refine ⟨inside, ?_⟩
  have same := (RectangularHorizontalTraceLengths.point_height traces.bottom vertex).trans
    (RectangularHorizontalTraceLengths.point_height traces.bottom (traces.bottom.vertices.indexed 0)).symm
  exact same.trans (congrArg (fun point => point.im) (RectangularCenteredPerimeter.bottom_first_point traces))

/-- Every owned top perimeter vertex lies on the original regular face's top side. -/
theorem top_onSide (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (vertex :
  (RectangularPerimeterTraces.topSelfSide mesh).Vertex mesh.depth) :
    SideBoundaryGeometry.OnSide face.cell.box .top (traces.top.point vertex) := by
  have inside := (domain.patch.cell_refines (traces.top.leftOwner vertex).column
    (traces.top.leftOwner vertex).row).contains (traces.top.leftOwner vertex).contains
  refine ⟨inside, ?_⟩
  have same := (RectangularHorizontalTraceLengths.point_height traces.top vertex).trans
    (RectangularHorizontalTraceLengths.point_height traces.top (traces.top.vertices.indexed 0)).symm
  exact same.trans (congrArg (fun point => point.im) (RectangularCenteredPerimeter.top_first_point traces))

/-- Every owned left perimeter vertex lies on the original regular face's left side. -/
theorem left_onSide (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (vertex :
  (RectangularPerimeterTraces.leftSelfSide mesh).Vertex mesh.depth) :
    SideBoundaryGeometry.OnSide face.cell.box .left (traces.left.point vertex) := by
  have inside := (domain.patch.cell_refines (traces.left.leftOwner vertex).column
    (traces.left.leftOwner vertex).row).contains (traces.left.leftOwner vertex).contains
  refine ⟨inside, ?_⟩
  have same := (RectangularVerticalTraceLengths.point_horizontal traces.left vertex).trans
    (RectangularVerticalTraceLengths.point_horizontal traces.left (traces.left.vertices.indexed 0)).symm
  exact same.trans (congrArg (fun point => point.re) (RectangularCenteredPerimeter.left_first_point traces))

/-- Every owned right perimeter vertex lies on the original regular face's right side. -/
theorem right_onSide (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (vertex :
  (RectangularPerimeterTraces.rightSelfSide mesh).Vertex mesh.depth) :
    SideBoundaryGeometry.OnSide face.cell.box .right (traces.right.point vertex) := by
  have inside := (domain.patch.cell_refines (traces.right.leftOwner vertex).column
    (traces.right.leftOwner vertex).row).contains (traces.right.leftOwner vertex).contains
  refine ⟨inside, ?_⟩
  have same := (RectangularVerticalTraceLengths.point_horizontal traces.right vertex).trans
    (RectangularVerticalTraceLengths.point_horizontal traces.right (traces.right.vertices.indexed 0)).symm
  exact same.trans (congrArg (fun point => point.re) (RectangularCenteredPerimeter.right_first_point traces))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterSideBoundary
