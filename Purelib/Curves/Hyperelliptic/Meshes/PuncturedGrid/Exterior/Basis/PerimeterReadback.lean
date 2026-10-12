module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadback
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Topology.Polygon

@[expose] public section

/-! Read weighted common-basis physical areas back to the complete Newton perimeter. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback

open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

open Purelib.Riemann.Normalization.RectangularInverseModels
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal)
variable {stage : Nat}
  {cuts : GridCuts ((domains.get
    occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    ObservationMesh cuts meshBox}

namespace SharedPerimeter

/-- The weighted value uses the very face, sheet, owner cell and numerical stage retained by the complete Newton
assembly. -/
def gridValues (cache : RegularMeshes.Numerics domains stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (column row : Fin (((domains.get occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).steps +
      1))
    (point : InverseRootPolynomial.Gaussian) : PrimitivePoint :=
  ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow *
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet basisRow).anchors.alignedValue
      (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet basisRow).offsets column row
        point))

variable (traces : PerimeterTraces mesh) (cache :
  Numerics domains stage)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- Read the coefficient-weighted original shared face-bank values on the retained side's actual indexed trace vertices.
-/
def values : (side : GridLiftedDualSteps.GridSide) →
    Fin (SharedPhysicalPerimeterReadings.count traces side + 1) → Stokes.PrimitivePoint
  | .bottom, vertex => ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin (fun row => coefficients row *
      SharedPhysicalHorizontalReadings.secondValue (occurrence := occurrence)
        traces.bottom (cache.get row) (traces.bottom.vertices.indexed vertex)))
  | .top, vertex => ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin (fun row => coefficients row *
      SharedPhysicalHorizontalReadings.secondValue (occurrence := occurrence)
        traces.top (cache.get row) (traces.top.vertices.indexed vertex)))
  | .left, vertex => ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin (fun row => coefficients row *
      SharedPhysicalVerticalReadings.secondValue (occurrence := occurrence)
        traces.left (cache.get row) (traces.left.vertices.indexed vertex)))
  | .right, vertex => ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin (fun row => coefficients row *
      SharedPhysicalVerticalReadings.secondValue (occurrence := occurrence)
        traces.right (cache.get row) (traces.right.vertices.indexed vertex)))

/-- Read the selected original side's cached weighted perimeter area. -/
def sideArea {assembly : ObservationMesh.ClippedAssembly mesh
  (gridValues (occurrence :=
  occurrence) cache coefficients)}
    (perimeter : assembly.Perimeter) : GridLiftedDualSteps.GridSide → InverseRootPolynomial.Gaussian
  | .bottom => perimeter.bottom
  | .top => perimeter.top
  | .left => perimeter.left
  | .right => perimeter.right

/-- Identify the entire weighted side area, with its owner junctions, in the actual perimeter assembly rather than
merely identifying endpoint totals. -/
theorem original_area {side : GridLiftedDualSteps.GridSide}
    (sample : CenteredBilinearPath.Sample
      (values traces cache
      coefficients side))
    (assembly : ObservationMesh.ClippedAssembly mesh
      (gridValues (occurrence
      := occurrence) cache coefficients))
    (perimeter : assembly.Perimeter) :
    sample.originalArea =
      sideArea cache
      coefficients perimeter side := by
  have retained := sample.originalArea_eq
  cases side with
  | bottom => exact retained.trans (traces.bottom_area _ assembly perimeter)
  | top => exact retained.trans (traces.top_area _ assembly perimeter)
  | left => exact retained.trans (traces.left_area _ assembly perimeter)
  | right => exact retained.trans (traces.right_area _ assembly perimeter)

/-- Keep the endpoint chord when passing from grouped centered paths to the uncentered Newton boundary valuation. -/
theorem centered_add_endpoint {side : GridLiftedDualSteps.GridSide}
    (sample : CenteredBilinearPath.Sample
      (values traces cache
      coefficients side))
    (assembly : ObservationMesh.ClippedAssembly mesh
      (gridValues (occurrence
      := occurrence) cache coefficients))
    (perimeter : assembly.Perimeter) :
    sample.centeredArea + sample.endpoint =
      sideArea cache
      coefficients perimeter side :=
  sample.decomposition.symm.trans
    (original_area traces
    cache coefficients sample assembly perimeter)

/-- Assemble all four sides with the rectangle's actual orientation. Every centering chord remains in the complete
exterior expression. -/
theorem exterior_readback
    (samples : (side : GridLiftedDualSteps.GridSide) → CenteredBilinearPath.Sample
      (values traces cache
      coefficients side))
    (assembly : ObservationMesh.ClippedAssembly mesh
      (gridValues (occurrence
      := occurrence) cache coefficients))
    (perimeter : assembly.Perimeter) :
    assembly.exterior =
      ((samples .bottom).centeredArea + (samples .bottom).endpoint) +
      ((samples .right).centeredArea + (samples .right).endpoint) -
      ((samples .top).centeredArea + (samples .top).endpoint) -
      ((samples .left).centeredArea + (samples .left).endpoint) := by
  rw [centered_add_endpoint
    traces cache coefficients (samples .bottom) assembly perimeter,
    centered_add_endpoint
      traces cache coefficients (samples .right) assembly perimeter,
    centered_add_endpoint
      traces cache coefficients (samples .top) assembly perimeter,
    centered_add_endpoint
      traces cache coefficients (samples .left) assembly perimeter]
  exact perimeter.exterior_eq

end SharedPerimeter
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
