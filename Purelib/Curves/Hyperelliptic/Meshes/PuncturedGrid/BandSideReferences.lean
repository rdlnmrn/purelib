module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PerimeterGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Integration.RectangularPerimeterLengths
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandBounds
public import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonBandPerimeterArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterSideBoundary
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation

open Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-! A requested Newton comparison selected by an actual rectangle side.
The source boundary certificate discharges all fine-vertex geometry. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : Face.InverseModels.BranchCellBank.FaceModels frames face}
  {sheet : Fin 2} (domain : Face.Periods.PeriodDomain models sheet)
  {cuts : Paths.RectangularSegmentSplitting.GridCuts domain.geometry}
  {mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts face.cell.box}
  {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {family : RootContinuation.PreparedNewtonBandFamilies.DifferentialFamily profile genus} {target radius :
    Fraction.Rational}

/-- The original Newton-band comparison request for a specified rectangle side.

Its two standard differentials, actual side trace and tolerance remain indexed by the retained domain and extracted
band. -/
def BandSideReference (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh) (band :
  RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family target radius)
    (first second : Fin genus) : Meshes.GridLiftedDualSteps.GridSide → Type _
  | .bottom => SideGeometry.Request
    (SideGeometry.bottom domain traces) domain
      (Periods.PeriodMatrix.standardDifferential first) (Periods.PeriodMatrix.standardDifferential second)
      (PreparedBandFamily.sideBudget band
        traces.bottom.vertices.rest.length).tolerance
  | .right => SideGeometry.Request
    (SideGeometry.right domain traces) domain
      (Periods.PeriodMatrix.standardDifferential first) (Periods.PeriodMatrix.standardDifferential second)
      (PreparedBandFamily.sideBudget band
        traces.right.vertices.rest.length).tolerance
  | .top => SideGeometry.Request
    (SideGeometry.top domain traces) domain
      (Periods.PeriodMatrix.standardDifferential first) (Periods.PeriodMatrix.standardDifferential second)
      (PreparedBandFamily.sideBudget band
        traces.top.vertices.rest.length).tolerance
  | .left => SideGeometry.Request
    (SideGeometry.left domain traces) domain
      (Periods.PeriodMatrix.standardDifferential first) (Periods.PeriodMatrix.standardDifferential second)
      (PreparedBandFamily.sideBudget band
        traces.left.vertices.rest.length).tolerance

namespace BandSideReference
variable {domain} {traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh} {band :
  RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family target radius}
  {first second : Fin genus} {side : Meshes.GridLiftedDualSteps.GridSide}

/-- Prepare the original differential comparison at the actual selected rectangle side and its retained band tolerance.
-/
def build (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh)
    (band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family target radius) (first second : Fin
      genus) :
    (side : Meshes.GridLiftedDualSteps.GridSide) →
      BandSideReference domain traces band first second side
  | .bottom => NewtonDomainPerimeterArea.SideGeometry.bottomRequest domain traces
      (Periods.PeriodMatrix.standardDifferential first) (Periods.PeriodMatrix.standardDifferential second)
        ((PreparedBandFamily.sideBudget band _))
  | .right => NewtonDomainPerimeterArea.SideGeometry.rightRequest domain traces
      (Periods.PeriodMatrix.standardDifferential first) (Periods.PeriodMatrix.standardDifferential second)
        ((PreparedBandFamily.sideBudget band _))
  | .top => NewtonDomainPerimeterArea.SideGeometry.topRequest domain traces
      (Periods.PeriodMatrix.standardDifferential first) (Periods.PeriodMatrix.standardDifferential second)
        ((PreparedBandFamily.sideBudget band _))
  | .left => NewtonDomainPerimeterArea.SideGeometry.leftRequest domain traces
      (Periods.PeriodMatrix.standardDifferential first) (Periods.PeriodMatrix.standardDifferential second)
        ((PreparedBandFamily.sideBudget band _))

/-- The retained comparison threshold of the selected original side request. -/
def index : (side : Meshes.GridLiftedDualSteps.GridSide) →
  BandSideReference domain traces band first second side → Nat
  | .bottom, request => SideGeometry.Request.index request
  | .right, request => SideGeometry.Request.index request
  | .top, request => SideGeometry.Request.index request
  | .left, request => SideGeometry.Request.index request

/-- Read the centered area of the specified original rectangle side. -/
def sideArea {values : Fin (domain.steps + 1) → Fin (domain.steps + 1) → Gaussian.Basic.Canonical →
  Topology.Polygon.Stokes.PrimitivePoint}
    (samples : Integration.RectangularCenteredPerimeter.Centered traces values) : Meshes.GridLiftedDualSteps.GridSide →
      Gaussian.Basic.Canonical
  | .bottom => samples.bottom.centeredArea
  | .top => samples.top.centeredArea
  | .left => samples.left.centeredArea
  | .right => samples.right.centeredArea

/-- The retained side request bounds its actual centered area by the Newton quadratic radius estimate.

The source boundary certificate supplies membership and common-side geometry for every original fine vertex. -/
theorem area_bound (reference : BandSideReference domain traces
  band first second side)
    (lengths : Integration.RectangularPerimeterLengths.Lengths traces)
    (boundary : SideBoundaryGeometry.SideBoundary face.cell.box
      band.selection.sample.output.box side)
    {stage : Nat} (later : BandSideReference.index side reference
      ≤ stage)
    (leftData : Face.PrimitiveData.DomainPrimitives domain
      (Periods.PeriodMatrix.standardDifferential first) stage)
    (rightData : Face.PrimitiveData.DomainPrimitives domain
      (Periods.PeriodMatrix.standardDifferential second) stage)
    (samples : Integration.RectangularCenteredPerimeter.Centered traces (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ : Topology.Polygon.Stokes.PrimitivePoint))) :
    Gaussian.Norm.Basic.normSq
      (BandSideReference.sideArea samples side) ≤
      PreparedBandFamily.areaCoefficient family *
        band.selection.sample.output.radius^2 := by
  cases side with
  | bottom =>
      exact NewtonBandPerimeterArea.SideGeometry.bottom_band_area_bound domain traces
        lengths band ((PreparedBandFamily.sideBudget band _))
        ((PreparedBandFamily.sideBudget_padding_le band _)) reference
        (fun vertex => boundary.contains (PerimeterSideBoundary.bottom_onSide domain
          traces vertex))
        (fun a b => boundary.sameSide face.cell.box_proper
          (PerimeterSideBoundary.bottom_onSide domain traces a)
            (PerimeterSideBoundary.bottom_onSide domain traces b))
        later leftData rightData samples
  | right =>
      exact NewtonBandPerimeterArea.SideGeometry.right_band_area_bound domain traces
        lengths band ((PreparedBandFamily.sideBudget band _))
        ((PreparedBandFamily.sideBudget_padding_le band _)) reference
        (fun vertex => boundary.contains (PerimeterSideBoundary.right_onSide domain
          traces vertex))
        (fun a b => boundary.sameSide face.cell.box_proper
          (PerimeterSideBoundary.right_onSide domain traces a)
            (PerimeterSideBoundary.right_onSide domain traces b))
        later leftData rightData samples
  | top =>
      exact NewtonBandPerimeterArea.SideGeometry.top_band_area_bound domain traces
        lengths band ((PreparedBandFamily.sideBudget band _))
        ((PreparedBandFamily.sideBudget_padding_le band _)) reference
        (fun vertex => boundary.contains (PerimeterSideBoundary.top_onSide domain
          traces vertex))
        (fun a b => boundary.sameSide face.cell.box_proper
          (PerimeterSideBoundary.top_onSide domain traces a)
            (PerimeterSideBoundary.top_onSide domain traces b))
        later leftData rightData samples
  | left =>
      exact NewtonBandPerimeterArea.SideGeometry.left_band_area_bound domain traces
        lengths band ((PreparedBandFamily.sideBudget band _))
        ((PreparedBandFamily.sideBudget_padding_le band _)) reference
        (fun vertex => boundary.contains (PerimeterSideBoundary.left_onSide domain
          traces vertex))
        (fun a b => boundary.sameSide face.cell.box_proper
          (PerimeterSideBoundary.left_onSide domain traces a)
            (PerimeterSideBoundary.left_onSide domain traces b))
        later leftData rightData samples

end BandSideReference
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences
