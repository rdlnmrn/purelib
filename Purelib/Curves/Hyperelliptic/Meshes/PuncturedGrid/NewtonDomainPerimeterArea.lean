module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
public import Purelib.Riemann.Integration.RectangularPerimeterLengths
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.RectangularHorizontalTraceLengths
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularVerticalTraceLengths
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonSideArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PerimeterGeometry
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
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
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularPerimeterLengths

open Purelib.Riemann.Paths

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.State

open Purelib.Topology.Polygon

@[expose] public section

/-! Full Newton bounds on retained domain perimeter traces. Both components
are read from the supplied domain primitives with their actual owner offsets. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation (SideGeometry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry (Request)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry (bottom top left right)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} (domain : PeriodDomain models sheet)
  {cuts : GridCuts domain.geometry}
  {mesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts face.cell.box}
  {left right : Differential genus}

namespace SideGeometry

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry
/-- Construct the request from geometry before acquiring any numerical bank. -/
def bottomRequest (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (left right :
  Differentials.Basic.Differential genus)
    {allowance : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget traces.bottom.vertices.rest.length
      allowance) :=
  SideGeometry.Request.build (SideGeometry.bottom domain traces) domain left right budget.tolerance
    budget.tolerance_positive

/-- The actual bottom perimeter's centered paired area satisfies the retained Newton density and horizontal-length
budget. -/
theorem bottom_area_bound (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (lengths :
  RectangularPerimeterLengths.Lengths traces)
    {allowance density : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget traces.bottom.vertices.rest.length
      allowance)
    (references : SideGeometry.Request (SideGeometry.bottom domain traces) domain left right budget.tolerance)
    {bandAmbient : Rational.Box} {current : Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : NewtonBandDifferentials.DifferentialProfile profile left.exponent}
    {rightProfile : NewtonBandDifferentials.DifferentialProfile profile right.exponent}
    {leftTarget rightTarget : Fraction.Rational}
    (leftBand : PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains (traces.bottom.point vertex))
    (leftSide : ∀ first last, PreparedBoundarySegments.SameSide leftBand.sample.output.box (traces.bottom.point first)
      (traces.bottom.point last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains (traces.bottom.point vertex))
    (rightSide : ∀ first last, PreparedBoundarySegments.SameSide rightBand.sample.output.box (traces.bottom.point first)
      (traces.bottom.point last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile leftBand.error ≤
      density)
    (rightDensity : PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile rightBand.error ≤
      density)
    {index : Nat} (later : references.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives domain left index) (rightData : PrimitiveData.DomainPrimitives domain
      right index)
    (samples : RectangularCenteredPerimeter.Centered traces (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ : Stokes.PrimitivePoint))) :
    Data.Gaussian.Norm.Basic.normSq samples.bottom.centeredArea ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) * (4 * density + 3) *
        (face.cell.box.xUpper - face.cell.box.xLower + allowance)^2 := by
  have bound := NewtonSideArea.area_bound budget references leftBand rightBand
    (fun vertex => leftInside (traces.bottom.vertices.indexed vertex))
    (fun first last => leftSide (traces.bottom.vertices.indexed first) (traces.bottom.vertices.indexed last))
    (fun vertex => rightInside (traces.bottom.vertices.indexed vertex))
    (fun first last => rightSide (traces.bottom.vertices.indexed first) (traces.bottom.vertices.indexed last))
    densityNonnegative leftDensity rightDensity later leftData rightData
    (traces.bottom.leftReadings leftData.anchors leftData.offsets)
    (traces.bottom.leftReadings rightData.anchors rightData.offsets)
    (values := fun vertex => traces.bottom.leftValue (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ : Stokes.PrimitivePoint))
      (traces.bottom.vertices.indexed vertex))
    (fun vertex => by
      rw [traces.bottom.leftReadings_value, traces.bottom.leftReadings_value]
      rfl)
    samples.bottom lengths.bottom.values lengths.bottom.nonnegative (fun edge => by
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact RectangularHorizontalTraceLengths.length_movement traces.bottom lengths.bottom edge)
  rw [← lengths.bottom.total_eq, Lengths.bottom_total lengths] at bound
  exact bound

/-- Construct the request from geometry before acquiring any numerical bank. -/
def topRequest (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (left right : Differentials.Basic.Differential
  genus)
    {allowance : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget traces.top.vertices.rest.length allowance)
      :=
  SideGeometry.Request.build (SideGeometry.top domain traces) domain left right budget.tolerance
    budget.tolerance_positive

/-- The actual top perimeter's centered paired area satisfies the retained Newton density and horizontal-length budget.
-/
theorem top_area_bound (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (lengths :
  RectangularPerimeterLengths.Lengths traces)
    {allowance density : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget traces.top.vertices.rest.length
      allowance)
    (references : SideGeometry.Request (SideGeometry.top domain traces) domain left right budget.tolerance)
    {bandAmbient : Rational.Box} {current : Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : NewtonBandDifferentials.DifferentialProfile profile left.exponent}
    {rightProfile : NewtonBandDifferentials.DifferentialProfile profile right.exponent}
    {leftTarget rightTarget : Fraction.Rational}
    (leftBand : PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains (traces.top.point vertex))
    (leftSide : ∀ first last, PreparedBoundarySegments.SameSide leftBand.sample.output.box (traces.top.point first)
      (traces.top.point last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains (traces.top.point vertex))
    (rightSide : ∀ first last, PreparedBoundarySegments.SameSide rightBand.sample.output.box (traces.top.point first)
      (traces.top.point last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile leftBand.error ≤
      density)
    (rightDensity : PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile rightBand.error ≤
      density)
    {index : Nat} (later : references.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives domain left index) (rightData : PrimitiveData.DomainPrimitives domain
      right index)
    (samples : RectangularCenteredPerimeter.Centered traces (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ : Stokes.PrimitivePoint))) :
    Data.Gaussian.Norm.Basic.normSq samples.top.centeredArea ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) * (4 * density + 3) *
        (face.cell.box.xUpper - face.cell.box.xLower + allowance)^2 := by
  have bound := NewtonSideArea.area_bound budget references leftBand rightBand
    (fun vertex => leftInside (traces.top.vertices.indexed vertex))
    (fun first last => leftSide (traces.top.vertices.indexed first) (traces.top.vertices.indexed last))
    (fun vertex => rightInside (traces.top.vertices.indexed vertex))
    (fun first last => rightSide (traces.top.vertices.indexed first) (traces.top.vertices.indexed last))
    densityNonnegative leftDensity rightDensity later leftData rightData
    (traces.top.leftReadings leftData.anchors leftData.offsets)
    (traces.top.leftReadings rightData.anchors rightData.offsets)
    (values := fun vertex => traces.top.leftValue (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ : Stokes.PrimitivePoint))
      (traces.top.vertices.indexed vertex))
    (fun vertex => by
      rw [traces.top.leftReadings_value, traces.top.leftReadings_value]
      rfl)
    samples.top lengths.top.values lengths.top.nonnegative (fun edge => by
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact RectangularHorizontalTraceLengths.length_movement traces.top lengths.top edge)
  rw [← lengths.top.total_eq, Lengths.top_total lengths] at bound
  exact bound

/-- Construct the request from geometry before acquiring any numerical bank. -/
def leftRequest (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (left right :
  Differentials.Basic.Differential genus)
    {allowance : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget traces.left.vertices.rest.length
      allowance) :=
  SideGeometry.Request.build (SideGeometry.left domain traces) domain left right budget.tolerance
    budget.tolerance_positive

/-- The actual left perimeter's centered paired area satisfies the retained Newton density and vertical-length budget.
-/
theorem left_area_bound (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (lengths :
  RectangularPerimeterLengths.Lengths traces)
    {allowance density : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget traces.left.vertices.rest.length
      allowance)
    (references : SideGeometry.Request (SideGeometry.left domain traces) domain left right budget.tolerance)
    {bandAmbient : Rational.Box} {current : Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : NewtonBandDifferentials.DifferentialProfile profile left.exponent}
    {rightProfile : NewtonBandDifferentials.DifferentialProfile profile right.exponent}
    {leftTarget rightTarget : Fraction.Rational}
    (leftBand : PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains (traces.left.point vertex))
    (leftSide : ∀ first last, PreparedBoundarySegments.SameSide leftBand.sample.output.box (traces.left.point first)
      (traces.left.point last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains (traces.left.point vertex))
    (rightSide : ∀ first last, PreparedBoundarySegments.SameSide rightBand.sample.output.box (traces.left.point first)
      (traces.left.point last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile leftBand.error ≤
      density)
    (rightDensity : PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile rightBand.error ≤
      density)
    {index : Nat} (later : references.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives domain left index) (rightData : PrimitiveData.DomainPrimitives domain
      right index)
    (samples : RectangularCenteredPerimeter.Centered traces (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ : Stokes.PrimitivePoint))) :
    Data.Gaussian.Norm.Basic.normSq samples.left.centeredArea ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) * (4 * density + 3) *
        (face.cell.box.yUpper - face.cell.box.yLower + allowance)^2 := by
  have bound := NewtonSideArea.area_bound budget references leftBand rightBand
    (fun vertex => leftInside (traces.left.vertices.indexed vertex))
    (fun first last => leftSide (traces.left.vertices.indexed first) (traces.left.vertices.indexed last))
    (fun vertex => rightInside (traces.left.vertices.indexed vertex))
    (fun first last => rightSide (traces.left.vertices.indexed first) (traces.left.vertices.indexed last))
    densityNonnegative leftDensity rightDensity later leftData rightData
    (traces.left.leftReadings leftData.anchors leftData.offsets)
    (traces.left.leftReadings rightData.anchors rightData.offsets)
    (values := fun vertex => traces.left.leftValue (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ : Stokes.PrimitivePoint))
      (traces.left.vertices.indexed vertex))
    (fun vertex => by
      rw [traces.left.leftReadings_value, traces.left.leftReadings_value]
      rfl)
    samples.left lengths.left.values lengths.left.nonnegative (fun edge => by
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact RectangularVerticalTraceLengths.length_movement traces.left lengths.left edge)
  rw [← lengths.left.total_eq, Lengths.left_total lengths] at bound
  exact bound

/-- Construct the request from geometry before acquiring any numerical bank. -/
def rightRequest (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (left right :
  Differentials.Basic.Differential genus)
    {allowance : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget traces.right.vertices.rest.length
      allowance) :=
  SideGeometry.Request.build (SideGeometry.right domain traces) domain left right budget.tolerance
    budget.tolerance_positive

/-- The actual right perimeter's centered paired area satisfies the retained Newton density and vertical-length budget.
-/
theorem right_area_bound (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (lengths :
  RectangularPerimeterLengths.Lengths traces)
    {allowance density : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget traces.right.vertices.rest.length
      allowance)
    (references : SideGeometry.Request (SideGeometry.right domain traces) domain left right budget.tolerance)
    {bandAmbient : Rational.Box} {current : Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : NewtonBandDifferentials.DifferentialProfile profile left.exponent}
    {rightProfile : NewtonBandDifferentials.DifferentialProfile profile right.exponent}
    {leftTarget rightTarget : Fraction.Rational}
    (leftBand : PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains (traces.right.point vertex))
    (leftSide : ∀ first last, PreparedBoundarySegments.SameSide leftBand.sample.output.box (traces.right.point first)
      (traces.right.point last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains (traces.right.point vertex))
    (rightSide : ∀ first last, PreparedBoundarySegments.SameSide rightBand.sample.output.box (traces.right.point first)
      (traces.right.point last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile leftBand.error ≤
      density)
    (rightDensity : PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile rightBand.error ≤
      density)
    {index : Nat} (later : references.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives domain left index) (rightData : PrimitiveData.DomainPrimitives domain
      right index)
    (samples : RectangularCenteredPerimeter.Centered traces (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ : Stokes.PrimitivePoint))) :
    Data.Gaussian.Norm.Basic.normSq samples.right.centeredArea ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) * (4 * density + 3) *
        (face.cell.box.yUpper - face.cell.box.yLower + allowance)^2 := by
  have bound := NewtonSideArea.area_bound budget references leftBand rightBand
    (fun vertex => leftInside (traces.right.vertices.indexed vertex))
    (fun first last => leftSide (traces.right.vertices.indexed first) (traces.right.vertices.indexed last))
    (fun vertex => rightInside (traces.right.vertices.indexed vertex))
    (fun first last => rightSide (traces.right.vertices.indexed first) (traces.right.vertices.indexed last))
    densityNonnegative leftDensity rightDensity later leftData rightData
    (traces.right.leftReadings leftData.anchors leftData.offsets)
    (traces.right.leftReadings rightData.anchors rightData.offsets)
    (values := fun vertex => traces.right.leftValue (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ : Stokes.PrimitivePoint))
      (traces.right.vertices.indexed vertex))
    (fun vertex => by
      rw [traces.right.leftReadings_value, traces.right.leftReadings_value]
      rfl)
    samples.right lengths.right.values lengths.right.nonnegative (fun edge => by
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact RectangularVerticalTraceLengths.length_movement traces.right lengths.right edge)
  rw [← lengths.right.total_eq, Lengths.right_total lengths] at bound
  exact bound

end SideGeometry
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea
