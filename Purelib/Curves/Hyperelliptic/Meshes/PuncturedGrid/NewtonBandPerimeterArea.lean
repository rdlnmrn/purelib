module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PerimeterGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
public import Purelib.Riemann.Integration.RectangularPerimeterLengths
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
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
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate

@[expose] public section

/-! Quadratic radius decay on the actual shared-band boundary. An inner grid
hole merely contained in the band does not satisfy the side hypothesis. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonBandPerimeterArea
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies (PreparedBandFamily DifferentialFamily)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry (Request bottom top left right)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (bottom_first_point bottom_last_point top_first_point
  top_last_point left_first_point left_last_point right_first_point right_last_point)
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
  {first second : Fin genus}
  {bandAmbient : Box} {current :
    Purelib.RootIsolation.State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : Purelib.Riemann.RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {family : DifferentialFamily profile genus} {target radius
    : Rational}

namespace SideGeometry

/-- The actual bottom perimeter's centered paired area has quadratic decay in the retained Newton band radius.

The supplied trace must lie on one side of that same band, with its length-error padding and both differential
references paid. -/
theorem bottom_band_area_bound (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (lengths :
  RectangularPerimeterLengths.Lengths traces)
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family target radius)
    (budget : NoisyPathArea.LengthErrorBudget traces.bottom.vertices.rest.length band.selection.sample.output.radius)
    (paddingLe : budget.padding ≤ band.selection.sample.output.radius)
    (references : SideGeometry.Request (SideGeometry.bottom domain traces) domain
      (PeriodMatrix.standardDifferential first) (PeriodMatrix.standardDifferential second) budget.tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (traces.bottom.point vertex))
    (side : ∀ a b, PreparedBoundarySegments.SameSide band.selection.sample.output.box (traces.bottom.point a)
      (traces.bottom.point b))
    {index : Nat} (later : references.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential first) index)
    (rightData : PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential second) index)
    (samples : RectangularCenteredPerimeter.Centered traces (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ :
          PrimitivePoint))) :
    Data.Gaussian.Norm.Basic.normSq samples.bottom.centeredArea ≤
      100 * (3 + 128 * PreparedBandFamily.areaRate family) * (4 * PreparedBandFamily.areaRate family + 3) *
        band.selection.sample.output.radius^2 := by
  have bound := SideGeometry.bottom_area_bound domain traces lengths budget references
    (band.forDifferential first) (band.forDifferential second) inside side inside side
    (PreparedBandFamily.pairedDensity_nonnegative band first second) (PreparedBandFamily.first_density_le band first
      second)
    (PreparedBandFamily.second_density_le band first second) later leftData rightData samples
  apply bound.trans
  apply PreparedBandFamily.area_rate band first second budget paddingLe face.cell.box.widthX_nonneg
  have startInside := inside (traces.bottom.vertices.indexed 0)
  have finishInside := inside (traces.bottom.vertices.indexed (Fin.last traces.bottom.vertices.rest.length))
  rw [RectangularCenteredPerimeter.bottom_first_point traces] at startInside
  rw [RectangularCenteredPerimeter.bottom_last_point traces] at finishInside
  exact (Fraction.Order.Arithmetic.sub_le_sub_direct finishInside.2.1 startInside.1).trans (PreparedBandFamily.widthX_le
    band)

/-- The actual top perimeter's centered paired area has quadratic decay in the retained Newton band radius.

The supplied trace must lie on one side of that same band, with its length-error padding and both differential
references paid. -/
theorem top_band_area_bound (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (lengths :
  RectangularPerimeterLengths.Lengths traces)
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family target radius)
    (budget : NoisyPathArea.LengthErrorBudget traces.top.vertices.rest.length band.selection.sample.output.radius)
    (paddingLe : budget.padding ≤ band.selection.sample.output.radius)
    (references : SideGeometry.Request (SideGeometry.top domain traces) domain
      (PeriodMatrix.standardDifferential first) (PeriodMatrix.standardDifferential second) budget.tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (traces.top.point vertex))
    (side : ∀ a b, PreparedBoundarySegments.SameSide band.selection.sample.output.box (traces.top.point a)
      (traces.top.point b))
    {index : Nat} (later : references.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential first) index)
    (rightData : PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential second) index)
    (samples : RectangularCenteredPerimeter.Centered traces (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ :
          PrimitivePoint))) :
    Data.Gaussian.Norm.Basic.normSq samples.top.centeredArea ≤
      100 * (3 + 128 * PreparedBandFamily.areaRate family) * (4 * PreparedBandFamily.areaRate family + 3) *
        band.selection.sample.output.radius^2 := by
  have bound := SideGeometry.top_area_bound domain traces lengths budget references
    (band.forDifferential first) (band.forDifferential second) inside side inside side
    (PreparedBandFamily.pairedDensity_nonnegative band first second) (PreparedBandFamily.first_density_le band first
      second)
    (PreparedBandFamily.second_density_le band first second) later leftData rightData samples
  apply bound.trans
  apply PreparedBandFamily.area_rate band first second budget paddingLe face.cell.box.widthX_nonneg
  have startInside := inside (traces.top.vertices.indexed 0)
  have finishInside := inside (traces.top.vertices.indexed (Fin.last traces.top.vertices.rest.length))
  rw [RectangularCenteredPerimeter.top_first_point traces] at startInside
  rw [RectangularCenteredPerimeter.top_last_point traces] at finishInside
  exact (Fraction.Order.Arithmetic.sub_le_sub_direct finishInside.2.1 startInside.1).trans (PreparedBandFamily.widthX_le
    band)

/-- The actual left perimeter's centered paired area has quadratic decay in the retained Newton band radius.

The supplied trace must lie on one side of that same band, with its length-error padding and both differential
references paid. -/
theorem left_band_area_bound (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (lengths :
  RectangularPerimeterLengths.Lengths traces)
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family target radius)
    (budget : NoisyPathArea.LengthErrorBudget traces.left.vertices.rest.length band.selection.sample.output.radius)
    (paddingLe : budget.padding ≤ band.selection.sample.output.radius)
    (references : SideGeometry.Request (SideGeometry.left domain traces) domain
      (PeriodMatrix.standardDifferential first) (PeriodMatrix.standardDifferential second) budget.tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (traces.left.point vertex))
    (side : ∀ a b, PreparedBoundarySegments.SameSide band.selection.sample.output.box (traces.left.point a)
      (traces.left.point b))
    {index : Nat} (later : references.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential first) index)
    (rightData : PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential second) index)
    (samples : RectangularCenteredPerimeter.Centered traces (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ :
          PrimitivePoint))) :
    Data.Gaussian.Norm.Basic.normSq samples.left.centeredArea ≤
      100 * (3 + 128 * PreparedBandFamily.areaRate family) * (4 * PreparedBandFamily.areaRate family + 3) *
        band.selection.sample.output.radius^2 := by
  have bound := SideGeometry.left_area_bound domain traces lengths budget references
    (band.forDifferential first) (band.forDifferential second) inside side inside side
    (PreparedBandFamily.pairedDensity_nonnegative band first second) (PreparedBandFamily.first_density_le band first
      second)
    (PreparedBandFamily.second_density_le band first second) later leftData rightData samples
  apply bound.trans
  apply PreparedBandFamily.area_rate band first second budget paddingLe face.cell.box.widthY_nonneg
  have startInside := inside (traces.left.vertices.indexed 0)
  have finishInside := inside (traces.left.vertices.indexed (Fin.last traces.left.vertices.rest.length))
  rw [RectangularCenteredPerimeter.left_first_point traces] at startInside
  rw [RectangularCenteredPerimeter.left_last_point traces] at finishInside
  exact (Fraction.Order.Arithmetic.sub_le_sub_direct finishInside.2.2.2 startInside.2.2.1).trans
    (PreparedBandFamily.widthY_le band)

/-- The actual right perimeter's centered paired area has quadratic decay in the retained Newton band radius.

The supplied trace must lie on one side of that same band, with its length-error padding and both differential
references paid. -/
theorem right_band_area_bound (traces : RectangularPerimeterTraces.PerimeterTraces mesh) (lengths :
  RectangularPerimeterLengths.Lengths traces)
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family target radius)
    (budget : NoisyPathArea.LengthErrorBudget traces.right.vertices.rest.length band.selection.sample.output.radius)
    (paddingLe : budget.padding ≤ band.selection.sample.output.radius)
    (references : SideGeometry.Request (SideGeometry.right domain traces) domain
      (PeriodMatrix.standardDifferential first) (PeriodMatrix.standardDifferential second) budget.tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (traces.right.point vertex))
    (side : ∀ a b, PreparedBoundarySegments.SameSide band.selection.sample.output.box (traces.right.point a)
      (traces.right.point b))
    {index : Nat} (later : references.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential first) index)
    (rightData : PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential second) index)
    (samples : RectangularCenteredPerimeter.Centered traces (fun column row point =>
      (⟨leftData.anchors.alignedValue leftData.offsets column row point,
        rightData.anchors.alignedValue rightData.offsets column row point⟩ :
          PrimitivePoint))) :
    Data.Gaussian.Norm.Basic.normSq samples.right.centeredArea ≤
      100 * (3 + 128 * PreparedBandFamily.areaRate family) * (4 * PreparedBandFamily.areaRate family + 3) *
        band.selection.sample.output.radius^2 := by
  have bound := SideGeometry.right_area_bound domain traces lengths budget references
    (band.forDifferential first) (band.forDifferential second) inside side inside side
    (PreparedBandFamily.pairedDensity_nonnegative band first second) (PreparedBandFamily.first_density_le band first
      second)
    (PreparedBandFamily.second_density_le band first second) later leftData rightData samples
  apply bound.trans
  apply PreparedBandFamily.area_rate band first second budget paddingLe face.cell.box.widthY_nonneg
  have startInside := inside (traces.right.vertices.indexed 0)
  have finishInside := inside (traces.right.vertices.indexed (Fin.last traces.right.vertices.rest.length))
  rw [RectangularCenteredPerimeter.right_first_point traces] at startInside
  rw [RectangularCenteredPerimeter.right_last_point traces] at finishInside
  exact (Fraction.Order.Arithmetic.sub_le_sub_direct finishInside.2.2.2 startInside.2.2.1).trans
    (PreparedBandFamily.widthY_le band)

end SideGeometry
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonBandPerimeterArea
