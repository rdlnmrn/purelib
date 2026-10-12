module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PerimeterGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandBounds
public import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonBandPerimeterArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Paid full-area bounds on normalized sides of the shared Newton band.
The area radius is chosen before extraction, and junction tolerances after
the trace is fixed. The inner grid hole is not identified with this band. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPaidPerimeters

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {target : Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    target}

namespace CenteredPerimeters
variable {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {family : RootContinuation.PreparedNewtonBandFamilies.DifferentialFamily profile genus}
  {areaTarget radius periodTarget : Fraction.Rational}

/-- The normalized original bottom perimeter area meets the paid Newton radius target.

The retained reference request must be sufficiently late, and all actual trace vertices must lie on a common side of the
extracted band. -/
theorem bottom_newton_area_paid (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples) (position :
      Fin base.faces.regulars.length) (sheet : Fin 2)
    (radiusBudget : RootContinuation.PreparedNewtonBandSamples.PreparedBandBudget
      (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient family) areaTarget radius)
    (band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radiusBudget.size)
    (references : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request
      (Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.bottom ((domains.get position).domain sheet)
        ((samples.traces.get position).get sheet))
      ((domains.get position).domain sheet) (Periods.PeriodMatrix.standardDifferential i)
        (Periods.PeriodMatrix.standardDifferential j)
      (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget band (((samples.traces.get position).get
        sheet).bottom.vertices.rest.length)).tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains
      (((samples.traces.get position).get sheet).bottom.point vertex))
    (side : ∀ first last, Paths.PreparedBoundarySegments.SameSide band.selection.sample.output.box
      (((samples.traces.get position).get sheet).bottom.point first)
      (((samples.traces.get position).get sheet).bottom.point last))
    (later : references.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea
      ((samples.samples.get position).get sheet) .bottom) ≤ areaTarget := by
  have bound := Hyperelliptic.Meshes.PuncturedGrid.NewtonBandPerimeterArea.SideGeometry.bottom_band_area_bound
    ((domains.get position).domain sheet)
    ((samples.traces.get position).get sheet) ((lengths.get position).get sheet) band
    ((RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget band _))
      ((RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget_padding_le band _)) references inside side
      later
    (cache.normalize.atDomain position sheet i) (cache.normalize.atDomain position sheet j)
    ((samples.samples.get position).get sheet)
  exact bound.trans (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.quadratic_paid radiusBudget band)

/-- The normalized original top perimeter area meets the paid Newton radius target.

The retained reference request must be sufficiently late, and all actual trace vertices must lie on a common side of the
extracted band. -/
theorem top_newton_area_paid (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples) (position :
      Fin base.faces.regulars.length) (sheet : Fin 2)
    (radiusBudget : RootContinuation.PreparedNewtonBandSamples.PreparedBandBudget
      (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient family) areaTarget radius)
    (band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radiusBudget.size)
    (references : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request
      (Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.top ((domains.get position).domain sheet)
        ((samples.traces.get position).get sheet))
      ((domains.get position).domain sheet) (Periods.PeriodMatrix.standardDifferential i)
        (Periods.PeriodMatrix.standardDifferential j)
      (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget band (((samples.traces.get position).get
        sheet).top.vertices.rest.length)).tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains
      (((samples.traces.get position).get sheet).top.point vertex))
    (side : ∀ first last, Paths.PreparedBoundarySegments.SameSide band.selection.sample.output.box
      (((samples.traces.get position).get sheet).top.point first)
      (((samples.traces.get position).get sheet).top.point last))
    (later : references.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea
      ((samples.samples.get position).get sheet) .top) ≤ areaTarget := by
  have bound := Hyperelliptic.Meshes.PuncturedGrid.NewtonBandPerimeterArea.SideGeometry.top_band_area_bound
    ((domains.get position).domain sheet)
    ((samples.traces.get position).get sheet) ((lengths.get position).get sheet) band
    ((RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget band _))
      ((RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget_padding_le band _)) references inside side
      later
    (cache.normalize.atDomain position sheet i) (cache.normalize.atDomain position sheet j)
    ((samples.samples.get position).get sheet)
  exact bound.trans (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.quadratic_paid radiusBudget band)

/-- The normalized original left perimeter area meets the paid Newton radius target.

The retained reference request must be sufficiently late, and all actual trace vertices must lie on a common side of the
extracted band. -/
theorem left_newton_area_paid (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples) (position :
      Fin base.faces.regulars.length) (sheet : Fin 2)
    (radiusBudget : RootContinuation.PreparedNewtonBandSamples.PreparedBandBudget
      (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient family) areaTarget radius)
    (band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radiusBudget.size)
    (references : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request
      (Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.left ((domains.get position).domain sheet)
        ((samples.traces.get position).get sheet))
      ((domains.get position).domain sheet) (Periods.PeriodMatrix.standardDifferential i)
        (Periods.PeriodMatrix.standardDifferential j)
      (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget band (((samples.traces.get position).get
        sheet).left.vertices.rest.length)).tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains
      (((samples.traces.get position).get sheet).left.point vertex))
    (side : ∀ first last, Paths.PreparedBoundarySegments.SameSide band.selection.sample.output.box
      (((samples.traces.get position).get sheet).left.point first)
      (((samples.traces.get position).get sheet).left.point last))
    (later : references.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea
      ((samples.samples.get position).get sheet) .left) ≤ areaTarget := by
  have bound := Hyperelliptic.Meshes.PuncturedGrid.NewtonBandPerimeterArea.SideGeometry.left_band_area_bound
    ((domains.get position).domain sheet)
    ((samples.traces.get position).get sheet) ((lengths.get position).get sheet) band
    ((RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget band _))
      ((RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget_padding_le band _)) references inside side
      later
    (cache.normalize.atDomain position sheet i) (cache.normalize.atDomain position sheet j)
    ((samples.samples.get position).get sheet)
  exact bound.trans (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.quadratic_paid radiusBudget band)

/-- The normalized original right perimeter area meets the paid Newton radius target.

The retained reference request must be sufficiently late, and all actual trace vertices must lie on a common side of the
extracted band. -/
theorem right_newton_area_paid (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples) (position :
      Fin base.faces.regulars.length) (sheet : Fin 2)
    (radiusBudget : RootContinuation.PreparedNewtonBandSamples.PreparedBandBudget
      (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient family) areaTarget radius)
    (band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radiusBudget.size)
    (references : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request
      (Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.right ((domains.get position).domain sheet)
        ((samples.traces.get position).get sheet))
      ((domains.get position).domain sheet) (Periods.PeriodMatrix.standardDifferential i)
        (Periods.PeriodMatrix.standardDifferential j)
      (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget band (((samples.traces.get position).get
        sheet).right.vertices.rest.length)).tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains
      (((samples.traces.get position).get sheet).right.point vertex))
    (side : ∀ first last, Paths.PreparedBoundarySegments.SameSide band.selection.sample.output.box
      (((samples.traces.get position).get sheet).right.point first)
      (((samples.traces.get position).get sheet).right.point last))
    (later : references.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea
      ((samples.samples.get position).get sheet) .right) ≤ areaTarget := by
  have bound := Hyperelliptic.Meshes.PuncturedGrid.NewtonBandPerimeterArea.SideGeometry.right_band_area_bound
    ((domains.get position).domain sheet)
    ((samples.traces.get position).get sheet) ((lengths.get position).get sheet) band
    ((RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget band _))
      ((RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.sideBudget_padding_le band _)) references inside side
      later
    (cache.normalize.atDomain position sheet i) (cache.normalize.atDomain position sheet j)
    ((samples.samples.get position).get sheet)
  exact bound.trans (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.quadratic_paid radiusBudget band)

end CenteredPerimeters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPaidPerimeters
