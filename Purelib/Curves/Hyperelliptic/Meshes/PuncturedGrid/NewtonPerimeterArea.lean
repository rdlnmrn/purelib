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
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Requested full Newton area bounds on the actual normalized perimeter
bank. The finite prefix and edge requests build both differential estimates;
no caller primitive magnitude or increment certificate is required. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPerimeterArea

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

/-- The normalized original bottom perimeter area satisfies its requested full Newton density bound.

The two retained differential bands supply side membership and density estimates; the actual rectangle side length and
allocated junction allowance determine the squared length factor. -/
theorem bottom_newton_area_bound (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples) (position :
      Fin base.faces.regulars.length) (sheet : Fin 2)
    {allowance density : Fraction.Rational}
    (budget : Path.NoisyPathArea.LengthErrorBudget (((samples.traces.get position).get
      sheet).bottom.vertices.rest.length) allowance)
    (references : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request
      (Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.bottom ((domains.get position).domain sheet)
        ((samples.traces.get position).get sheet))
      ((domains.get position).domain sheet) (Periods.PeriodMatrix.standardDifferential i)
        (Periods.PeriodMatrix.standardDifferential j)
      budget.tolerance)
    {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile
      (Periods.PeriodMatrix.standardDifferential i).exponent}
    {rightProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile
      (Periods.PeriodMatrix.standardDifferential j).exponent}
    {leftTarget rightTarget : Fraction.Rational}
    (leftBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains
      (((samples.traces.get position).get sheet).bottom.point vertex))
    (leftSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide leftBand.sample.output.box
      (((samples.traces.get position).get sheet).bottom.point first)
      (((samples.traces.get position).get sheet).bottom.point last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains
      (((samples.traces.get position).get sheet).bottom.point vertex))
    (rightSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide rightBand.sample.output.box
      (((samples.traces.get position).get sheet).bottom.point first)
      (((samples.traces.get position).get sheet).bottom.point last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile
      leftBand.error ≤ density)
    (rightDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile
      rightBand.error ≤ density)
    (later : references.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea
      ((samples.samples.get position).get sheet) .bottom) ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) * (4 * density + 3) *
        ((base.faces.regulars[position.val]'position.isLt).cell.box.xUpper -
          (base.faces.regulars[position.val]'position.isLt).cell.box.xLower + allowance)^2 := by
  exact Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea.SideGeometry.bottom_area_bound ((domains.get
    position).domain sheet)
    ((samples.traces.get position).get sheet) ((lengths.get position).get sheet) budget references
    leftBand rightBand leftInside leftSide rightInside rightSide densityNonnegative leftDensity rightDensity later
    (cache.normalize.atDomain position sheet i) (cache.normalize.atDomain position sheet j)
    ((samples.samples.get position).get sheet)

/-- The normalized original top perimeter area satisfies its requested full Newton density bound.

The two retained differential bands supply side membership and density estimates; the actual rectangle side length and
allocated junction allowance determine the squared length factor. -/
theorem top_newton_area_bound (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples) (position :
      Fin base.faces.regulars.length) (sheet : Fin 2)
    {allowance density : Fraction.Rational}
    (budget : Path.NoisyPathArea.LengthErrorBudget (((samples.traces.get position).get sheet).top.vertices.rest.length)
      allowance)
    (references : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request
      (Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.top ((domains.get position).domain sheet)
        ((samples.traces.get position).get sheet))
      ((domains.get position).domain sheet) (Periods.PeriodMatrix.standardDifferential i)
        (Periods.PeriodMatrix.standardDifferential j)
      budget.tolerance)
    {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile
      (Periods.PeriodMatrix.standardDifferential i).exponent}
    {rightProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile
      (Periods.PeriodMatrix.standardDifferential j).exponent}
    {leftTarget rightTarget : Fraction.Rational}
    (leftBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains
      (((samples.traces.get position).get sheet).top.point vertex))
    (leftSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide leftBand.sample.output.box
      (((samples.traces.get position).get sheet).top.point first)
      (((samples.traces.get position).get sheet).top.point last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains
      (((samples.traces.get position).get sheet).top.point vertex))
    (rightSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide rightBand.sample.output.box
      (((samples.traces.get position).get sheet).top.point first)
      (((samples.traces.get position).get sheet).top.point last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile
      leftBand.error ≤ density)
    (rightDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile
      rightBand.error ≤ density)
    (later : references.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea
      ((samples.samples.get position).get sheet) .top) ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) * (4 * density + 3) *
        ((base.faces.regulars[position.val]'position.isLt).cell.box.xUpper -
          (base.faces.regulars[position.val]'position.isLt).cell.box.xLower + allowance)^2 := by
  exact Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea.SideGeometry.top_area_bound ((domains.get
    position).domain sheet)
    ((samples.traces.get position).get sheet) ((lengths.get position).get sheet) budget references
    leftBand rightBand leftInside leftSide rightInside rightSide densityNonnegative leftDensity rightDensity later
    (cache.normalize.atDomain position sheet i) (cache.normalize.atDomain position sheet j)
    ((samples.samples.get position).get sheet)

/-- The normalized original left perimeter area satisfies its requested full Newton density bound.

The two retained differential bands supply side membership and density estimates; the actual rectangle side length and
allocated junction allowance determine the squared length factor. -/
theorem left_newton_area_bound (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples) (position :
      Fin base.faces.regulars.length) (sheet : Fin 2)
    {allowance density : Fraction.Rational}
    (budget : Path.NoisyPathArea.LengthErrorBudget (((samples.traces.get position).get sheet).left.vertices.rest.length)
      allowance)
    (references : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request
      (Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.left ((domains.get position).domain sheet)
        ((samples.traces.get position).get sheet))
      ((domains.get position).domain sheet) (Periods.PeriodMatrix.standardDifferential i)
        (Periods.PeriodMatrix.standardDifferential j)
      budget.tolerance)
    {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile
      (Periods.PeriodMatrix.standardDifferential i).exponent}
    {rightProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile
      (Periods.PeriodMatrix.standardDifferential j).exponent}
    {leftTarget rightTarget : Fraction.Rational}
    (leftBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains
      (((samples.traces.get position).get sheet).left.point vertex))
    (leftSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide leftBand.sample.output.box
      (((samples.traces.get position).get sheet).left.point first)
      (((samples.traces.get position).get sheet).left.point last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains
      (((samples.traces.get position).get sheet).left.point vertex))
    (rightSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide rightBand.sample.output.box
      (((samples.traces.get position).get sheet).left.point first)
      (((samples.traces.get position).get sheet).left.point last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile
      leftBand.error ≤ density)
    (rightDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile
      rightBand.error ≤ density)
    (later : references.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea
      ((samples.samples.get position).get sheet) .left) ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) * (4 * density + 3) *
        ((base.faces.regulars[position.val]'position.isLt).cell.box.yUpper -
          (base.faces.regulars[position.val]'position.isLt).cell.box.yLower + allowance)^2 := by
  exact Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea.SideGeometry.left_area_bound ((domains.get
    position).domain sheet)
    ((samples.traces.get position).get sheet) ((lengths.get position).get sheet) budget references
    leftBand rightBand leftInside leftSide rightInside rightSide densityNonnegative leftDensity rightDensity later
    (cache.normalize.atDomain position sheet i) (cache.normalize.atDomain position sheet j)
    ((samples.samples.get position).get sheet)

/-- The normalized original right perimeter area satisfies its requested full Newton density bound.

The two retained differential bands supply side membership and density estimates; the actual rectangle side length and
allocated junction allowance determine the squared length factor. -/
theorem right_newton_area_bound (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples) (position :
      Fin base.faces.regulars.length) (sheet : Fin 2)
    {allowance density : Fraction.Rational}
    (budget : Path.NoisyPathArea.LengthErrorBudget (((samples.traces.get position).get
      sheet).right.vertices.rest.length) allowance)
    (references : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request
      (Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.right ((domains.get position).domain sheet)
        ((samples.traces.get position).get sheet))
      ((domains.get position).domain sheet) (Periods.PeriodMatrix.standardDifferential i)
        (Periods.PeriodMatrix.standardDifferential j)
      budget.tolerance)
    {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile
      (Periods.PeriodMatrix.standardDifferential i).exponent}
    {rightProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile
      (Periods.PeriodMatrix.standardDifferential j).exponent}
    {leftTarget rightTarget : Fraction.Rational}
    (leftBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains
      (((samples.traces.get position).get sheet).right.point vertex))
    (leftSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide leftBand.sample.output.box
      (((samples.traces.get position).get sheet).right.point first)
      (((samples.traces.get position).get sheet).right.point last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains
      (((samples.traces.get position).get sheet).right.point vertex))
    (rightSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide rightBand.sample.output.box
      (((samples.traces.get position).get sheet).right.point first)
      (((samples.traces.get position).get sheet).right.point last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile
      leftBand.error ≤ density)
    (rightDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile
      rightBand.error ≤ density)
    (later : references.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea
      ((samples.samples.get position).get sheet) .right) ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) * (4 * density + 3) *
        ((base.faces.regulars[position.val]'position.isLt).cell.box.yUpper -
          (base.faces.regulars[position.val]'position.isLt).cell.box.yLower + allowance)^2 := by
  exact Hyperelliptic.Meshes.PuncturedGrid.NewtonDomainPerimeterArea.SideGeometry.right_area_bound ((domains.get
    position).domain sheet)
    ((samples.traces.get position).get sheet) ((lengths.get position).get sheet) budget references
    leftBand rightBand leftInside leftSide rightInside rightSide densityNonnegative leftDensity rightDensity later
    (cache.normalize.atDomain position sheet i) (cache.normalize.atDomain position sheet j)
    ((samples.samples.get position).get sheet)

end CenteredPerimeters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPerimeterArea
