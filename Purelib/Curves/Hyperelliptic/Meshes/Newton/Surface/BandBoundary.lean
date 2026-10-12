module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterLengths
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
public import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BandArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterLengths

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate

@[expose] public section

/-! Conjugate energy bounds on certified band sides of the observation surface. -/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces (Centered traceValues)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry (SideBoundary OnSide)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : SurfacePartitions observations grid} {coarse :
    SurfaceMeshes partitions domains sheet}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions coarse fixed error}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {assemblies : ExteriorRequest.Assemblies energy
    cache coefficients} {perimeters : Perimeters
    assemblies}
  {position : Fin grid.faces.regulars.length}

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

section

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample area)
open _root_.Purelib.Data.Gaussian.Basic (conj)

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces

/-- Select the actual concatenated perimeter without reversing its cached owners. -/
def sideTrace (traces : PerimeterTraces.FacePerimeterTraces energy position) : GridLiftedDualSteps.GridSide →
    JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry)
  | .bottom => traces.bottom
  | .right => traces.right
  | .top => traces.top
  | .left => traces.left

/-- The certified original face-side geometry of the retained perimeter trace. -/
def sideGeometry (traces : PerimeterTraces.FacePerimeterTraces energy position) (side : GridLiftedDualSteps.GridSide) :
    SidePreparation.SideGeometry (domains.get position).models
      (fun vertex => ((traces.sideTrace side).indexed vertex).point) := by
  cases side with
  | bottom => exact FacePerimeterTraces.bottomGeometry traces
  | right => exact FacePerimeterTraces.rightGeometry traces
  | top => exact FacePerimeterTraces.topGeometry traces
  | left => exact FacePerimeterTraces.leftGeometry traces

/-- Every actual vertex of the retained perimeter trace lies on its specified original face side. -/
theorem side_onSide (traces : PerimeterTraces.FacePerimeterTraces energy position) (side : GridLiftedDualSteps.GridSide)
    (vertex : Fin ((traces.sideTrace side).rest.length + 1)) :
    SideBoundaryGeometry.OnSide (grid.faces.regulars[position.val]'position.isLt).cell.box side
      ((traces.sideTrace side).indexed vertex).point := by
  refine ⟨(traces.sideGeometry side).inside vertex, ?_⟩
  cases side with
  | bottom => exact FacePerimeterTraces.bottom_height traces vertex
  | right => exact FacePerimeterTraces.right_horizontal traces vertex
  | top => exact FacePerimeterTraces.top_height traces vertex
  | left => exact FacePerimeterTraces.left_horizontal traces vertex

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered

/-- Read the already cached centered sample for the requested side. -/
def sideSample
    {traces : PerimeterTraces.FacePerimeterTraces energy position}
    (samples : FacePerimeterTraces.Centered traces cache coefficients) :
    (side : GridLiftedDualSteps.GridSide) → CenteredBilinearPath.Sample (FacePerimeterTraces.traceValues cache
      coefficients (traces.sideTrace side))
  | .bottom => samples.bottom
  | .right => samples.right
  | .top => samples.top
  | .left => samples.left

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered

open Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies (PreparedBandFamily DifferentialFamily)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {bandAmbient : Purelib.Geometry.Rational.Box} {current :
  Purelib.RootIsolation.State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : Purelib.Riemann.RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {family : DifferentialFamily profile genus}
  {periodTarget areaTarget : Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces

/-- Bound a certified side by the already selected band radius. -/
theorem boundary_energy_bound
    (traces : PerimeterTraces.FacePerimeterTraces energy position) (side : GridLiftedDualSteps.GridSide)
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radius)
    (boundary : SideBoundaryGeometry.SideBoundary (grid.faces.regulars[position.val]'position.isLt).cell.box
      band.selection.sample.output.box side)
    (request : FacePerimeterTraces.SideRequest (traces.sideGeometry side)
      (PreparedBandFamily.sideBudget band (traces.sideTrace side).rest.length).tolerance)
    (later : request.index ≤ stage) (readings : BasisReadings (traces.sideTrace side) cache)
    (sample : CenteredBilinearPath.Sample (FacePerimeterTraces.traceValues cache coefficients (traces.sideTrace side)))
      :
    Data.Gaussian.Norm.Basic.normSq sample.centeredArea ≤
      (genus : Fraction.Rational)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients^2 *
        (PreparedBandFamily.areaCoefficient family * band.selection.sample.output.radius^2) := by
  have inside := fun vertex => boundary.contains (traces.side_onSide side vertex)
  have same := fun first last => boundary.sameSide
    (grid.faces.regulars[position.val]'position.isLt).cell.box_proper
    (traces.side_onSide side first) (traces.side_onSide side last)
  cases side with
  | bottom =>
      exact request.band_energy_bound band inside same later readings sample
        (FacePerimeterTraces.bottomLengths traces) (FacePerimeterTraces.bottom_movement traces
          (FacePerimeterTraces.bottomLengths traces))
        (FacePerimeterTraces.band_length_re band (FacePerimeterTraces.bottomLengths traces) inside)
  | right =>
      exact request.band_energy_bound band inside same later readings sample
        (FacePerimeterTraces.rightLengths traces) (FacePerimeterTraces.right_movement traces
          (FacePerimeterTraces.rightLengths traces))
        (FacePerimeterTraces.band_length_im band (FacePerimeterTraces.rightLengths traces) inside)
  | top =>
      exact request.band_energy_bound band inside same later readings sample
        (FacePerimeterTraces.topLengths traces) (FacePerimeterTraces.top_movement traces (FacePerimeterTraces.topLengths
          traces))
        (FacePerimeterTraces.band_length_re band (FacePerimeterTraces.topLengths traces) inside)
  | left =>
      exact request.band_energy_bound band inside same later readings sample
        (FacePerimeterTraces.leftLengths traces) (FacePerimeterTraces.left_movement traces
          (FacePerimeterTraces.leftLengths traces))
        (FacePerimeterTraces.band_length_im band (FacePerimeterTraces.leftLengths traces) inside)

/-- An actual band-boundary certificate supplies both containment and the same-side condition for every intermediate
owned perimeter vertex. -/
theorem boundary_energy_paid
    (traces : PerimeterTraces.FacePerimeterTraces energy position) (side : GridLiftedDualSteps.GridSide)
    (radiusBudget : PreparedNewtonBandSamples.PreparedBandBudget (PreparedBandFamily.areaCoefficient family) areaTarget
      radius)
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radiusBudget.size)
    (boundary : SideBoundaryGeometry.SideBoundary (grid.faces.regulars[position.val]'position.isLt).cell.box
      band.selection.sample.output.box side)
    (request : FacePerimeterTraces.SideRequest (traces.sideGeometry side)
      (PreparedBandFamily.sideBudget band (traces.sideTrace side).rest.length).tolerance)
    (later : request.index ≤ stage) (readings : BasisReadings (traces.sideTrace side) cache)
    (sample : CenteredBilinearPath.Sample (FacePerimeterTraces.traceValues cache coefficients (traces.sideTrace side)))
      :
    Data.Gaussian.Norm.Basic.normSq sample.centeredArea ≤
      (genus : Fraction.Rational)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients^2 * areaTarget := by
  have inside := fun vertex => boundary.contains (traces.side_onSide side vertex)
  have same := fun first last => boundary.sameSide
    (grid.faces.regulars[position.val]'position.isLt).cell.box_proper
    (traces.side_onSide side first) (traces.side_onSide side last)
  cases side with
  | bottom =>
      exact request.band_energy_paid radiusBudget band inside same later readings sample
        (FacePerimeterTraces.bottomLengths traces) (FacePerimeterTraces.bottom_movement traces
          (FacePerimeterTraces.bottomLengths traces))
        (FacePerimeterTraces.band_length_re band (FacePerimeterTraces.bottomLengths traces) inside)
  | right =>
      exact request.band_energy_paid radiusBudget band inside same later readings sample
        (FacePerimeterTraces.rightLengths traces) (FacePerimeterTraces.right_movement traces
          (FacePerimeterTraces.rightLengths traces))
        (FacePerimeterTraces.band_length_im band (FacePerimeterTraces.rightLengths traces) inside)
  | top =>
      exact request.band_energy_paid radiusBudget band inside same later readings sample
        (FacePerimeterTraces.topLengths traces) (FacePerimeterTraces.top_movement traces (FacePerimeterTraces.topLengths
          traces))
        (FacePerimeterTraces.band_length_re band (FacePerimeterTraces.topLengths traces) inside)
  | left =>
      exact request.band_energy_paid radiusBudget band inside same later readings sample
        (FacePerimeterTraces.leftLengths traces) (FacePerimeterTraces.left_movement traces
          (FacePerimeterTraces.leftLengths traces))
        (FacePerimeterTraces.band_length_im band (FacePerimeterTraces.leftLengths traces) inside)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces

end
end
