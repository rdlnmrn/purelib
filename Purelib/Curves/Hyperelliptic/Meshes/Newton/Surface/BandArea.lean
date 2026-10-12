module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.TraceLengths
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SideArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
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
import Purelib.Data.Vector.Basic
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces

open Purelib.Data.Rat

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.TraceLengths

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate

@[expose] public section

/-! Requested homogeneous energy-area bounds on the actual Newton band.
The complete owned trace, its physical length, and all pair readings remain
those of the observation surface. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces

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
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (BasisReadings)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces (pairValues traceValues
  centered_combination_bound)
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

namespace FacePerimeterTraces

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample area)
open _root_.Purelib.Data.Gaussian.Basic (conj)

variable {trace : Purelib.Integration.Path.JoinedTrace.VertexTrace
  (OwnedVertex ((domains.get position).domain
  sheet).geometry)}

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable (geometry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry (domains.get
  position).models (fun vertex => (trace.indexed vertex).point))

open Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies (PreparedBandFamily DifferentialFamily)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandBudget)

variable {bandAmbient : Purelib.Geometry.Rational.Box} {current :
  Purelib.RootIsolation.State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : Purelib.Riemann.RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {family : DifferentialFamily profile genus}
  {periodTarget radius areaTarget : Rational}

/-- The total of the original retained nonnegative coordinate lengths is nonnegative. -/
private theorem lengths_nonnegative {coordinate : RectangularOwnedTriangulation.OwnedVertex ((domains.get
  position).domain sheet).geometry → Fraction.Rational}
    (lengths : VertexTrace.Lengths trace coordinate) : 0 ≤ lengths.total := by
  rw [lengths.total_eq]
  have bound := Order.Positivity.sumFin_mono (fun _ : Fin trace.rest.length => (0 : Fraction.Rational))
    (fun edge => lengths.values edge) lengths.nonnegative
  exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound

/-- The total retained real-coordinate trace length inside the actual selected Newton band is at most four times its
radius. -/
theorem band_length_re (band : PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radius)
    (lengths : VertexTrace.Lengths trace (fun owner => owner.point.re))
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (trace.indexed vertex).point) :
    lengths.total ≤ 4 * band.selection.sample.output.radius := by
  have firstInside := inside 0
  have lastInside := inside (Fin.last trace.rest.length)
  rw [show trace.indexed (Fin.last trace.rest.length) = trace.last from
    DyadicTrace.indexed_last _ _] at lastInside
  change band.selection.sample.output.box.Contains trace.first.point at firstInside
  rw [lengths.endpoints]
  exact (Fraction.Order.Arithmetic.sub_le_sub_direct lastInside.2.1 firstInside.1).trans
    (PreparedBandFamily.widthX_le band)

/-- The total retained imaginary-coordinate trace length inside the actual selected Newton band is at most four times
its radius. -/
theorem band_length_im (band : PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radius)
    (lengths : VertexTrace.Lengths trace (fun owner => owner.point.im))
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (trace.indexed vertex).point) :
    lengths.total ≤ 4 * band.selection.sample.output.radius := by
  have firstInside := inside 0
  have lastInside := inside (Fin.last trace.rest.length)
  rw [show trace.indexed (Fin.last trace.rest.length) = trace.last from
    DyadicTrace.indexed_last _ _] at lastInside
  change band.selection.sample.output.box.Contains trace.first.point at firstInside
  rw [lengths.endpoints]
  exact (Fraction.Order.Arithmetic.sub_le_sub_direct lastInside.2.2.2 firstInside.2.2.1).trans
    (PreparedBandFamily.widthY_le band)

namespace SideRequest

variable {geometry}

/-- The actual selected radius controls each conjugate side area before the pre-grid allocation is paid. -/
theorem band_pair_bound
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radius)
    (request : FacePerimeterTraces.SideRequest geometry (PreparedBandFamily.sideBudget band
      trace.rest.length).tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (trace.indexed vertex).point)
    (side : ∀ first last, PreparedBoundarySegments.SameSide band.selection.sample.output.box (trace.indexed first).point
      (trace.indexed last).point)
    (later : request.index ≤ stage) (readings : BasisReadings trace cache) (first second : Fin
      genus)
    (sample : CenteredBilinearPath.Sample (FacePerimeterTraces.pairValues cache trace first second))
    {coordinate : RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry →
      Fraction.Rational}
    (lengths : VertexTrace.Lengths trace coordinate)
    (movement : ∀ edge : Fin trace.rest.length,
      Data.Gaussian.Norm.Basic.normSq ((trace.indexed edge.succ).point - (trace.indexed edge.castSucc).point) =
        (lengths.values edge)^2)
    (lengthLe : lengths.total ≤ 4 * band.selection.sample.output.radius) :
    Data.Gaussian.Norm.Basic.normSq sample.centeredArea ≤ PreparedBandFamily.areaCoefficient family *
      band.selection.sample.output.radius^2 := by
  have bound := request.pair_area_bound (PreparedBandFamily.sideBudget band trace.rest.length) first second
    (band.forDifferential first) (band.forDifferential second) inside side inside side
    (PreparedBandFamily.pairedDensity_nonnegative band first second) (PreparedBandFamily.first_density_le band first
      second)
    (PreparedBandFamily.second_density_le band first second) later readings sample lengths movement
  have rate := PreparedBandFamily.area_rate band first second (PreparedBandFamily.sideBudget band trace.rest.length)
    (PreparedBandFamily.sideBudget_padding_le band trace.rest.length)
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces.lengths_nonnegative lengths)
      lengthLe
  exact bound.trans rate

/-- A prepared radius pays the complete conjugate side area, for every pair at the request's common numerical stage. The
actual band-side condition is retained; containment in a band alone does not imply it. -/
theorem band_pair_paid
    (radiusBudget : PreparedNewtonBandSamples.PreparedBandBudget (PreparedBandFamily.areaCoefficient family) areaTarget
      radius)
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radiusBudget.size)
    (request : FacePerimeterTraces.SideRequest geometry (PreparedBandFamily.sideBudget band
      trace.rest.length).tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (trace.indexed vertex).point)
    (side : ∀ first last, PreparedBoundarySegments.SameSide band.selection.sample.output.box (trace.indexed first).point
      (trace.indexed last).point)
    (later : request.index ≤ stage) (readings : BasisReadings trace cache) (first second : Fin
      genus)
    (sample : CenteredBilinearPath.Sample (FacePerimeterTraces.pairValues cache trace first second))
    {coordinate : RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry →
      Fraction.Rational}
    (lengths : VertexTrace.Lengths trace coordinate)
    (movement : ∀ edge : Fin trace.rest.length,
      Data.Gaussian.Norm.Basic.normSq ((trace.indexed edge.succ).point - (trace.indexed edge.castSucc).point) =
        (lengths.values edge)^2)
    (lengthLe : lengths.total ≤ 4 * band.selection.sample.output.radius) :
    Data.Gaussian.Norm.Basic.normSq sample.centeredArea ≤ areaTarget :=
  (request.band_pair_bound band inside side later readings first second sample lengths movement lengthLe).trans
    (PreparedBandFamily.quadratic_paid radiusBudget band)

/-- Homogeneous bound using the actual radius of an already selected band. -/
theorem band_energy_bound
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radius)
    (request : FacePerimeterTraces.SideRequest geometry (PreparedBandFamily.sideBudget band
      trace.rest.length).tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (trace.indexed vertex).point)
    (side : ∀ first last, PreparedBoundarySegments.SameSide band.selection.sample.output.box (trace.indexed first).point
      (trace.indexed last).point)
    (later : request.index ≤ stage) (readings : BasisReadings trace cache)
    (combined : CenteredBilinearPath.Sample (FacePerimeterTraces.traceValues cache coefficients trace))
    {coordinate : RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry →
      Fraction.Rational}
    (lengths : VertexTrace.Lengths trace coordinate)
    (movement : ∀ edge : Fin trace.rest.length,
      Data.Gaussian.Norm.Basic.normSq ((trace.indexed edge.succ).point - (trace.indexed edge.castSucc).point) =
        (lengths.values edge)^2)
    (lengthLe : lengths.total ≤ 4 * band.selection.sample.output.radius) :
    Data.Gaussian.Norm.Basic.normSq combined.centeredArea ≤
      (genus : Fraction.Rational)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients^2 *
        (PreparedBandFamily.areaCoefficient family * band.selection.sample.output.radius^2) := by
  let pairs := readings.pairSamples
  apply FacePerimeterTraces.centered_combination_bound trace combined (fun first second => (pairs.get first).get second)
  intro first second
  exact request.band_pair_bound band inside side later readings first second
    ((pairs.get first).get second) lengths movement lengthLe

/-- The radius and numerical request are independent of the coefficients. The squared area error retains the required
homogeneous quadratic factor. -/
theorem band_energy_paid
    (radiusBudget : PreparedNewtonBandSamples.PreparedBandBudget (PreparedBandFamily.areaCoefficient family) areaTarget
      radius)
    (band : PreparedNewtonBandFamilies.PreparedBandFamily family periodTarget radiusBudget.size)
    (request : FacePerimeterTraces.SideRequest geometry (PreparedBandFamily.sideBudget band
      trace.rest.length).tolerance)
    (inside : ∀ vertex, band.selection.sample.output.box.Contains (trace.indexed vertex).point)
    (side : ∀ first last, PreparedBoundarySegments.SameSide band.selection.sample.output.box (trace.indexed first).point
      (trace.indexed last).point)
    (later : request.index ≤ stage) (readings : BasisReadings trace cache)
    (combined : CenteredBilinearPath.Sample (FacePerimeterTraces.traceValues cache coefficients trace))
    {coordinate : RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry →
      Fraction.Rational}
    (lengths : VertexTrace.Lengths trace coordinate)
    (movement : ∀ edge : Fin trace.rest.length,
      Data.Gaussian.Norm.Basic.normSq ((trace.indexed edge.succ).point - (trace.indexed edge.castSucc).point) =
        (lengths.values edge)^2)
    (lengthLe : lengths.total ≤ 4 * band.selection.sample.output.radius) :
    Data.Gaussian.Norm.Basic.normSq combined.centeredArea ≤
      (genus : Fraction.Rational)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients^2 * areaTarget := by
  let pairs := readings.pairSamples
  apply FacePerimeterTraces.centered_combination_bound trace combined (fun first second => (pairs.get first).get second)
  intro first second
  exact request.band_pair_paid radiusBudget band inside side later readings first second
    ((pairs.get first).get second) lengths movement lengthLe

end SideRequest
end FacePerimeterTraces
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
