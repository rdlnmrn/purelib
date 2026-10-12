module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Acquire the root-side source readings and radial fan data at computed finite stages. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceRootReadings

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Normalization.InverseRootPolynomial.Coordinate}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured} {differential : Hyperelliptic.Differentials.Basic.Differential
    genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedSurfaceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes

variable {whole :
  PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  {selected : PuncturedGrid.Exterior.SourceCuts whole previous}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared} {index :
    Nat} {inputs : retained.Inputs index}
  {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  (schedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    selected request retained inputs requested minimum)

variable {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {partitions :
  Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCoarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {surfaceFixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
    {surfaceTarget : Normalization.InverseRootPolynomial.Coordinate}
  (initialSurface : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests surfaceCoarse surfaceFixed
    surfaceTarget)

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
  (energyTarget coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (traceFloor sourceFloor : Nat)

namespace SourceSurfaceAcquisition
variable {schedules initialSurface basis energyTarget coefficientTarget traceFloor sourceFloor}
  (acquired : SourceSurfaceAcquisition
    schedules initialSurface basis energyTarget coefficientTarget traceFloor sourceFloor)
  {box : Rational.Box}
  (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential acquired.index box)
  (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap acquired.index
    box)
  (energyFloor : Nat)

set_option genInjectivity false in
/-- Retain the numerical source readings, radial fans and parameters at their computed stages. -/
structure RootReadings where
  /-- The original source plans using the retained cap sample, basis polynomials and minimum depth. -/ plans :
    acquired.request.Plans capSample polynomials minimum
  /-- The computed numerical stage paying the retained source plans. -/ readingIndex : Nat
  /-- The reading stage is exactly the stage calculated by the original source request. -/ reading_eq : readingIndex =
    acquired.request.readingStage plans
  /-- The acquired numerical source readings on the exact retained input bank and plans. -/ readings :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    acquired.request.schedule.bank plans acquired.source.inputs readingIndex
  /-- The prepared radial fans indexed by the retained source readings and energy floor. -/ fans :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.FanPreparation acquired.request
    plans acquired.source.inputs readings energyFloor
  /-- The common radial depth computed from these exact prepared fans. -/ radialDepth : Nat
  /-- The radial depth is exactly the finite maximum computed by the retained fan bank. -/ radial_eq : radialDepth =
    fans.depth retained.anchors retained.sources acquired.request.schedule.bank plans acquired.source.inputs readings
  /-- The cached radial subdivision parameters at the computed common depth. -/ parameters :
    Path.Dyadic.RadialTriangles.Parameters radialDepth

constructive_injectivity RootReadings

namespace RootReadings

/-- Source and radial stages are computed once before any coefficient vector is evaluated. -/
@[expose] def build (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    Hyperelliptic.Meshes.Newton.Basis.SourceRootReadings.RequestedSurfaceRuns.SourceSurfaceAcquisition.RootReadings
      acquired capSample polynomials energyFloor := by
  let plans := acquired.request.plans capSample polynomials minimum
  let readingIndex := acquired.request.readingStage plans
  let readings := acquired.request.acquire capSample polynomials plans acquired.source.inputs branch acquired.request_le
    readingIndex (Nat.le_refl _)
  let fans := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.prepareFans
    acquired.request plans acquired.source.inputs readings energyFloor
  let radialDepth := fans.depth retained.anchors retained.sources acquired.request.schedule.bank plans
    acquired.source.inputs readings
  exact ⟨plans, readingIndex, rfl, readings, fans, radialDepth, rfl, Path.Dyadic.RadialTriangles.Parameters.build
    radialDepth⟩

variable {acquired capSample polynomials energyFloor}
  (readings :
    SourceSurfaceAcquisition.RootReadings
    acquired capSample polynomials energyFloor)

/-- Evaluate coefficients on the retained source bank and radial parameters. -/
@[expose] def sample (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (_branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled readings.fans coefficients
      readings.radialDepth :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.sample acquired.request
    readings.plans acquired.source.inputs readings.readings readings.fans coefficients readings.parameters _branch
    readings.reading_eq.symm.le readings.radial_eq.symm.le

end RootReadings
end SourceSurfaceAcquisition
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceRootReadings
