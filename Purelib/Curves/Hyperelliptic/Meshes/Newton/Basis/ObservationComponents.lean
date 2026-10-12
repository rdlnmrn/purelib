module
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CorrectionReindex

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests

public section

/-! Reindex common-basis component sides onto the actual observation exterior. -/
namespace Purelib.Curves.Hyperelliptic.Meshes

open Purelib

open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation SurfaceComponent AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence
  (oriented)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius
    : Data.Rat.Fraction.Rational} {grid : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid
    preparation target radius}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {stage : Nat} {cache : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
    stage}

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value)

variable {observations : Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original}
  {partitions : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {coarse : (sheet : Fin 2) → Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error
    : Data.Rat.Fraction.Rational}
  {requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error} {traces
    : Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  (samples : Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests traces
    cache coefficients)
  {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- The complete observed side area at one face and sheet, before orientation. -/
@[expose] def Newton.Basis.ObservationComponents.observationSide (position : Fin grid.faces.regulars.length) (sheet :
  Fin 2) : GridLiftedDualSteps.GridSide
  → Data.Gaussian.Basic.Canonical
  | .bottom => ((samples.get sheet).get position).bottom.originalArea
  | .right => ((samples.get sheet).get position).right.originalArea
  | .top => ((samples.get sheet).get position).top.originalArea
  | .left => ((samples.get sheet).get position).left.originalArea

/-- Read a prepared component on the very observation samples used by the sewn surface. -/
@[expose] def
  PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.observedSides
  {program : PeriodPrograms.ExteriorProgram lifted differential}
    (prepared : ExteriorProgram.SurfacePreparation regular domains program) : Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map fun occurrence => SideOccurrence.oriented
    occurrence.sideOccurrence
    (Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationComponents.observationSide samples
      occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side))

/-- Reindex all component side areas onto the actual Newton exterior component. -/
theorem
  PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.observedSides_sum
  (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.components.map (fun component =>
      component.prepared.observedSides samples)) =
      PerimeterSamples.componentBoundary samples neighbors .exterior := by
  have indexed := prepared.oriented_sum_eq_component neighbors
    (Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationComponents.observationSide samples)
  have mapped := Data.Gaussian.Norm.Sum.Indexed.sumFin_map prepared.occurrences (fun occurrence =>
    SideOccurrence.oriented occurrence.sideOccurrence
    (Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationComponents.observationSide samples
      occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side))
  have all := (Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_flatMap prepared.components
    (fun component => component.prepared.occurrences) (fun occurrence => SideOccurrence.oriented
      occurrence.sideOccurrence
      (Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationComponents.observationSide samples
        occurrence.sideOccurrence.position
        occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side))).symm
  rw [← prepared.occurrences_eq] at all
  apply (all.trans (mapped.symm.trans indexed)).trans
  rfl

end Purelib.Curves.Hyperelliptic.Meshes
