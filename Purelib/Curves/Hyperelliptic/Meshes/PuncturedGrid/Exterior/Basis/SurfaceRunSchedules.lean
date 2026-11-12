module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRefinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentCapacityTransport
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunDepthSynchronization
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Prepare all occurrence requests on one retained surface and refine their mesh. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedSurfaceRuns

variable {whole :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  (selected : SourceCuts whole previous)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    InverseRootPolynomial.Coordinate}
  (request : TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)

/-- Read each retained occurrence physical side capacity from its actual requested mesh. -/
def capacities (outer : Fin prepared.occurrences.length) : Nat :=
  SharedOccurrenceRuns.sideCapacity outer (mesh
    := RequestedOccurrenceRuns.mesh outer selected
    request)

variable (retained : Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)

/-- The dependent occurrence schedule vector indexed by the exact retained mesh capacities and input bank. -/
def Schedules (requested : InverseRootPolynomial.Coordinate) (minimum : Nat) :=
  RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
    retained inputs
    (RequestedSurfaceRuns.capacities (prepared :=
    prepared) selected request) requested minimum

/-- Each request uses the actual side capacity and the same retained source inputs. -/
def prepare (requested : InverseRootPolynomial.Coordinate) (positive : 0 < requested) (minimum : Nat) :
    Schedules selected
      request retained inputs requested minimum :=
  Data.Vector.DependentVector.ofFn fun outer =>
    RequestedOccurrenceRuns.parentSchedule
      retained inputs outer selected request requested positive minimum

variable {selected request retained inputs} {requested : InverseRootPolynomial.Coordinate} {minimum : Nat}
  (schedules :
    Schedules
    selected request retained inputs requested minimum)

/-- Changing only the dyadic depth preserves the computed parent requests. -/
def atDepth (depth : Nat) (later : request.depth ≤ depth) :
    Schedules selected
      (request.atDepth depth later) retained inputs requested minimum :=
  Data.Vector.DependentVector.ofFn fun outer =>
    ParentCapacityTransport.CommonBasisPreparation.ParentRunSchedule.castCapacity
    (OccurrenceRefinement.RequestedOccurrenceRuns.atDepth_capacity
      outer selected request depth later).symm (schedules.get outer)

/-- Refining the physical mesh preserves each retained occurrence request depth. -/
theorem atDepth_depth (depth : Nat) (later : request.depth ≤ depth)
    (outer : Fin prepared.occurrences.length) :
    ((RequestedSurfaceRuns.atDepth schedules depth
      later).get outer).depth = (schedules.get outer).depth := by
  dsimp only [RequestedSurfaceRuns.atDepth]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact
    ParentCapacityTransport.CommonBasisPreparation.ParentRunSchedule.castCapacity_depth
    ..

/-- Refining the physical mesh preserves each retained occurrence numerical source threshold. -/
theorem atDepth_sourceIndex (depth : Nat) (later : request.depth ≤ depth)
    (outer : Fin prepared.occurrences.length) :
    ((RequestedSurfaceRuns.atDepth schedules depth
      later).get outer).sourceIndex = (schedules.get outer).sourceIndex := by
  dsimp only [RequestedSurfaceRuns.atDepth]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact
    ParentCapacityTransport.CommonBasisPreparation.ParentRunSchedule.castCapacity_sourceIndex
    ..

/-- Refining the physical mesh preserves each retained occurrence source magnitude. -/
theorem atDepth_magnitude (depth : Nat) (later : request.depth ≤ depth)
    (outer : Fin prepared.occurrences.length) :
    ((RequestedSurfaceRuns.atDepth schedules depth
      later).get outer).magnitude = (schedules.get outer).magnitude := by
  dsimp only [RequestedSurfaceRuns.atDepth]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact
    ParentCapacityTransport.CommonBasisPreparation.ParentRunSchedule.castCapacity_magnitude
    ..

end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
