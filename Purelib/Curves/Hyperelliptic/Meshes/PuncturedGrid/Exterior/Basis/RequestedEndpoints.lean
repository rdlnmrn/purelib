module
import Purelib.Tactic.Ring
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

public section

/-! Read acquired component endpoint chords from the original shared cache. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedEndpoints

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedSurfaceRuns

variable {whole :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  (selected : SourceCuts whole previous)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)

variable {selected request} {retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared} {index : Nat} {inputs :
  retained.Inputs index}
  {traces : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Traces
    (prepared := prepared) selected request} {faceIndex : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {requested :
    Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {schedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    selected request retained inputs requested minimum}
  {vertices : (outer : Fin prepared.occurrences.length) → Fin
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
    request outer) → Nat}
  {owners :
    RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.SharedOwnerBanks
    schedules
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.pieceCounts
    selected request) vertices}
  {perimeters :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Perimeters
    selected request traces cache}

namespace PhysicalSamples

variable (samples :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.PhysicalSamples
  selected request traces cache coefficients schedules owners perimeters)

/-- Every signed endpoint reads the original four-corner numerical bank. -/
theorem endpointSides_eq_cached :
  RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.endpointSides
  samples =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
      let endpoint := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter.cachedEndpoint
        cache coefficients occurrence.sideOccurrence.position
        occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then endpoint else -endpoint) := by
  unfold
    RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.endpointSides
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.OfFn.Basic.ofFn_congr
  intro outer
  exact congrArg (fun endpoint => if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).sourceForward then endpoint else -endpoint)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter.endpoint_eq_cached (traces.get
      outer) cache coefficients
      ((samples.get outer).samples.get (traces.get outer) cache coefficients
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).sideOccurrence.side))

/-- The retained source traversal sign agrees with the orientation of the original grid-side occurrence. -/
private theorem signed_endpoint (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (value : Normalization.InverseRootPolynomial.Gaussian) :
    (if occurrence.sourceForward then value else -value) =
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
      occurrence.sideOccurrence value := by
  cases side : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
    simp only
      [SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceForward,
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented, side,
        backward,
      if_pos (by decide : Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .left),
      if_pos (by decide : Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .left),
      if_neg (by decide : ¬ (Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .left)),
      if_neg (by decide : ¬ (Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .left)),
      if_pos (Eq.refl true), if_neg (by decide : ¬ false = true), -eq_self, -iff_self] <;>
      first | rfl | ring1

/-- The original component traversal supplies the signs of its cached chords. -/
theorem endpointSides_eq_oriented :
  RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.endpointSides
  samples =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        occurrence.sideOccurrence
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter.cachedEndpoint cache
        coefficients occurrence.sideOccurrence.position
        occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side)) := by
  rw
    [endpointSides_eq_cached
    samples]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  exact Data.List.OfFn.Basic.ofFn_congr (fun outer =>
    signed_endpoint
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) _)

end PhysicalSamples
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedEndpoints
