module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Curves

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Exact endpoint totals for the requested physical occurrence constructor. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrenceTotals

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns

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

namespace RequestedOccurrenceRuns

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {whole :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {previous :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  (selected : SourceCuts whole previous)
  (member : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer ∈
    whole.occurrences)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)

variable {stage : Nat} (traces : Paths.RectangularPerimeterTraces.PerimeterTraces
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.mesh outer selected
  request))
  (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
  (banks : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Banks (occurrence :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) traces
    cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
    (Paths.RectangularDyadicPairedTrace.dyadicCount
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.mesh outer selected
    request).depth) allowance)
  (owners : OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    budget.tolerance) (later : owners.index ≤ stage)
  {junctionAllowance : Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
    Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ stage)

/-- Whole-face refinement preserves the complete acquired occurrence word. -/
theorem build_increments :
    (List.ofFn (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.build
      retained inputs outer selected member request traces cache banks coefficients
      budget owners later junctionBudget junctionOwners junctionLater).physical).flatten =
      let sample := (banks.sample traces cache coefficients).get traces cache coefficients
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).sideOccurrence.side
      if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceForward then Path.CenteredPathIncrements.Sample.increments sample
      else Path.PairedAreaReversal.reverseIncrements (Path.CenteredPathIncrements.Sample.increments sample) :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.build_increments
    retained inputs outer traces cache banks coefficients
    budget owners later junctionBudget junctionOwners junctionLater
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlock.forOccurrence selected member request)
      rfl

/-- The actual acquired occurrence has its signed original corner displacement. -/
theorem build_total :
    Path.PairedIncrementArea.total (List.ofFn
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.build retained
      inputs outer selected member request traces cache banks coefficients
      budget owners later junctionBudget junctionOwners junctionLater).physical).flatten =
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
      let total := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter.cachedIncrement
        (lifted := lifted) cache coefficients
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then total else Topology.Polygon.Stokes.PrimitivePoint.sub
        Topology.Polygon.Stokes.PrimitivePoint.zero total := by
  rw
    [build_increments]
  dsimp only
  split
  · exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter.total_eq_cached traces cache
      coefficients _
  · rw [Path.PairedAreaReversal.total_reverseIncrements]
    exact congrArg (Topology.Polygon.Stokes.PrimitivePoint.sub Topology.Polygon.Stokes.PrimitivePoint.zero)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter.total_eq_cached traces cache
      coefficients _)

end RequestedOccurrenceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrenceTotals
