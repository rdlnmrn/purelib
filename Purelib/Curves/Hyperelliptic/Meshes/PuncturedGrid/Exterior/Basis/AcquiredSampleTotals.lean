module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOwnerSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrenceTotals
import Purelib.Approximation.Budget.RequestedLengthBudget
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath

open Purelib.Curves

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Original-corner totals on the scheduled and actually acquired physical bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredSampleTotals

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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns (mesh
  buildScheduled)

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {whole :
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
  {stage : Nat} (traces : Paths.RectangularPerimeterTraces.PerimeterTraces (mesh outer selected request))
  (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
  (banks : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Banks (occurrence :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) traces
    cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  (schedule :
    ParentRunSchedule
    retained inputs outer
    (SharedOccurrenceRuns.sideCapacity outer
      (mesh := mesh outer selected request)) requested minimum)
  {vertices : Fin
    (SharedOccurrenceRuns.sideCapacity outer
    (mesh := mesh outer selected request)) → Nat}
  (owners :
    SharedOwnerSchedule.CommonBasisPreparation.ParentRunSchedule.SharedOwners
    schedule (Paths.RectangularDyadicPairedTrace.dyadicCount (mesh outer selected request).depth) vertices)

variable (member : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
  outer ∈ whole.occurrences)
  (facePaid : owners.faceIndex ≤ stage)

/-- Shared owner scheduling preserves the original signed side displacement. -/
theorem buildScheduled_total :
    Path.PairedIncrementArea.total (List.ofFn
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.buildScheduled
      retained inputs outer selected member request
      traces cache banks coefficients schedule owners facePaid).physical).flatten =
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
      let total := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter.cachedIncrement
        (lifted := lifted) cache coefficients
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then total else Topology.Polygon.Stokes.PrimitivePoint.sub
        Topology.Polygon.Stokes.PrimitivePoint.zero total :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrenceTotals.RequestedOccurrenceRuns.build_total
    retained inputs outer selected member request traces cache banks coefficients
    owners.piece.budget owners.pieceOwner (owners.piece_le.trans facePaid)
    owners.junction.budget owners.junctionOwner (owners.junction_le.trans facePaid)

/-- Read the bank actually stored by acquisition, without an independent path assumption. -/
theorem acquireSample_total :
    Path.PairedIncrementArea.total (List.ofFn
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample.RequestedOccurrenceRuns.acquireSample
      retained inputs outer selected request
      traces cache banks coefficients schedule owners member facePaid).bank.physical).flatten =
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
      let total := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter.cachedIncrement
        (lifted := lifted) cache coefficients
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then total else Topology.Polygon.Stokes.PrimitivePoint.sub
        Topology.Polygon.Stokes.PrimitivePoint.zero total :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredSampleTotals.RequestedOccurrenceRuns.buildScheduled_total
    retained inputs outer selected request traces cache banks coefficients schedule owners member facePaid

end RequestedOccurrenceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredSampleTotals
