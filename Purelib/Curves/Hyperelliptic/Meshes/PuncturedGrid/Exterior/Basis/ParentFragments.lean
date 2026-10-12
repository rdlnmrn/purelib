module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalFragments
import Purelib.Riemann.Paths.RectangularParentTraceSteps
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularAxisParameterRange
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularTraceParameterReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Integration.Path

open Purelib.Riemann.Paths

@[expose] public section

/-! Construct owned physical fragments on the canonical common-source parent. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings
  ownedValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)

namespace ParentBlock
variable {vertical forward : Bool} {physical : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
  (block : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock occurrence vertical
    forward physical)
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence block.index)}
  {sourceIndex faceIndex : Nat}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers sourceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex}
  (coordinate : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate)
  (sourceFirst : Purelib.Geometry.Rectangle.SourceIntervals.axisCoordinate (!vertical) occurrence.start = coordinate)
  (sourceLast : Purelib.Geometry.Rectangle.SourceIntervals.axisCoordinate (!vertical) occurrence.finish = coordinate)
  {lc lr rc rr vertices : Nat}
  {lg : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry lc lr} {rg :
    Purelib.Riemann.Normalization.RectangularInverseModels.Geometry rc rr}
  {piece : Purelib.Riemann.Paths.RectangularPairedSegments.PairedSegmentPiece lg rg} (trace :
    Purelib.Riemann.Integration.RectangularPairedPointBanks.Trace piece vertices)
  (firstAlong : Purelib.Geometry.Rectangle.SourceIntervals.axisCoordinate vertical piece.first = physical.lower)
  (lastAlong : Purelib.Geometry.Rectangle.SourceIntervals.axisCoordinate vertical piece.last = physical.upper)
  (firstAcross : Purelib.Geometry.Rectangle.SourceIntervals.axisCoordinate (!vertical) piece.first = coordinate)
  (lastAcross : Purelib.Geometry.Rectangle.SourceIntervals.axisCoordinate (!vertical) piece.last = coordinate)
  (increasing : ∀ edge : Fin vertices, trace.parameters edge.castSucc ≤ trace.parameters edge.succ)
  {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
    Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget vertices allowance)
  (owners : OwnerRequest occurrence
    budget.tolerance) (later : owners.index ≤ faceIndex)
  (readings : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
    vertex => trace.points vertex))
  (owned : Purelib.Riemann.Periods.CenteredBilinearPath.Sample (fun vertex =>
    Purelib.Integration.Path.ConjugateIncrementComparison.conjugateFirst
    (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
      Purelib.Topology.Polygon.Stokes.PrimitivePoint)))
  (source : Purelib.Riemann.Periods.CenteredBilinearPath.Sample (fun vertex =>
    Purelib.Integration.Path.ConjugateIncrementComparison.conjugateFirst

      (⟨Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
      originals coefficients
        ((block.traceParameters coordinate sourceFirst sourceLast trace firstAlong lastAlong firstAcross
          lastAcross).parameters vertex),

        Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients
        ((block.traceParameters coordinate sourceFirst sourceLast trace firstAlong lastAlong firstAcross
          lastAcross).parameters vertex)⟩ : Purelib.Topology.Polygon.Stokes.PrimitivePoint)))

/-- Consume the canonical parent's located split and the existing physical trace. The source bank is indexed by that
exact original parent. -/
def ownedFragment : OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data :=
  OwnedFragment.ofTrace block.member block.located forward
    (block.traceParameters coordinate sourceFirst sourceLast trace firstAlong lastAlong firstAcross lastAcross)
    increasing budget owners later readings owned source

local notation "fragment" => block.ownedFragment coordinate sourceFirst sourceLast trace
  firstAlong lastAlong firstAcross lastAcross increasing budget owners later readings owned source

/-- Endpoint readbacks refer to retained parent parameters in either orientation. -/
theorem ownedFragment_first : (fragment).parameters 0 = block.firstParameter :=
  RectangularParentTraceSteps.first_parameter (block.traceParameters coordinate sourceFirst sourceLast trace firstAlong
    lastAlong firstAcross lastAcross)

/-- The original owned fragment's last parameter is the retained parent block's direction-selected endpoint. -/
theorem ownedFragment_last : (fragment).parameters (Fin.last vertices) = block.lastParameter :=
  (block.traceParameters coordinate sourceFirst sourceLast trace firstAlong lastAlong firstAcross
    lastAcross).last_parameter

/-- Physical increments remain the increments of the supplied area sample. -/
theorem ownedFragment_increments : (fragment).pair.1 = CenteredPathIncrements.Sample.increments owned := rfl

end ParentBlock
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
