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

open Purelib.Geometry.Rectangle

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
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrence
    regular domains differential}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)

namespace ParentBlock
variable {vertical forward : Bool} {physical : Partition.PreparedAxisPartitions.Interval}
  (block : ParentBlock occurrence vertical
    forward physical)
  {covers : BasisSourceCovers
    (ParentBlocks.cacheParent occurrence block.index)}
  {sourceIndex faceIndex : Nat}
  {originals :
    PrimitiveBank
    covers sourceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data :
    RowData occurrence faceIndex}
  (coordinate : Coordinate)
  (sourceFirst : SourceIntervals.axisCoordinate (!vertical) occurrence.start = coordinate)
  (sourceLast : SourceIntervals.axisCoordinate (!vertical) occurrence.finish = coordinate)
  {lc lr rc rr vertices : Nat}
  {lg : RectangularInverseModels.Geometry lc lr} {rg :
    RectangularInverseModels.Geometry rc rr}
  {piece : RectangularPairedSegments.PairedSegmentPiece lg rg} (trace :
    Riemann.Integration.RectangularPairedPointBanks.Trace piece vertices)
  (firstAlong : SourceIntervals.axisCoordinate vertical piece.first = physical.lower)
  (lastAlong : SourceIntervals.axisCoordinate vertical piece.last = physical.upper)
  (firstAcross : SourceIntervals.axisCoordinate (!vertical) piece.first = coordinate)
  (lastAcross : SourceIntervals.axisCoordinate (!vertical) piece.last = coordinate)
  (increasing : ∀ edge : Fin vertices, trace.parameters edge.castSucc ≤ trace.parameters edge.succ)
  {allowance : Coordinate} (budget :
    LengthErrorBudget vertices allowance)
  (owners : OwnerRequest occurrence
    budget.tolerance) (later : owners.index ≤ faceIndex)
  (readings : OwnedReadings data (fun
    vertex => trace.points vertex))
  (owned : Sample (fun vertex =>
    ConjugateIncrementComparison.conjugateFirst
    (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
      PrimitivePoint)))
  (source : Sample (fun vertex =>
    ConjugateIncrementComparison.conjugateFirst

      (⟨Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
      originals coefficients
        ((block.traceParameters coordinate sourceFirst sourceLast trace firstAlong lastAlong firstAcross
          lastAcross).parameters vertex),

        Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients
        ((block.traceParameters coordinate sourceFirst sourceLast trace firstAlong lastAlong firstAcross
          lastAcross).parameters vertex)⟩ : PrimitivePoint)))

/-- Consume the canonical parent's located split and the existing physical trace. The source bank is indexed by that
exact original parent. -/
def ownedFragment : OwnedFragment (originals := originals) (coefficients := coefficients) data :=
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
