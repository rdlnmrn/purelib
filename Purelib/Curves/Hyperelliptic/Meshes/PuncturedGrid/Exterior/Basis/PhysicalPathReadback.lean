module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path

open Purelib.Integration.Path.JoinedTrace

open Purelib.Integration.Polynomial.Rectangle

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

@[expose] public section

/-! Full physical path readback across heterogeneous retained source parents. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalPathReadback
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation (CommonBasisPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (blockIndex blockIndex_read
  occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection (SelectedInput)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs (blockInput)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank (ParentBlockBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments (SampledFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks (BlockSample)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)

/-- Keep physical and source increments paired in the original side order. -/
def pairedSideBlocks : {count : Nat} →
    (Fin (count + 1) → List Stokes.PrimitivePoint × List Stokes.PrimitivePoint) →
    (Fin count → List Stokes.PrimitivePoint × List Stokes.PrimitivePoint) →
    List (List Stokes.PrimitivePoint × List Stokes.PrimitivePoint)
  | 0, pieces, _ => [pieces 0]
  | _ + 1, pieces, junctions => pieces 0 :: junctions 0 ::
      pairedSideBlocks (fun
        position => pieces position.succ) (fun position => junctions position.succ)

variable {retained : CommonBasisPreparation
  prepared} {index : Nat} {inputs : retained.Inputs index}
  {outer : Fin prepared.occurrences.length} {faceIndex : Nat}
  {data : RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {vertical forward : Bool}
  {Vertex : Type} (values : Vertex → PrimitivePoint)

/-- A side may cross several original parents. Its physical readback does not require identifying their independently
retained source banks. -/
theorem pairedSideBlocks_physical {count : Nat}
    (physical : Fin (count + 1) → PreparedAxisPartitions.Interval)
    (blocks : (position : Fin (count + 1)) →
      ParentBlocks.ParentBlock (ParentIndices.occurrenceAt prepared.occurrences outer) vertical forward (physical
        position))
    (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      PhysicalBanks.BlockSample retained inputs outer (blocks position) data coefficients
        (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      PhysicalBanks.BlockSample retained inputs outer (blocks position.castSucc) data coefficients
        (JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ))) :
    (pairedSideBlocks (fun position =>
      (pieces position).fragment.pair)
      (fun position => (junctions position).fragment.pair)).map Prod.fst =
    JoinedSampleBlocks.sampledBlocks values traces (fun position => (pieces position).reading)
      (fun position => (junctions position).reading) := by
  induction count with
  | zero => exact congrArg (fun block => [block]) (pieces 0).increments_eq.symm
  | succ count ih =>
    exact congrArg₂ List.cons (pieces 0).increments_eq.symm
      (congrArg₂ List.cons (junctions 0).increments_eq.symm
        (ih (fun position => physical position.succ) (fun position => blocks position.succ)
          (fun position => traces position.succ) (fun position => pieces position.succ)
          (fun position => junctions position.succ)))

/-- The flattened physical projection is exactly the original cached side sample, including every owner junction and
cross-parent joining term. -/
theorem pairedSideBlocks_flatten {count : Nat}
    (physical : Fin (count + 1) → PreparedAxisPartitions.Interval)
    (blocks : (position : Fin (count + 1)) →
      ParentBlocks.ParentBlock (ParentIndices.occurrenceAt prepared.occurrences outer) vertical forward (physical
        position))
    (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      PhysicalBanks.BlockSample retained inputs outer (blocks position) data coefficients
        (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      PhysicalBanks.BlockSample retained inputs outer (blocks position.castSucc) data coefficients
        (JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
    {whole : JoinedTrace.VertexTrace Vertex}
    (sample : CenteredBilinearPath.Sample (fun vertex => values (whole.indexed vertex)))
    (traceEq : whole = VertexTrace.concatenate traces) :
    ((pairedSideBlocks (fun position =>
      (pieces position).fragment.pair)
      (fun position => (junctions position).fragment.pair)).map Prod.fst).flatten =
        CenteredPathIncrements.Sample.increments sample := by
  rw [pairedSideBlocks_physical values
    physical blocks traces pieces junctions]
  exact JoinedSampleBlocks.sampledBlocks_flatten values traces _ _ sample traceEq

/-- Read the complete area, rather than only the sum of individual piece areas. -/
theorem pairedSideBlocks_area {count : Nat}
    (physical : Fin (count + 1) → PreparedAxisPartitions.Interval)
    (blocks : (position : Fin (count + 1)) →
      ParentBlocks.ParentBlock (ParentIndices.occurrenceAt prepared.occurrences outer) vertical forward (physical
        position))
    (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      PhysicalBanks.BlockSample retained inputs outer (blocks position) data coefficients
        (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      PhysicalBanks.BlockSample retained inputs outer (blocks position.castSucc) data coefficients
        (JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
    {whole : JoinedTrace.VertexTrace Vertex}
    (sample : CenteredBilinearPath.Sample (fun vertex => values (whole.indexed vertex)))
    (traceEq : whole = VertexTrace.concatenate traces) :
    PairedIncrementArea.area
      ((pairedSideBlocks (fun position =>
        (pieces position).fragment.pair)
        (fun position => (junctions position).fragment.pair)).map Prod.fst).flatten = sample.centeredArea := by
  rw [pairedSideBlocks_flatten values
    physical blocks traces pieces junctions sample traceEq]
  exact CenteredPathIncrements.Sample.increments_area sample

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalPathReadback
