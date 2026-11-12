module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalPathReadback
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Integration.Path

open Purelib.Integration.Path.JoinedTrace

open Purelib.Riemann.Periods

@[expose] public section

/-! Preserve complete physical side samples through common-parent grouping. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation (CommonBasisPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (parentIndex parentIndex_read
  occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection (SelectedInput)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks (BlockSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments (IndexedFragment ParentFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping (IndexedRun IndexedGrouping)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : ExteriorProgram lifted
    differential} {prepared :
    SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalPathReadback (pairedSideBlocks
  pairedSideBlocks_flatten)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks (BlockSample)

variable {retained : CommonBasisPreparation
  prepared} {index : Nat} {inputs : retained.Inputs index}
  {outer : Fin prepared.occurrences.length} {faceIndex : Nat}
  {data : RowData
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- Interleave every physical piece with its retained owner junction. -/
def indexedSideFragments : {count : Nat} →
    (Fin (count + 1) → IndexedFragment retained inputs outer data coefficients) →
    (Fin count → IndexedFragment retained inputs outer data coefficients) →
    List (IndexedFragment retained inputs outer data coefficients)
  | 0, pieces, _ => [pieces 0]
  | _ + 1, pieces, junctions => pieces 0 :: junctions 0 ::
      GroupedSideReadback.indexedSideFragments (fun
        position => pieces position.succ) (fun position => junctions position.succ)

/-- The interleaved original indexed fragments retain exactly the physical piece and owner-junction increment pairs. -/
theorem indexedSideFragments_pairs {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragment retained inputs outer data coefficients)
    (junctions : Fin count → IndexedFragment retained inputs outer data coefficients) :
    (GroupedSideReadback.indexedSideFragments pieces
      junctions).map IndexedFragment.pair =
      PhysicalPathReadback.pairedSideBlocks (fun position => (pieces position).pair) (fun position => (junctions
        position).pair) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    exact congrArg (List.cons (pieces 0).pair)
      (congrArg (List.cons (junctions 0).pair)
        (ih (fun position => pieces position.succ) (fun position => junctions position.succ)))

variable {vertical forward : Bool} {Vertex : Type} (values : Vertex → PrimitivePoint)
  {count : Nat} (physical : Fin (count + 1) → Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval)
  (blocks : (position : Fin (count + 1)) →
    ParentBlock
      (ParentIndices.occurrenceAt prepared.occurrences
      outer) vertical forward (physical position))
  (traces : Fin (count + 1) → VertexTrace Vertex)
  (pieces : (position : Fin (count + 1)) →
    BlockSample retained inputs outer
      (blocks position) data coefficients
      (fun vertex => values ((traces position).indexed vertex)))
  (junctions : (position : Fin count) →
    BlockSample retained inputs outer
      (blocks position.castSucc) data coefficients
      (Integration.Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues values (traces position.castSucc)
        (traces position.succ)))

/-- Construct the maximal groups from the existing certified side banks. -/
def groupSideFragments :=
  IndexedGrouping.build
    (GroupedSideReadback.indexedSideFragments
    (fun position => IndexedFragment.ofBlockSample (blocks position) (pieces position))
    (fun position => IndexedFragment.ofBlockSample (blocks position.castSucc) (junctions position)))

/-- Grouping on common numerical owners preserves the whole physical sample, including cross-parent joining terms,
rather than merely its endpoint total. -/
theorem groupSideFragments_flatten {whole : VertexTrace Vertex}
    (sample : CenteredBilinearPath.Sample (fun vertex => values (whole.indexed vertex)))
    (traceEq : whole = VertexTrace.concatenate traces) :
    ((((GroupedSideReadback.groupSideFragments values physical
      blocks traces pieces junctions).runs.map
      (fun run => run.fragments.map OwnedFragment.pair)).flatten).map Prod.fst).flatten =
        CenteredPathIncrements.Sample.increments sample := by
  rw [(GroupedSideReadback.groupSideFragments values physical
    blocks traces pieces junctions).pairs_eq,
    GroupedSideReadback.indexedSideFragments_pairs]
  exact PhysicalPathReadback.pairedSideBlocks_flatten values physical blocks traces pieces junctions sample traceEq

/-- The complete grouped physical polygon has the original cached side sample's centered area.

The exact trace readback retains every piece and owner junction in order when grouping fragments by their original
numerical parent. -/
theorem groupSideFragments_area {whole : VertexTrace Vertex}
    (sample : CenteredBilinearPath.Sample (fun vertex => values (whole.indexed vertex)))
    (traceEq : whole = VertexTrace.concatenate traces) :
    PairedIncrementArea.area
      ((((GroupedSideReadback.groupSideFragments values
        physical blocks traces pieces junctions).runs.map
        (fun run => run.fragments.map OwnedFragment.pair)).flatten).map Prod.fst).flatten = sample.centeredArea := by
  rw [GroupedSideReadback.groupSideFragments_flatten values
    physical blocks traces pieces junctions sample traceEq]
  exact CenteredPathIncrements.Sample.increments_area sample

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback
