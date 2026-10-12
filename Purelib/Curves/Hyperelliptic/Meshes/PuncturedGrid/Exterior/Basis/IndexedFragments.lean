module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks
import Init.Core
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Geometry.Rectangle.Partition

open Purelib.Topology.Polygon

@[expose] public section

/-! Retain physical fragments at their canonical numerical parent positions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
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
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
variable (retained : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- Fragments at this position share the exact original primitive bank. -/
def ParentFragment
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length) :=
  OwnedFragments.OwnedFragment (originals := (ParentInputs.parentInput retained inputs outer
    position).numerical.originals)
    (coefficients := coefficients) data

set_option genInjectivity false in
/-- An original physical fragment retaining its canonical parent position and that parent's identical primitive bank. -/
structure IndexedFragment where
  /-- The fragment's original bounded parent position in the retained occurrence. -/ parent : Fin
    (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length
  /-- The cached owned fragment on exactly that original parent's primitive bank. -/ fragment :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment retained inputs outer data
    coefficients parent

constructive_injectivity IndexedFragment

variable {retained inputs outer data coefficients}

namespace ParentFragment

/-- Equality transport keeps the cached readings and both increment samples. -/
def castParent {first last : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length}
    (same : first = last) (fragment :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment retained inputs outer
      data coefficients first) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment retained inputs outer data
      coefficients last :=
  Eq.mp (congrArg (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment retained
    inputs outer data coefficients) same) fragment

/-- Transporting a fragment along an equality of retained parent positions preserves both cached increment lists. -/
theorem castParent_pair {first last : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length}
    (same : first = last) (fragment :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment retained inputs outer
      data coefficients first) :
    (fragment.castParent same).pair = fragment.pair := by
  cases same
  rfl

end ParentFragment
namespace IndexedFragment

/-- Read the original physical and source increment lists from the retained indexed fragment. -/
def pair (item : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained
  inputs outer data coefficients) :
    List Stokes.PrimitivePoint × List PrimitivePoint := item.fragment.pair

/-- Physical builders enter the indexed representation without reacquisition. -/
def ofBlockSample {vertical forward : Bool} {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock (ParentIndices.occurrenceAt prepared.occurrences outer) vertical forward physical)
    {vertices : Nat} {values : Fin (vertices + 1) → Stokes.PrimitivePoint}
    (sample : PhysicalBanks.BlockSample retained inputs outer block data coefficients values) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs outer data
      coefficients := ⟨block.index, sample.fragment⟩

/-- Indexing an original block sample preserves its exact physical/source increment pair. -/
theorem ofBlockSample_pair {vertical forward : Bool} {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock (ParentIndices.occurrenceAt prepared.occurrences outer) vertical forward physical)
    {vertices : Nat} {values : Fin (vertices + 1) → Stokes.PrimitivePoint}
    (sample : PhysicalBanks.BlockSample retained inputs outer block data coefficients values) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample block
      sample).pair = sample.fragment.pair := rfl

end IndexedFragment

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
