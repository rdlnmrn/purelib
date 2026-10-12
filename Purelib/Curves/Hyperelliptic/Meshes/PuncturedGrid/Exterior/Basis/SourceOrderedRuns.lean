module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.GetD
import Purelib.Data.List.Map
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder
import Purelib.Integration.Path.PairedReverseBlocks
import Init.Data.List.OfFn
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
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
import Purelib.Topology.Polygon.Stokes

public section
/-! Select grouped runs by exact retained source position, preserving repeated parent payloads. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
open Purelib.Data.List
open Purelib.LinearAlgebra.Gaussian.Energy
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains (SourceChain)
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

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
variable (retained : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

variable {retained inputs outer data coefficients}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

set_option genInjectivity false in
/-- A finite run bank indexed by source position, not by equality of parent payloads. Its list already has the exact
original parent order. -/
structure ParentOrderedRuns (retained : Preparation.CommonBasisPreparation prepared) (inputs : retained.Inputs index)
    (outer : Fin prepared.occurrences.length) (data : FragmentQueries.RowData (ParentIndices.occurrenceAt
      prepared.occurrences outer) faceIndex)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The original fragment runs retained in complete source-parent order. -/ runs : List (FragmentGrouping.IndexedRun
    retained inputs outer data coefficients)
  /-- The retained run parents enumerate every original bounded source position exactly once in ascending order. -/
    indices : runs.map IndexedRun.parent =
    List.ofFn (fun position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length => position)

constructive_injectivity ParentOrderedRuns

namespace IndexedGrouping
variable {items : List
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs
  outer data coefficients)}

/-- Retain the original grouped forward runs with their exact ascending source-parent certificate. -/
@[expose] def inSourceOrder (grouped : FragmentGrouping.IndexedGrouping retained inputs outer data coefficients items)
    (word : IndexedFragment.ParentWord items) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns retained inputs outer
      data coefficients :=
  ⟨grouped.runs, IndexedGrouping.parent_indices grouped word⟩

/-- Reverse the descending run list once and retain its exact ascending source-parent certificate. -/
@[expose] def reverseInSourceOrder (grouped : FragmentGrouping.IndexedGrouping retained inputs outer data coefficients
  items)
    (word : IndexedFragment.ReverseParentWord items) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns retained inputs outer
      data coefficients :=
  ⟨grouped.runs.reverse, IndexedGrouping.reverse_parent_indices grouped word⟩

end IndexedGrouping
namespace ParentOrderedRuns
variable (ordered : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer data coefficients)

/-- The retained run list has exactly the original source-parent count. -/
theorem length_eq : ordered.runs.length =
    (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length := by
  have equal := congrArg List.length ordered.indices
  simpa only [Data.List.Map.length_map, Data.List.OfFn.Basic.length_ofFn, -eq_self, -iff_self] using equal

/-- The stored length certificate supplies the bound; no search or payload comparison is involved in selecting the
retained run. -/
@[expose] def runAt (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length) :
    FragmentGrouping.IndexedRun retained inputs outer data coefficients :=
  ordered.runs[position.val]'(position.isLt.trans_eq ordered.length_eq.symm)

/-- The selected retained run has exactly the requested original parent position. -/
theorem runAt_parent (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length) :
    (ordered.runAt position).parent = position := by
  have bound := position.isLt.trans_eq ordered.length_eq.symm
  have equal := (Data.List.at_cast ordered.indices
    ⟨position.val, by rw [Data.List.Map.length_map]; exact bound⟩).symm
  rw [Data.List.Map.getElem_map] at equal
  have tableBound : position.val < (List.ofFn (fun current : Fin (ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length => current)).length := by
    rewrite [Data.List.OfFn.Basic.length_ofFn]
    exact position.isLt
  change (ordered.runAt position).parent =
    (List.ofFn (fun current : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length => current))[position.val]'tableBound at equal
  rewrite [Data.List.OfFn.Basic.getElem_ofFn _ position tableBound] at equal
  exact equal

/-- The bounded selection is a member of the original cached run list. -/
theorem runAt_mem (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length) :
    ordered.runAt position ∈ ordered.runs :=
  List.getElem_mem (position.isLt.trans_eq ordered.length_eq.symm)

/-- Reading every position returns the original cached list exactly. -/
theorem runAt_all : List.ofFn ordered.runAt = ordered.runs := by
  exact Eq.rec (motive := fun count equal =>
    List.ofFn (fun position : Fin count => ordered.runs[position.val]'(position.isLt.trans_eq equal.symm)) =
      ordered.runs)
    (Data.List.OfFn.Basic.ofFn_getElem ordered.runs) ordered.length_eq

/-- Read the complete physical increment block of the retained run at its original source-parent position. -/
@[expose] def physical (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length) : List PrimitivePoint :=
  (((ordered.runAt position).fragments.map OwnedFragment.pair).map Prod.fst).flatten

/-- Reindexing retains each whole physical block, including its junctions. -/
theorem physical_all : List.ofFn ordered.physical = ordered.runs.map (fun run =>
    ((run.fragments.map OwnedFragment.pair).map Prod.fst).flatten) := by
  have equal := congrArg (List.map (fun run : FragmentGrouping.IndexedRun retained inputs outer data coefficients =>
    ((run.fragments.map OwnedFragment.pair).map Prod.fst).flatten)) ordered.runAt_all
  rw [OfFn.Basic.map_ofFn] at equal
  exact equal

end ParentOrderedRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
