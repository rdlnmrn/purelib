module
import Purelib.Data.List.Membership
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Data.List

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

public section

/-! Preserve forward mesh-width budgets through common-parent grouping. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedWidths
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback (groupSideFragments
  indexedSideFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains (SourceChain)
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

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
variable (retained : CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : RowData
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

variable {retained inputs outer data coefficients}

namespace ParentFragment

/-- Transporting to an equal retained parent preserves the original fragment's source width. -/
theorem castParent_width
    {first last : Fin (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length}
    (same : first = last) (fragment : IndexedFragments.ParentFragment retained inputs outer data coefficients first) :
    (fragment.castParent same).sourceWidth = fragment.sourceWidth := by
  cases same
  rfl

end ParentFragment

/-- Transporting original fragments to their common retained parent preserves every source-width bound. -/
private theorem fragmentsAt_bounded
    (parent : Fin (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length)
    (items : List (IndexedFragment retained inputs outer data coefficients))
    (same : ∀ item ∈ items, item.parent = parent) {width : Coordinate}
    (bounded : ∀ item ∈ items, item.fragment.sourceWidth ≤ width) :
    ∀ fragment ∈ IndexedRun.fragmentsAt parent items same, fragment.sourceWidth ≤ width := by
  induction items with
  | nil => intro _ member; cases member
  | cons item rest ih =>
    intro fragment member
    rcases Membership.mem_cons.mp member with rfl | member
    · exact (ParentFragment.castParent_width _
        item.fragment).trans_le (bounded item List.mem_cons_self)
    · exact ih (fun found present => same found (List.mem_cons_of_mem item present))
        (fun found present => bounded found (List.mem_cons_of_mem item present)) fragment member

/-- An original fragment of a retained member run belongs to the complete flattened run list. -/
private theorem item_present (runs : List (IndexedRun retained inputs outer data coefficients))
    {run : IndexedRun retained inputs outer data coefficients} (present : run ∈ runs)
    {item : IndexedFragment retained inputs outer data coefficients} (member : item ∈ run.items) :
    item ∈ (runs.map IndexedRun.items).flatten := by
  induction runs with
  | nil => cases present
  | cons first rest ih =>
    rcases Membership.mem_cons.mp present with rfl | present
    · exact Membership.mem_append.mpr (Or.inl member)
    · exact Membership.mem_append.mpr (Or.inr (ih present))

/-- The explicit finite maximum is bounded by any nonnegative common bound on the original values. -/
private theorem maximum_le {Item : Type u} (value : Item → Coordinate) (items : List Item)
    {bound : Coordinate} (nonnegative : 0 ≤ bound) (bounded : ∀ item ∈ items, value item ≤ bound)
      :
    PairedFragmentBlocks.maximum value items ≤ bound := by
  induction items with
  | nil => exact nonnegative
  | cons first rest ih =>
    exact Data.Rat.Fraction.Order.Basic.max_le (bounded first List.mem_cons_self)
      (ih (fun item member => bounded item (List.mem_cons_of_mem _ member)))

namespace IndexedGrouping
variable {items : List
  (IndexedFragment retained inputs
  outer data coefficients)} {width : Coordinate}

/-- Transport and maximal grouping preserve the paid forward mesh width. -/
theorem width_bound (grouped : FragmentGrouping.IndexedGrouping retained inputs outer data coefficients items)
    (nonnegative : 0 ≤ width) (bounded : ∀ item ∈ items, item.fragment.sourceWidth ≤ width) :
    ∀ run ∈ grouped.runs,
      PairedFragmentBlocks.maximum OwnedFragment.sourceWidth run.fragments ≤ width := by
  intro run present
  apply GroupedWidths.maximum_le _ _ nonnegative
  apply GroupedWidths.fragmentsAt_bounded run.parent run.items
    (fun _ member => run.parent_eq member)
  intro item member
  exact bounded item ((congrArg (fun entries => item ∈ entries) grouped.flattened).mp
    (GroupedWidths.item_present grouped.runs present member))

end IndexedGrouping

/-- Every original piece and stationary junction contributes its retained width. -/
theorem indexedSideFragments_width {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragment retained inputs outer data coefficients)
    (junctions : Fin count → IndexedFragment retained inputs outer data coefficients) {width :
      Coordinate}
    (pieceBound : ∀ position, (pieces position).fragment.sourceWidth ≤ width)
    (junctionBound : ∀ position, (junctions position).fragment.sourceWidth ≤ width) :
    ∀ item ∈ GroupedSideReadback.indexedSideFragments pieces junctions, item.fragment.sourceWidth ≤ width := by
  induction count with
  | zero =>
    intro item member
    rcases Membership.mem_cons.mp member with rfl | member
    · exact pieceBound 0
    · cases member
  | succ count ih =>
    intro item member
    rcases Membership.mem_cons.mp member with rfl | member
    · exact pieceBound 0
    rcases Membership.mem_cons.mp member with rfl | member
    · exact junctionBound 0
    exact ih (fun position => pieces position.succ) (fun position => junctions position.succ)
      (fun position => pieceBound position.succ) (fun position => junctionBound position.succ) item member

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedWidths
