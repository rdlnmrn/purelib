module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
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
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath

/-! Preserve owner-error budgets through parent transport, interleaving and grouping. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedBudgets
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
open Purelib.Data.List

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

namespace ParentFragment
variable {first last : Fin (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length}

/-- Transporting to an equal retained parent preserves the original fragment allowance. -/
theorem castParent_allowance (same : first = last)
    (fragment : IndexedFragments.ParentFragment retained inputs outer data coefficients first) :
    (fragment.castParent same).allowance = fragment.allowance := by
  cases same
  rfl

/-- Transporting to an equal retained parent preserves the original owner-budget tolerance. -/
theorem castParent_tolerance (same : first = last)
    (fragment : IndexedFragments.ParentFragment retained inputs outer data coefficients first) :
    (fragment.castParent same).budget.tolerance = fragment.budget.tolerance := by
  cases same
  rfl

end ParentFragment
namespace IndexedRun

/-- Transport changes only the parent index; both numeric budget bounds survive.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
theorem fragmentsAt_budget
    (parent : Fin (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length)
    (items : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients))
    (same : ∀ item ∈ items, item.parent = parent)
    {allowance tolerance : InverseRootPolynomial.Coordinate}
    (paid : ∀ item ∈ items, item.fragment.allowance ≤ allowance ∧ item.fragment.budget.tolerance ≤ tolerance) :
    ∀ fragment ∈ IndexedRun.fragmentsAt parent items same,
      fragment.allowance ≤ allowance ∧ fragment.budget.tolerance ≤ tolerance := by
  induction items with
  | nil => intro _ member; cases member
  | cons item rest ih =>
    intro fragment member
    rcases Membership.mem_cons.mp member with rfl | member
    · have bounds := paid item List.mem_cons_self
      exact
        ⟨(Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedBudgets.ParentFragment.castParent_allowance _
        _).trans_le bounds.1,
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedBudgets.ParentFragment.castParent_tolerance _
          _).trans_le bounds.2⟩
    · exact ih (fun next member => same next (List.mem_cons_of_mem _ member))
        (fun next member => paid next (List.mem_cons_of_mem _ member)) fragment member

/-- Every transported fragment of the retained run inherits its original allowance and tolerance bounds. -/
theorem fragments_budget (run : FragmentGrouping.IndexedRun retained inputs outer data coefficients)
    {allowance tolerance : InverseRootPolynomial.Coordinate}
    (paid : ∀ item ∈ run.items, item.fragment.allowance ≤ allowance ∧ item.fragment.budget.tolerance ≤ tolerance) :
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowance ∧ fragment.budget.tolerance ≤ tolerance :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedBudgets.IndexedRun.fragmentsAt_budget run.parent
    run.items (fun _ member => run.parent_eq member) paid

end IndexedRun

namespace IndexedGrouping
variable {items : List
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs
  outer data coefficients)}

/-- Every stored run inherits the paid budgets of the original geometric side. -/
theorem run_budget (grouped : FragmentGrouping.IndexedGrouping retained inputs outer data coefficients items)
    {allowance tolerance : InverseRootPolynomial.Coordinate}
    (paid : ∀ item ∈ items, item.fragment.allowance ≤ allowance ∧ item.fragment.budget.tolerance ≤ tolerance)
    (run : FragmentGrouping.IndexedRun retained inputs outer data coefficients) (member : run ∈ grouped.runs) :
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowance ∧ fragment.budget.tolerance ≤ tolerance := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedBudgets.IndexedRun.fragments_budget run
  intro item inside
  apply paid item
  rw [← grouped.flattened]
  exact mem_flatten_of_mem (Map.mem_map_of_mem member) inside

end IndexedGrouping

/-- Piece and junction certificates cover the entire interleaved side, including stationary owner changes. No
endpoint-only substitute is used.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
theorem indexedSideFragments_budget {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragments.IndexedFragment retained inputs outer data coefficients)
    (junctions : Fin count → IndexedFragments.IndexedFragment retained inputs outer data coefficients)
    {allowance tolerance : InverseRootPolynomial.Coordinate}
    (piecePaid : ∀ position, (pieces position).fragment.allowance ≤ allowance ∧
      (pieces position).fragment.budget.tolerance ≤ tolerance)
    (junctionPaid : ∀ position, (junctions position).fragment.allowance ≤ allowance ∧
      (junctions position).fragment.budget.tolerance ≤ tolerance) :
    ∀ item ∈ GroupedSideReadback.indexedSideFragments pieces junctions,
      item.fragment.allowance ≤ allowance ∧ item.fragment.budget.tolerance ≤ tolerance := by
  induction count with
  | zero =>
    intro item member
    rcases Membership.mem_cons.mp member with rfl | member
    · exact piecePaid 0
    · cases member
  | succ count ih =>
    intro item member
    rcases Membership.mem_cons.mp member with rfl | member
    · exact piecePaid 0
    · rcases Membership.mem_cons.mp member with rfl | member
      · exact junctionPaid 0
      · exact ih (fun position => pieces position.succ) (fun position => junctions position.succ)
          (fun position => piecePaid position.succ) (fun position => junctionPaid position.succ) item member

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedBudgets
