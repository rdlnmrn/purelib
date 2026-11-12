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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseChains
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

open Purelib.Curves

open Purelib

open Purelib.Riemann

public section

/-! Preserve reverse mesh-width budgets through common-parent grouping. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseWidths

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable (retained : Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : FragmentQueries.RowData
    (ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

variable {retained inputs outer data coefficients}

namespace ParentFragment

/-- Transporting a fragment along equality of its retained parent index preserves its reverse source width. -/
theorem castParent_reverseWidth
    {first last : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length}
    (same : first = last) (fragment : IndexedFragments.ParentFragment
      retained inputs outer data coefficients first) :
    (fragment.castParent same).reverseSourceWidth = fragment.reverseSourceWidth := by
  cases same
  rfl

end ParentFragment

/-- Transporting all fragments to their common retained parent preserves a pointwise reverse-width bound. -/
private theorem fragmentsAt_bounded
    (parent : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length)
    (items : List (IndexedFragments.IndexedFragment retained inputs
      outer data coefficients))
    (same : ∀ item ∈ items, item.parent = parent) {width : InverseRootPolynomial.Coordinate}
    (bounded : ∀ item ∈ items, item.fragment.reverseSourceWidth ≤ width) :
    ∀ fragment ∈ FragmentGrouping.IndexedRun.fragmentsAt parent items
      same, fragment.reverseSourceWidth ≤ width := by
  induction items with
  | nil => intro _ member; cases member
  | cons item rest ih =>
    intro fragment member
    rcases Membership.mem_cons.mp member with rfl | member
    · exact
        (ParentFragment.castParent_reverseWidth _
        item.fragment).trans_le (bounded item List.mem_cons_self)
    · exact ih (fun found present => same found (List.mem_cons_of_mem item present))
        (fun found present => bounded found (List.mem_cons_of_mem item present)) fragment member

/-- An item in a retained run occurs in the flattened ordered list of all run items. -/
private theorem item_present (runs : List (FragmentGrouping.IndexedRun
  retained inputs outer data coefficients))
    {run : FragmentGrouping.IndexedRun retained inputs outer data
      coefficients} (present : run ∈ runs)
    {item : IndexedFragments.IndexedFragment retained inputs outer
      data coefficients} (member : item ∈ run.items) :
    item ∈ (runs.map FragmentGrouping.IndexedRun.items).flatten := by
  induction runs with
  | nil => cases present
  | cons first rest ih =>
    rcases Membership.mem_cons.mp present with rfl | present
    · exact Membership.mem_append.mpr (Or.inl member)
    · exact Membership.mem_append.mpr (Or.inr (ih present))

/-- A nonnegative pointwise bound also bounds the finite maximum of the listed rational values. -/
private theorem maximum_le {Item : Type u} (value : Item → InverseRootPolynomial.Coordinate) (items : List
  Item)
    {bound : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ bound) (bounded : ∀ item ∈ items, value
      item ≤ bound) :
    PairedFragmentBlocks.maximum value items ≤ bound := by
  induction items with
  | nil => exact nonnegative
  | cons first rest ih =>
    exact Data.Rat.Fraction.Order.Basic.max_le (bounded first List.mem_cons_self)
      (ih (fun item member => bounded item (List.mem_cons_of_mem _ member)))

namespace IndexedGrouping
variable {items : List (IndexedFragments.IndexedFragment retained
  inputs outer data coefficients)} {width : InverseRootPolynomial.Coordinate}

/-- Transport and maximal grouping preserve the paid reverse mesh width. -/
theorem reverse_width_bound (grouped :
  FragmentGrouping.IndexedGrouping retained inputs outer data
  coefficients items)
    (nonnegative : 0 ≤ width) (bounded : ∀ item ∈ items, item.fragment.reverseSourceWidth ≤ width) :
    ∀ run ∈ grouped.runs,
      PairedFragmentBlocks.maximum
        OwnedFragments.OwnedFragment.reverseSourceWidth run.fragments
        ≤ width := by
  intro run present
  apply GroupedReverseWidths.maximum_le _ _ nonnegative
  apply GroupedReverseWidths.fragmentsAt_bounded run.parent run.items
    (fun _ member => run.parent_eq member)
  intro item member
  exact bounded item ((congrArg (fun entries => item ∈ entries) grouped.flattened).mp
    (GroupedReverseWidths.item_present grouped.runs present member))

end IndexedGrouping

/-- Every original piece and stationary junction contributes its retained width. -/
theorem indexedSideFragments_reverse_width {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragments.IndexedFragment
      retained inputs outer data coefficients)
    (junctions : Fin count → IndexedFragments.IndexedFragment retained
      inputs outer data coefficients) {width : InverseRootPolynomial.Coordinate}
    (pieceBound : ∀ position, (pieces position).fragment.reverseSourceWidth ≤ width)
    (junctionBound : ∀ position, (junctions position).fragment.reverseSourceWidth ≤ width) :
    ∀ item ∈ GroupedSideReadback.indexedSideFragments pieces
      junctions, item.fragment.reverseSourceWidth ≤ width := by
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

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseWidths
