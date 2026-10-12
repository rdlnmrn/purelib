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

open Purelib.Curves

open Purelib

open Purelib.Riemann

public section

/-! Preserve reverse mesh-width budgets through common-parent grouping. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseWidths

open Purelib.Riemann.Normalization

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

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

variable {retained inputs outer data coefficients}

namespace ParentFragment

/-- Transporting a fragment along equality of its retained parent index preserves its reverse source width. -/
theorem castParent_reverseWidth
    {first last : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length}
    (same : first = last) (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment
      retained inputs outer data coefficients first) :
    (fragment.castParent same).reverseSourceWidth = fragment.reverseSourceWidth := by
  cases same
  rfl

end ParentFragment

/-- Transporting all fragments to their common retained parent preserves a pointwise reverse-width bound. -/
private theorem fragmentsAt_bounded
    (parent : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length)
    (items : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs
      outer data coefficients))
    (same : ∀ item ∈ items, item.parent = parent) {width : Normalization.InverseRootPolynomial.Coordinate}
    (bounded : ∀ item ∈ items, item.fragment.reverseSourceWidth ≤ width) :
    ∀ fragment ∈ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.fragmentsAt parent items
      same, fragment.reverseSourceWidth ≤ width := by
  induction items with
  | nil => intro _ member; cases member
  | cons item rest ih =>
    intro fragment member
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseWidths.ParentFragment.castParent_reverseWidth _
        item.fragment).trans_le (bounded item List.mem_cons_self)
    · exact ih (fun found present => same found (List.mem_cons_of_mem item present))
        (fun found present => bounded found (List.mem_cons_of_mem item present)) fragment member

/-- An item in a retained run occurs in the flattened ordered list of all run items. -/
private theorem item_present (runs : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun
  retained inputs outer data coefficients))
    {run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer data
      coefficients} (present : run ∈ runs)
    {item : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs outer
      data coefficients} (member : item ∈ run.items) :
    item ∈ (runs.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.items).flatten := by
  induction runs with
  | nil => cases present
  | cons first rest ih =>
    rcases Purelib.Data.List.Membership.mem_cons.mp present with rfl | present
    · exact Purelib.Data.List.Membership.mem_append.mpr (Or.inl member)
    · exact Purelib.Data.List.Membership.mem_append.mpr (Or.inr (ih present))

/-- A nonnegative pointwise bound also bounds the finite maximum of the listed rational values. -/
private theorem maximum_le {Item : Type u} (value : Item → Normalization.InverseRootPolynomial.Coordinate) (items : List
  Item)
    {bound : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ bound) (bounded : ∀ item ∈ items, value
      item ≤ bound) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum value items ≤ bound := by
  induction items with
  | nil => exact nonnegative
  | cons first rest ih =>
    exact Purelib.Data.Rat.Fraction.Order.Basic.max_le (bounded first List.mem_cons_self)
      (ih (fun item member => bounded item (List.mem_cons_of_mem _ member)))

namespace IndexedGrouping
variable {items : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained
  inputs outer data coefficients)} {width : Normalization.InverseRootPolynomial.Coordinate}

/-- Transport and maximal grouping preserve the paid reverse mesh width. -/
theorem reverse_width_bound (grouped :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping retained inputs outer data
  coefficients items)
    (nonnegative : 0 ≤ width) (bounded : ∀ item ∈ items, item.fragment.reverseSourceWidth ≤ width) :
    ∀ run ∈ grouped.runs,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.reverseSourceWidth run.fragments
        ≤ width := by
  intro run present
  apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseWidths.maximum_le _ _ nonnegative
  apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseWidths.fragmentsAt_bounded run.parent run.items
    (fun _ member => run.parent_eq member)
  intro item member
  exact bounded item ((congrArg (fun entries => item ∈ entries) grouped.flattened).mp
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseWidths.item_present grouped.runs present member))

end IndexedGrouping

/-- Every original piece and stationary junction contributes its retained width. -/
theorem indexedSideFragments_reverse_width {count : Nat}
    (pieces : Fin (count + 1) → Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment
      retained inputs outer data coefficients)
    (junctions : Fin count → Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained
      inputs outer data coefficients) {width : Normalization.InverseRootPolynomial.Coordinate}
    (pieceBound : ∀ position, (pieces position).fragment.reverseSourceWidth ≤ width)
    (junctionBound : ∀ position, (junctions position).fragment.reverseSourceWidth ≤ width) :
    ∀ item ∈ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments pieces
      junctions, item.fragment.reverseSourceWidth ≤ width := by
  induction count with
  | zero =>
    intro item member
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact pieceBound 0
    · cases member
  | succ count ih =>
    intro item member
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact pieceBound 0
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact junctionBound 0
    exact ih (fun position => pieces position.succ) (fun position => junctions position.succ)
      (fun position => pieceBound position.succ) (fun position => junctionBound position.succ) item member

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseWidths
