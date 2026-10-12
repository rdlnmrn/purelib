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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Init.Prelude
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
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

/-! Derive descending common-source chains while retaining physical fragment order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains (SourceChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains (ReverseSourceChain)
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

/-- Transporting to an equal retained parent preserves nonincreasing original source parameters. -/
theorem castParent_descending (same : first = last)
    (fragment : IndexedFragments.ParentFragment retained inputs outer data coefficients first)
    (ordered : ∀ edge : Fin fragment.vertices, fragment.parameters edge.succ ≤ fragment.parameters edge.castSucc) :
    ∀ edge : Fin (fragment.castParent same).vertices,
      (fragment.castParent same).parameters edge.succ ≤ (fragment.castParent same).parameters edge.castSucc := by
  cases same
  exact ordered

end ParentFragment
namespace IndexedFragment

/-- Every source step of the retained original indexed fragment is nonincreasing.

Every successor edge compares the retained parameters in reverse order on the same fragment and finite vertex indices.
-/
@[expose]
def Decreasing (item : IndexedFragments.IndexedFragment retained inputs outer data coefficients) : Prop :=
  ∀ edge : Fin item.fragment.vertices,
    item.fragment.parameters edge.succ ≤ item.fragment.parameters edge.castSucc

/-- Consecutive original fragments share a parameter at the same parent or use zero and one at a changed parent.

A common parent requires exact endpoint agreement. A changed parent uses the
preceding terminal parameter zero and the next initial parameter one. -/
@[expose]
def ReverseJoined (before after : IndexedFragments.IndexedFragment retained inputs outer data coefficients) : Prop :=
  (before.parent = after.parent → before.lastParameter = after.firstParameter) ∧
  (before.parent ≠ after.parent → before.lastParameter = 0 ∧ after.firstParameter = 1)

/-- The original indexed fragment tail retains every descending join and finishes at parameter zero.

Each retained successor supplies its reverse join with the preceding fragment; the empty tail fixes the final parameter
at zero. -/
@[expose]
def ReverseAfter (before : IndexedFragments.IndexedFragment retained inputs outer data coefficients) :
    List (IndexedFragments.IndexedFragment retained inputs outer data coefficients) → Prop
  | [] => before.lastParameter = 0
  | after :: rest => before.ReverseJoined after ∧
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ReverseAfter after
    rest

/-- The original indexed fragments form a complete joined parameter word from one to zero.

The first fragment starts at parameter one, consecutive fragments keep their reverse joins, and the final fragment ends
at zero. -/
@[expose]
def ReverseWord : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients) → Prop
  | [] => True
  | first :: rest => first.firstParameter = 1 ∧
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ReverseAfter first rest

end IndexedFragment

/-- The supplied retained parent differs from the first indexed fragment's parent, when present. -/
private def apart (parent : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length) :
    List (IndexedFragments.IndexedFragment retained inputs outer data coefficients) → Prop
  | [] => True
  | item :: _ => parent ≠ item.parent

/-- A maximal original-parent fragment segment forms a descending source chain through zero and leaves a complete
descending parameter word. -/
private theorem finish_run
    (parent : Fin (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length)
    (first : IndexedFragments.IndexedFragment retained inputs outer data coefficients)
    (rest after : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients))
    (same : ∀ item ∈ first :: rest, item.parent = parent)
    (ends : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ReverseAfter first
      (rest ++ after)) (separate : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.apart
      parent after)
    (descending : ∀ item ∈ first :: rest, item.Decreasing) :
    ReverseSourceChains.ReverseSourceChain (IndexedRun.fragmentsAt parent (first :: rest) same) first.firstParameter 0 ∧
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ReverseWord after := by
  induction rest generalizing first with
  | nil =>
    have last : first.lastParameter = 0 ∧
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ReverseWord after := by
      cases after with
      | nil => exact ⟨ends, True.intro⟩
      | cons next tail =>
        have different : first.parent ≠ next.parent := fun equal =>
          separate ((same first List.mem_cons_self).symm.trans equal)
        have joined := ends.1.2 different
        exact ⟨joined.1, joined.2, ends.2⟩
    let fragment := first.fragment.castParent (same first List.mem_cons_self)
    have tail : ReverseSourceChains.ReverseSourceChain ([] : List (IndexedFragments.ParentFragment retained inputs outer
      data coefficients parent))
        (fragment.parameters (Fin.last fragment.vertices)) 0 := by
      rw [ParentFragment.castParent_last]
      change ReverseSourceChains.ReverseSourceChain [] first.lastParameter 0
      rw [last.1]
      exact .nil 0
    have chain := ReverseSourceChain.cons fragment
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment.castParent_descending _
        _ (descending first List.mem_cons_self)) tail
    rw [ParentFragment.castParent_first] at chain
    exact ⟨chain, last.2⟩
  | cons next rest ih =>
    have result := ih next (fun item member => same item (List.mem_cons_of_mem first member)) ends.2
      (fun item member => descending item (List.mem_cons_of_mem first member))
    have joined := ends.1.1 ((same first List.mem_cons_self).trans
      (same next (List.mem_cons_of_mem first List.mem_cons_self)).symm)
    let fragment := first.fragment.castParent (same first List.mem_cons_self)
    have tail : ReverseSourceChains.ReverseSourceChain (IndexedRun.fragmentsAt parent (next :: rest)
        (fun item member => same item (List.mem_cons_of_mem first member)))
        (fragment.parameters (Fin.last fragment.vertices)) 0 := by
      rw [ParentFragment.castParent_last]
      change ReverseSourceChains.ReverseSourceChain _ first.lastParameter 0
      rw [joined]
      exact result.1
    have chain := ReverseSourceChain.cons fragment
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment.castParent_descending _
        _ (descending first List.mem_cons_self)) tail
    rw [ParentFragment.castParent_first] at chain
    exact ⟨chain, result.2⟩

/-- Every separated group of the original decreasing joined fragment word forms a complete source chain from one to
zero.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
private theorem runs_chains (runs : List (FragmentGrouping.IndexedRun retained inputs outer data coefficients))
    (separated : IndexedRun.separated runs)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ReverseWord
      (runs.map IndexedRun.items).flatten)
    (descending : ∀ item ∈ (runs.map IndexedRun.items).flatten, item.Decreasing) :
    ∀ run ∈ runs, ReverseSourceChains.ReverseSourceChain run.fragments 1 0 := by
  induction runs with
  | nil => intro _ member; cases member
  | cons run rest ih =>
    have separate : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.apart run.parent (rest.map
      IndexedRun.items).flatten := by
      cases rest with
      | nil => trivial
      | cons next tail => exact fun same => separated.1 (same.trans next.first_parent)
    have result := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.finish_run run.parent
      run.first run.rest (rest.map IndexedRun.items).flatten
      (fun _ member => run.parent_eq member) word.2 separate
      (fun item member => descending item (Membership.mem_append.mpr (Or.inl member)))
    have firstChain : ReverseSourceChains.ReverseSourceChain run.fragments 1 0 := by
      have chain := result.1
      rw [word.1] at chain
      exact chain
    have tailChains := ih separated.2 result.2
      (fun item member => descending item (Membership.mem_append.mpr (Or.inr member)))
    intro selected member
    rcases Membership.mem_cons.mp member with rfl | member
    · exact firstChain
    · exact tailChains selected member

namespace IndexedGrouping
variable {items : List
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs
  outer data coefficients)}

/-- The original word's certified joins imply a complete chain for each maximal group on its exact retained numerical
source owner. -/
theorem reverse_source_chains (grouped : FragmentGrouping.IndexedGrouping retained inputs outer data coefficients items)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ReverseWord items)
      (descending : ∀ item ∈ items, item.Decreasing) :
    ∀ run ∈ grouped.runs, ReverseSourceChains.ReverseSourceChain run.fragments 1 0 := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.runs_chains grouped.runs
    grouped.separated
  · rw [grouped.flattened]
    exact word
  · rw [grouped.flattened]
    exact descending

end IndexedGrouping

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
