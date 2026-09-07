import FTA.BoxGeometry

/-!
# Finite winding arithmetic

The extraction argument ultimately uses only a finite list of integer child
windings, additivity, and nonnegativity.  This module isolates and proves that
discrete core, including the unique-child conclusion of Lemma 9.3.
-/

namespace FTA.WindingArithmetic

open scoped BigOperators

/-- Every member of a finite nonnegative integer family is bounded by its sum. -/
theorem value_le_sum {n : ℕ} (w : Fin n → ℤ) (h₀ : ∀ i, 0 ≤ w i) (i : Fin n) :
    w i ≤ ∑ j, w j := by
  exact Finset.single_le_sum (fun j _ => h₀ j) (Finset.mem_univ i)

/-- A nonnegative finite integer family summing to one has exactly one
winding-one member.  This is the arithmetic heart of Lemma 9.3. -/
theorem existsUnique_one {n : ℕ} (w : Fin n → ℤ)
    (h₀ : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃! i, w i = 1 := by
  have h01 : ∀ i, w i = 0 ∨ w i = 1 := by
    intro i
    have hle : w i ≤ 1 := (value_le_sum w h₀ i).trans_eq hsum
    have hnonneg := h₀ i
    omega
  have hex : ∃ i, w i = 1 := by
    by_contra h
    have hz : ∀ i, w i = 0 := fun i =>
      (h01 i).resolve_right (fun hi => h ⟨i, hi⟩)
    have : (∑ i, w i) = 0 := by simp [hz]
    omega
  rcases hex with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  have hdecomp := Finset.sum_erase_add (s := Finset.univ) (f := w)
    (Finset.mem_univ i)
  have herase : ∑ k ∈ Finset.univ.erase i, w k = 0 := by
    rw [hi, hsum] at hdecomp
    omega
  have hjmem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩
  have hjle : w j ≤ ∑ k ∈ Finset.univ.erase i, w k :=
    Finset.single_le_sum (fun k _ => h₀ k) hjmem
  rw [hj, herase] at hjle
  omega

/-- A finite certified subdivision records only the data used by additivity. -/
structure Subdivision (n : ℕ) where
  parentWinding : ℤ
  childWinding : Fin n → ℤ
  additive : ∑ i, childWinding i = parentWinding

theorem Subdivision.uniqueChild {n : ℕ} (S : Subdivision n)
    (hparent : S.parentWinding = 1) (hnonneg : ∀ i, 0 ≤ S.childWinding i) :
    ∃! i, S.childWinding i = 1 := by
  apply existsUnique_one S.childWinding hnonneg
  rw [S.additive, hparent]

/-- Raw-winding version used by the constructive box refinement.  The local
extraction theorem supplies the `4 ≤ w i` premise for every positive clear
child, avoiding any separate divisibility assumption on raw winding. -/
theorem existsUnique_four_of_positive_ge_four {n : ℕ} (w : Fin n → ℤ)
    (hnonnegative : ∀ i, 0 ≤ w i)
    (hpositive : ∀ i, 0 < w i → 4 ≤ w i)
    (hsum : ∑ i, w i = 4) : ∃! i, w i = 4 := by
  have hle : ∀ i, w i ≤ 4 := by
    intro i
    exact (value_le_sum w hnonnegative i).trans_eq hsum
  have hzeroOrFour : ∀ i, w i = 0 ∨ w i = 4 := by
    intro i
    by_cases hzero : w i = 0
    · exact Or.inl hzero
    · exact Or.inr (by
        have hstrict : 0 < w i := lt_of_le_of_ne (hnonnegative i) (Ne.symm hzero)
        exact le_antisymm (hle i) (hpositive i hstrict))
  have hexists : ∃ i, w i = 4 := by
    by_contra hnone
    have hallZero : ∀ i, w i = 0 := fun i =>
      (hzeroOrFour i).resolve_right (fun hi => hnone ⟨i, hi⟩)
    have : (∑ i, w i) = 0 := by simp [hallZero]
    omega
  rcases hexists with ⟨selected, hselected⟩
  refine ⟨selected, hselected, ?_⟩
  intro other hother
  by_contra hne
  have hselectedLe :
      w selected + w other ≤ ∑ i, w i := by
    let pair : Finset (Fin n) := {selected, other}
    have hpairSum : ∑ i ∈ pair, w i = w selected + w other := by
      simp [pair, Ne.symm hne]
    rw [← hpairSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ pair)
      fun i _ _ => hnonnegative i
  rw [hselected, hother, hsum] at hselectedLe
  omega

end FTA.WindingArithmetic
