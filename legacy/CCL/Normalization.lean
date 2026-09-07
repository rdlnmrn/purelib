import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega

/-!
# Bounded binary normalization

This module formalizes Lemma 3.1.  Each returned exponent is computed as the
maximum or minimum of a `Finset.range`; the bounds in that finite range are part
of the definition, so no unbounded minimization or logarithm is hidden here.
-/

namespace CCL

namespace BinaryNormalization

/-- The elementary estimate `n + 1 ≤ 2ⁿ` used to bound every scan. -/
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have : n + 2 ≤ 2 * (n + 1) := by omega
      simpa only [Nat.mul_comm] using this.trans (Nat.mul_le_mul_left 2 ih)

/-- A certified result of Lemma 3.1(a). -/
structure HighResult (A B : ℕ) where
  exponent : ℕ
  positive : 1 ≤ exponent
  lower : 2 ^ exponent * B ≤ A
  upper : A < 2 ^ (exponent + 1) * B

/-- A certified result of Lemma 3.1(b). -/
structure LowResult (A B : ℕ) where
  exponent : ℕ
  lower : B ≤ 2 ^ exponent * A
  upper : 2 ^ exponent * A < 2 * B

/-- A certified result of Lemma 3.1(c). -/
structure LoopResult (A B : ℕ) where
  exponent : ℕ
  lower : 2 ^ exponent * B < A
  upper : A ≤ 2 ^ (exponent + 1) * B

/-- Part (a): scan `1, …, A` and retain the last admissible exponent. -/
def high (A B : ℕ) (hB : 0 < B) (h : 2 * B ≤ A) : HighResult A B := by
  let S : Finset ℕ :=
    (Finset.range (A + 1)).filter fun k => 1 ≤ k ∧ 2 ^ k * B ≤ A
  have h1 : 1 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    constructor
    · omega
    · simpa using h
  let k := S.max' ⟨1, h1⟩
  have hkS : k ∈ S := Finset.max'_mem S ⟨1, h1⟩
  have hkData : k < A + 1 ∧ 1 ≤ k ∧ 2 ^ k * B ≤ A := by
    simpa only [S, Finset.mem_filter, Finset.mem_range] using hkS
  refine ⟨k, hkData.2.1, hkData.2.2, ?_⟩
  apply Nat.lt_of_not_ge
  intro hnext
  have hpow : k + 1 ≤ 2 ^ k := succ_le_two_pow k
  have hone : 1 ≤ B := hB
  have hkb : 2 ^ k ≤ 2 ^ k * B := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ k) hone
  have hbound : k + 1 < A + 1 := by omega
  have hnextS : k + 1 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨hbound, by omega, hnext⟩
  have hmax : k + 1 ≤ k := S.le_max' (k + 1) hnextS
  omega

/-- Exponents satisfying the high bracket are unique. -/
theorem high_unique {A B k l : ℕ} (hk₀ : 2 ^ k * B ≤ A)
    (hk₁ : A < 2 ^ (k + 1) * B) (hl₀ : 2 ^ l * B ≤ A)
    (hl₁ : A < 2 ^ (l + 1) * B) : k = l := by
  apply le_antisymm
  · apply Nat.le_of_not_gt
    intro hlk
    have hp : 2 ^ (l + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpm := Nat.mul_le_mul_right B hp
    omega
  · apply Nat.le_of_not_gt
    intro hkl
    have hp : 2 ^ (k + 1) ≤ 2 ^ l :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpm := Nat.mul_le_mul_right B hp
    omega

theorem high_isUnique (A B : ℕ) (hB : 0 < B) (h : 2 * B ≤ A) (l : ℕ)
    (hl₀ : 2 ^ l * B ≤ A) (hl₁ : A < 2 ^ (l + 1) * B) :
    (high A B hB h).exponent = l :=
  high_unique (high A B hB h).lower (high A B hB h).upper hl₀ hl₁

/-- Part (b): scan `0, …, B` and return the first successful exponent. -/
def low (A B : ℕ) (hA : 0 < A) (_hB : 0 < B) (h : A < 2 * B) : LowResult A B := by
  let S : Finset ℕ :=
    (Finset.range (B + 1)).filter fun m => B ≤ 2 ^ m * A
  have hpow : B + 1 ≤ 2 ^ B := succ_le_two_pow B
  have hone : 1 ≤ A := hA
  have hBA : B ≤ 2 ^ B * A := by
    have h₁ : B ≤ 2 ^ B := by omega
    exact h₁.trans (by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ B) hone)
  have hBS : B ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hBA⟩
  let m := S.min' ⟨B, hBS⟩
  have hmS : m ∈ S := Finset.min'_mem S ⟨B, hBS⟩
  have hmData : m < B + 1 ∧ B ≤ 2 ^ m * A := by
    simpa only [S, Finset.mem_filter, Finset.mem_range] using hmS
  refine ⟨m, hmData.2, ?_⟩
  by_cases hm : m = 0
  · simpa only [hm, pow_zero, one_mul] using h
  · obtain ⟨n, hmn⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [hmn]
    have hnBound : n < B + 1 := by omega
    have hnNot : n ∉ S := by
      intro hnS
      have hmin : m ≤ n := S.min'_le n hnS
      omega
    have hnFail : ¬B ≤ 2 ^ n * A := by
      intro hn
      apply hnNot
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨hnBound, hn⟩
    have hnlt : 2 ^ n * A < B := Nat.lt_of_not_ge hnFail
    calc
      2 ^ (n + 1) * A = 2 * (2 ^ n * A) := by
        rw [pow_succ]
        ac_rfl
      _ < 2 * B := (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnlt

/-- Exponents satisfying the low bracket are unique. -/
theorem low_unique {A B k l : ℕ} (_hA : 0 < A)
    (hk₀ : B ≤ 2 ^ k * A) (hk₁ : 2 ^ k * A < 2 * B)
    (hl₀ : B ≤ 2 ^ l * A) (hl₁ : 2 ^ l * A < 2 * B) : k = l := by
  apply le_antisymm
  · apply Nat.le_of_not_gt
    intro hlk
    have hsucc : l + 1 ≤ k := by omega
    have hp : 2 ^ (l + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hsucc
    have hpm : 2 * (2 ^ l * A) ≤ 2 ^ k * A := by
      calc
        2 * (2 ^ l * A) = 2 ^ (l + 1) * A := by
          rw [pow_succ]
          ac_rfl
        _ ≤ 2 ^ k * A := Nat.mul_le_mul_right A hp
    omega
  · apply Nat.le_of_not_gt
    intro hkl
    have hsucc : k + 1 ≤ l := by omega
    have hp : 2 ^ (k + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) hsucc
    have hpm : 2 * (2 ^ k * A) ≤ 2 ^ l * A := by
      calc
        2 * (2 ^ k * A) = 2 ^ (k + 1) * A := by
          rw [pow_succ]
          ac_rfl
        _ ≤ 2 ^ l * A := Nat.mul_le_mul_right A hp
    omega

theorem low_isUnique (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (h : A < 2 * B)
    (l : ℕ) (hl₀ : B ≤ 2 ^ l * A) (hl₁ : 2 ^ l * A < 2 * B) :
    (low A B hA hB h).exponent = l :=
  low_unique hA (low A B hA hB h).lower (low A B hA hB h).upper hl₀ hl₁

/-- Part (c): scan `0, …, A` and retain the last strict exponent. -/
def loop (A B : ℕ) (hB : 0 < B) (h : B < A) : LoopResult A B := by
  let S : Finset ℕ :=
    (Finset.range (A + 1)).filter fun k => 2 ^ k * B < A
  have h0 : 0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range, pow_zero, one_mul]
    exact ⟨by omega, h⟩
  let k := S.max' ⟨0, h0⟩
  have hkS : k ∈ S := Finset.max'_mem S ⟨0, h0⟩
  have hkData : k < A + 1 ∧ 2 ^ k * B < A := by
    simpa only [S, Finset.mem_filter, Finset.mem_range] using hkS
  refine ⟨k, hkData.2, ?_⟩
  apply Nat.le_of_not_gt
  intro hnext
  have hpow : k + 1 ≤ 2 ^ k := succ_le_two_pow k
  have hone : 1 ≤ B := hB
  have hkb : 2 ^ k ≤ 2 ^ k * B := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ k) hone
  have hbound : k + 1 < A + 1 := by omega
  have hnextS : k + 1 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨hbound, hnext⟩
  have hmax : k + 1 ≤ k := S.le_max' (k + 1) hnextS
  omega

/-- Exponents satisfying the strict loop bracket are unique. -/
theorem loop_unique {A B k l : ℕ} (hk₀ : 2 ^ k * B < A)
    (hk₁ : A ≤ 2 ^ (k + 1) * B) (hl₀ : 2 ^ l * B < A)
    (hl₁ : A ≤ 2 ^ (l + 1) * B) : k = l := by
  apply le_antisymm
  · apply Nat.le_of_not_gt
    intro hlk
    have hp : 2 ^ (l + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpm := Nat.mul_le_mul_right B hp
    omega
  · apply Nat.le_of_not_gt
    intro hkl
    have hp : 2 ^ (k + 1) ≤ 2 ^ l :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpm := Nat.mul_le_mul_right B hp
    omega

theorem loop_isUnique (A B : ℕ) (hB : 0 < B) (h : B < A) (l : ℕ)
    (hl₀ : 2 ^ l * B < A) (hl₁ : A ≤ 2 ^ (l + 1) * B) :
    (loop A B hB h).exponent = l :=
  loop_unique (loop A B hB h).lower (loop A B hB h).upper hl₀ hl₁

end BinaryNormalization

end CCL
