module

public import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

/-! # Conjugation of original finite enclosure processes -/

public section

namespace Purelib.Approximation.Gaussian.Process

open Purelib.Data.Gaussian

/-- Conjugate every original enclosure and possible reading while retaining the original states and refinements.

Each possible output retains its original possible source reading. Conjugation
preserves all squared radii and centre bounds exactly.
-/
@[expose] def conj (process : Process) : Process where
  State := process.State
  ball state := (process.ball state).conj
  Possible state value := ∃ source, process.Possible state source ∧ value = Basic.conj source
  witness state :=
    ⟨Basic.conj (process.witness state).val, (process.witness state).val,
      (process.witness state).property, rfl⟩
  possible_inside := by
    rintro state value ⟨source, possible, rfl⟩
    change Norm.Basic.normSq (Basic.conj source - Basic.conj (process.ball state).center) ≤ _
    rw [Basic.conj_eq_canonical source, Basic.conj_eq_canonical (process.ball state).center,
      ← Basic.Canonical.conj_sub, ← Basic.conj_eq_canonical, Norm.Basic.normSq_conj]
    exact process.possible_inside possible
  refine := process.refine
  refine_persists := by
    rintro state target positive value ⟨source, possible, equal⟩
    exact ⟨source, process.refine_persists state target positive possible, equal⟩
  accurate := process.accurate
  centerBound := process.centerBound
  centerBound_nonneg := process.centerBound_nonneg
  center_bounded := by
    intro state
    change Norm.Basic.normSq (Basic.conj (process.ball state).center) ≤ _
    rw [Norm.Basic.normSq_conj]
    exact process.center_bounded state

namespace Apart

/-- Conjugation retains the same positive whole-ball floor at the same original states. -/
def conj {process : Process} (apart : Apart process) : Apart process.conj where
  lowerSq := apart.lowerSq
  positive := apart.positive
  lower := by
    intro state value inside
    have transformed := Norm.Basic.normSq_conj (value - Basic.conj (process.ball state).center)
    rewrite [Basic.conj_eq_canonical (value - Basic.conj (process.ball state).center),
      Basic.Canonical.conj_sub, ← Basic.conj_eq_canonical value,
      ← Basic.conj_eq_canonical (Basic.conj (process.ball state).center), Basic.conj_conj] at transformed
    have originalInside : (process.ball state).Contains (Basic.conj value) := by
      change Norm.Basic.normSq (Basic.conj value - (process.ball state).center) ≤ (process.ball state).radiusSq
      rewrite [transformed]
      exact inside
    have lower := apart.lower state originalInside
    rewrite [Norm.Basic.normSq_conj] at lower
    exact lower

/-- Conjugation changes no retained numerical lower quadrance. -/
theorem conj_lowerSq {process : Process} (apart : Apart process) : apart.conj.lowerSq = apart.lowerSq := by
  unfold conj
  rfl

end Apart

end Purelib.Approximation.Gaussian.Process

end
