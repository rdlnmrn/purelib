import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Geometry.FiniteGeometric
import CCL.Progressive.Approximation

/-!
# Finite sampling of a progressive name

Every state below is obtained by one explicitly requested finite refinement.
Its displayed sample is the process's finite rational witness at that state.
The construction never selects or names a value common to all states.
-/

namespace CCL.ProgressiveSampling

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation

open RFAP.ConstructiveGaussian.Gaussian

def refinementTarget (index : Nat) : Coordinate :=
  CCL.FiniteGeometric.quarterRadius 1 index

theorem refinementTarget_pos (index : Nat) : 0 < refinementTarget index :=
  CCL.FiniteGeometric.quarterRadius_pos (by decide) index

theorem refinementTarget_le_one (index : Nat) : refinementTarget index ≤ 1 :=
  CCL.FiniteGeometric.quarterRadius_le_scale (by decide) index

/-- A nested path of finite process states.  State zero is itself a genuine
refinement, so every displayed state has the same geometric accuracy form. -/
def stateAt (process : Process) (start : process.State) : Nat → process.State
  | 0 => process.refine start (refinementTarget 0) (refinementTarget_pos 0)
  | index + 1 =>
      process.refine (stateAt process start index)
        (refinementTarget (index + 1)) (refinementTarget_pos (index + 1))

@[simp] theorem stateAt_zero (process : Process) (start : process.State) :
    stateAt process start 0 =
      process.refine start (refinementTarget 0) (refinementTarget_pos 0) := rfl

@[simp] theorem stateAt_succ (process : Process) (start : process.State)
    (index : Nat) :
    stateAt process start (index + 1) =
      process.refine (stateAt process start index)
        (refinementTarget (index + 1)) (refinementTarget_pos (index + 1)) := rfl

theorem stateAt_accurate (process : Process) (start : process.State)
    (index : Nat) :
    (process.ball (stateAt process start index)).radiusSq <
      refinementTarget index := by
  cases index with
  | zero => exact process.accurate start _ _
  | succ index => exact process.accurate (stateAt process start index) _ _

theorem stateAt_possible_persists_add (process : Process)
    (start : process.State) (earlier : Nat) :
    ∀ (extra : Nat) {value : Gaussian},
      process.Possible (stateAt process start (earlier + extra)) value →
        process.Possible (stateAt process start earlier) value
  | 0, _, possible => by
      simpa only [Nat.add_zero] using possible
  | extra + 1, value, possible => by
      have atPrevious :
          process.Possible (stateAt process start (earlier + extra)) value := by
        apply process.refine_persists
          (stateAt process start (earlier + extra))
          (refinementTarget (earlier + extra + 1))
          (refinementTarget_pos (earlier + extra + 1))
        simpa only [stateAt_succ,
          show earlier + (extra + 1) = earlier + extra + 1 by ring1] using possible
      exact stateAt_possible_persists_add process start earlier extra atPrevious

theorem stateAt_possible_persists (process : Process) (start : process.State)
    {earlier later : Nat} (order : earlier ≤ later) {value : Gaussian}
    (possible : process.Possible (stateAt process start later) value) :
    process.Possible (stateAt process start earlier) value := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  exact stateAt_possible_persists_add process start earlier extra possible

def witnessAt (process : Process) (start : process.State) (index : Nat) :
    Gaussian :=
  (process.witness (stateAt process start index)).val

theorem witnessAt_possible (process : Process) (start : process.State)
    (index : Nat) :
    process.Possible (stateAt process start index)
      (witnessAt process start index) :=
  (process.witness (stateAt process start index)).property

theorem witnessAt_later_possible (process : Process) (start : process.State)
    {earlier later : Nat} (order : earlier ≤ later) :
    process.Possible (stateAt process start earlier)
      (witnessAt process start later) :=
  stateAt_possible_persists process start order
    (witnessAt_possible process start later)

theorem stateAt_possible_at_start (process : Process) (start : process.State)
    (index : Nat) {value : Gaussian}
    (possible : process.Possible (stateAt process start index) value) :
    process.Possible start value := by
  have atZero : process.Possible (stateAt process start 0) value :=
    stateAt_possible_persists process start (Nat.zero_le index) possible
  exact process.refine_persists start (refinementTarget 0)
    (refinementTarget_pos 0) atZero

theorem witnessAt_possible_start (process : Process) (start : process.State)
    (index : Nat) :
    process.Possible start (witnessAt process start index) :=
  stateAt_possible_at_start process start index
    (witnessAt_possible process start index)

private theorem center_sub_eq_neg_sub (center value : Gaussian) :
    center - value = -(value - center) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1

private theorem later_sub_earlier (later center earlier : Gaussian) :
    later - earlier = (later - center) + (center - earlier) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im] <;> ring1

/-- Two later finite witnesses are close because both are explicit candidates
inside the earlier finite ball. -/
theorem witnessAt_later_close (process : Process) (start : process.State)
    {earlier later : Nat} (order : earlier ≤ later) :
    normSq (witnessAt process start later - witnessAt process start earlier) ≤
      CCL.FiniteGeometric.quarterRadius 4 earlier := by
  let state := stateAt process start earlier
  let center := (process.ball state).center
  let radius := (process.ball state).radiusSq
  have laterInside := process.possible_inside
    (witnessAt_later_possible process start order)
  have earlierInside := process.possible_inside
    (witnessAt_possible process start earlier)
  have centerEarlierInside :
      normSq (center - witnessAt process start earlier) ≤ radius := by
    rw [center_sub_eq_neg_sub, normSq_neg]
    exact earlierInside
  have radiusLeTarget : radius ≤ refinementTarget earlier :=
    (stateAt_accurate process start earlier).le
  calc
    normSq (witnessAt process start later - witnessAt process start earlier) =
        normSq ((witnessAt process start later - center) +
          (center - witnessAt process start earlier)) := by
      rw [later_sub_earlier]
    _ ≤ 2 * (normSq (witnessAt process start later - center) +
        normSq (center - witnessAt process start earlier)) :=
      normSq_add_le_two _ _
    _ ≤ 2 * (radius + radius) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add laterInside centerEarlierInside) (by decide)
    _ = 4 * radius := by ring1
    _ ≤ 4 * refinementTarget earlier :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusLeTarget
        (by decide)
    _ = CCL.FiniteGeometric.quarterRadius 4 earlier := by
      rw [refinementTarget,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      ring1

theorem witnessAt_bounded (process : Process) (start : process.State)
    (index : Nat) :
    normSq (witnessAt process start index) ≤
      2 * (1 + process.centerBound) := by
  let state := stateAt process start index
  let center := (process.ball state).center
  let radius := (process.ball state).radiusSq
  have inside := process.possible_inside (witnessAt_possible process start index)
  have centerBound := process.center_bounded state
  have radiusLeOne : radius ≤ 1 :=
    (stateAt_accurate process start index).le.trans
      (refinementTarget_le_one index)
  have identity : witnessAt process start index =
      (witnessAt process start index - center) + center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  rw [identity]
  calc
    normSq ((witnessAt process start index - center) + center) ≤
        2 * (normSq (witnessAt process start index - center) + normSq center) :=
      normSq_add_le_two _ _
    _ ≤ 2 * (radius + process.centerBound) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add inside centerBound) (by decide)
    _ ≤ 2 * (1 + process.centerBound) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (calc
          radius + process.centerBound = process.centerBound + radius := by ring1
          _ ≤ process.centerBound + 1 :=
            add_le_add_right radiusLeOne process.centerBound
          _ = 1 + process.centerBound := by ring1)
        (by decide)

/-- A progressive name viewed only through a nested sequence of displayed
finite witnesses and rational pairwise-error allowances. -/
def approximation (name : Named) : Approximation where
  sample := witnessAt name.process name.state
  radiusSq := CCL.FiniteGeometric.quarterRadius 4
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg (by decide)
  later_close := witnessAt_later_close name.process name.state
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow 4 current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge 4 current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 4 (by decide)
  centerBound := 2 * (1 + name.process.centerBound)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) name.process.centerBound_nonneg)
  sample_bounded := witnessAt_bounded name.process name.state

end CCL.ProgressiveSampling
