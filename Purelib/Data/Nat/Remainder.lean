module

public import Init.Data.Nat.Div.Basic
import Purelib.Data.Nat.Subtraction

namespace Purelib.Data.Nat.Remainder

/-- Sufficient fuel does not change the core remainder computation.

The positive divisor and retained strict fuel bounds certify both runs of
the same subtraction procedure. -/
private theorem fuel_congr (value divisor firstFuel secondFuel : Nat)
    (positive : 0 < divisor) (firstBound : value < firstFuel)
    (secondBound : value < secondFuel) :
    Nat.modCore.go divisor positive firstFuel value firstBound =
      Nat.modCore.go divisor positive secondFuel value secondBound := by
  match firstFuel, secondFuel with
  | 0, _ => exact False.elim (Nat.not_lt_zero value firstBound)
  | _, 0 => exact False.elim (Nat.not_lt_zero value secondBound)
  | firstFuel + 1, secondFuel + 1 =>
      rw [Nat.modCore.go, Nat.modCore.go]
      by_cases retained : divisor ≤ value
      · rw [dif_pos retained, dif_pos retained]
        exact fuel_congr (value - divisor) divisor firstFuel secondFuel positive _ _
      · rw [dif_neg retained, dif_neg retained]
termination_by structural firstFuel

/-- The core remainder procedure subtracts a positive divisor when it fits. -/
private theorem core_step (value divisor : Nat) : Nat.modCore value divisor =
    if 0 < divisor ∧ divisor ≤ value then Nat.modCore (value - divisor) divisor
    else value := by
  unfold Nat.modCore
  by_cases positive : 0 < divisor
  · rw [dif_pos positive]
    by_cases retained : divisor ≤ value
    · rw [if_pos ⟨positive, retained⟩, dif_pos positive, Nat.modCore.go, dif_pos retained]
      exact fuel_congr (value - divisor) divisor value (value - divisor + 1) positive _ _
    · rw [if_neg (fun condition => retained condition.2), Nat.modCore.go, dif_neg retained]
  · rw [if_neg (fun condition => positive condition.1), dif_neg positive]

/-- The core subtraction procedure agrees with ordinary natural remainder. -/
public theorem core_eq (value divisor : Nat) : Nat.modCore value divisor = value % divisor := by
  cases value with
  | zero =>
      rw [core_step]
      exact if_neg (fun condition => Nat.lt_irrefl 0
        (Nat.lt_of_lt_of_le condition.1 condition.2))
  | succ value =>
      change Nat.modCore (value + 1) divisor = Nat.mod (value + 1) divisor
      rw [Nat.mod]
      by_cases retained : divisor ≤ value + 1
      · rw [if_pos retained]
      · rw [if_neg retained, core_step, if_neg (fun condition => retained condition.2)]

/-- Natural remainder takes one subtraction step exactly when the divisor fits.

A positive divisor bounded by the dividend is subtracted once. Otherwise the
remainder equals the dividend, including division by zero. -/
public theorem mod_eq (value divisor : Nat) : value % divisor =
    if 0 < divisor ∧ divisor ≤ value then (value - divisor) % divisor else value := by
  rw [← core_eq value divisor, ← core_eq (value - divisor) divisor]
  exact core_step value divisor

/-- A bounded natural dividend is its own original remainder.

The original subtraction procedure takes no step when its divisor is greater
than the supplied dividend. The equation uses the original total remainder. -/
public theorem mod_eq_of_lt {value divisor : Nat} (bound : value < divisor) :
    value % divisor = value := by
  rw [mod_eq, if_neg (fun condition => Nat.not_le_of_gt bound condition.2)]

/-- Subtracting a bounded divisor preserves the natural remainder. -/
public theorem mod_eq_sub_mod {value divisor : Nat} (retained : divisor ≤ value) :
    value % divisor = (value - divisor) % divisor := by
  cases divisor with
  | zero => rw [Nat.sub_zero]
  | succ divisor => rw [mod_eq, if_pos ⟨Nat.zero_lt_succ divisor, retained⟩]

/-- Adding a displayed divisor multiple preserves the natural remainder.

Each retained multiple contributes one subtraction step to the original
remainder procedure. The tail dividend and its remainder stay unchanged,
including when the divisor is zero. -/
public theorem mul_add_mod (divisor factor tail : Nat) :
    (divisor * factor + tail) % divisor = tail % divisor := by
  induction factor with
  | zero => rw [Nat.mul_zero, Nat.zero_add]
  | succ factor ih =>
      rw [Nat.mul_succ, Nat.add_assoc, Nat.add_comm divisor tail,
        ← Nat.add_assoc, Nat.add_comm (divisor * factor + tail) divisor,
        mod_eq_sub_mod (Nat.le_add_right divisor _), Subtraction.add_sub_cancel_left, ih]

end Purelib.Data.Nat.Remainder
