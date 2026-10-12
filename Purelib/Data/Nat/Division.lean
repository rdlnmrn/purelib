module

public import Init.Data.Nat.Div.Basic
import Purelib.Data.Nat.Remainder
import Purelib.Data.Nat.Subtraction

namespace Purelib.Data.Nat.Division

/-- Sufficient fuel does not change the core quotient computation.

The retained bounds certify two runs of the original subtraction procedure
with the same positive divisor and dividend. -/
private theorem fuel_congr (value divisor firstFuel secondFuel : Nat)
    (positive : 0 < divisor) (firstBound : value < firstFuel)
    (secondBound : value < secondFuel) :
    Nat.div.go divisor positive firstFuel value firstBound =
      Nat.div.go divisor positive secondFuel value secondBound := by
  match firstFuel, secondFuel with
  | 0, _ => exact False.elim (Nat.not_lt_zero value firstBound)
  | _, 0 => exact False.elim (Nat.not_lt_zero value secondBound)
  | firstFuel + 1, secondFuel + 1 =>
      rw [Nat.div.go, Nat.div.go]
      by_cases retained : divisor ≤ value
      · rw [dif_pos retained, dif_pos retained]
        exact congrArg (· + 1)
          (fuel_congr (value - divisor) divisor firstFuel secondFuel positive _ _)
      · rw [dif_neg retained, dif_neg retained]
termination_by structural firstFuel

/-- Natural division takes one subtraction step exactly when the divisor fits.

A positive divisor bounded by the dividend is subtracted once and contributes
one to the quotient. Otherwise the quotient is zero, including division by zero. -/
public theorem div_eq (value divisor : Nat) : value / divisor =
    if 0 < divisor ∧ divisor ≤ value then (value - divisor) / divisor + 1 else 0 := by
  change Nat.div value divisor =
    if 0 < divisor ∧ divisor ≤ value then Nat.div (value - divisor) divisor + 1 else 0
  unfold Nat.div
  by_cases positive : 0 < divisor
  · rw [dif_pos positive]
    by_cases retained : divisor ≤ value
    · rw [if_pos ⟨positive, retained⟩, dif_pos positive, Nat.div.go, dif_pos retained]
      exact congrArg (· + 1)
        (fuel_congr (value - divisor) divisor value (value - divisor + 1) positive _ _)
    · rw [if_neg (fun condition => retained condition.2), Nat.div.go, dif_neg retained]
  · rw [if_neg (fun condition => positive condition.1), dif_neg positive]

/-- Sufficient common fuel certifies the core quotient and remainder identity.

Both procedures subtract the same positive divisor at each retained step.
Their ordinary outputs reconstruct the original natural dividend. -/
private theorem core_mod_add_div (divisor : Nat) (positive : 0 < divisor) :
    ∀ fuel value : Nat, ∀ bound : value < fuel,
      Nat.modCore.go divisor positive fuel value bound +
        divisor * Nat.div.go divisor positive fuel value bound = value
  | 0, value, bound => False.elim (Nat.not_lt_zero value bound)
  | fuel + 1, value, bound => by
      rw [Nat.modCore.go, Nat.div.go]
      by_cases retained : divisor ≤ value
      · rw [dif_pos retained, dif_pos retained, Nat.mul_succ, ← Nat.add_assoc,
          core_mod_add_div divisor positive fuel (value - divisor)]
        exact (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le retained)
      · rw [dif_neg retained, dif_neg retained, Nat.mul_zero, Nat.add_zero]

/-- The natural remainder and quotient reconstruct the original dividend.

The equation uses the original executable division and remainder operations,
including their total zero-divisor behavior. Positive divisors use the same
retained fuel for both core subtraction procedures. -/
public theorem mod_add_div (value divisor : Nat) :
    value % divisor + divisor * (value / divisor) = value := by
  rw [← Remainder.core_eq]
  change Nat.modCore value divisor + divisor * Nat.div value divisor = value
  unfold Nat.modCore Nat.div
  by_cases positive : 0 < divisor
  · rw [dif_pos positive, dif_pos positive]
    exact core_mod_add_div divisor positive (value + 1) value (Nat.lt_succ_self value)
  · rw [dif_neg positive, dif_neg positive, Nat.mul_zero, Nat.add_zero]

/-- Dividing a displayed multiple by a positive natural factor recovers its multiplier. -/
public theorem mul_div_cancel_left (multiplier : Nat) {divisor : Nat}
    (positive : 0 < divisor) : divisor * multiplier / divisor = multiplier := by
  induction multiplier with
  | zero =>
      rw [Nat.mul_zero, div_eq, if_neg (fun condition =>
        Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le condition.1 condition.2))]
  | succ multiplier ih =>
      rw [Nat.mul_succ, div_eq, if_pos ⟨positive, Nat.le_add_left divisor _⟩,
        Nat.add_comm (divisor * multiplier) divisor, Subtraction.add_sub_cancel_left, ih]

/-- Multiplying a divisible natural quotient back by its divisor recovers the dividend.

The retained divisibility witness supplies the original multiplier. The
zero-divisor case uses its displayed zero product directly. -/
public theorem div_mul_cancel {divisor value : Nat} (retained : divisor ∣ value) :
    value / divisor * divisor = value := by
  obtain ⟨multiplier, equation⟩ := retained
  rw [equation]
  cases divisor with
  | zero => rw [Nat.zero_mul, Nat.mul_zero]
  | succ divisor =>
      rw [mul_div_cancel_left multiplier (Nat.zero_lt_succ divisor), Nat.mul_comm]

/-- Dividing a natural value by one preserves it. -/
public theorem div_one (value : Nat) : value / 1 = value := by
  have remainderZero : value % 1 = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.mod_lt value (Nat.zero_lt_succ 0)))
  have reconstruct := mod_add_div value 1
  rw [remainderZero, Nat.zero_add, Nat.one_mul] at reconstruct
  exact reconstruct

/-- A natural quotient never exceeds its dividend.

A positive divisor contains at least one copy of each quotient unit in the
retained remainder equation. Division by zero gives the original total zero
quotient. -/
public theorem div_le_self (value divisor : Nat) : value / divisor ≤ value := by
  cases divisor with
  | zero =>
      rw [div_eq, if_neg (fun condition => Nat.lt_irrefl 0 condition.1)]
      exact Nat.zero_le value
  | succ divisor =>
      have reconstruct := mod_add_div value (divisor + 1)
      have productBound : (divisor + 1) * (value / (divisor + 1)) ≤
          value % (divisor + 1) + (divisor + 1) * (value / (divisor + 1)) :=
        Nat.le_add_left _ _
      rw [reconstruct] at productBound
      apply Nat.le_trans _ productBound
      rw [Nat.succ_mul]
      exact Nat.le_add_left _ _

/-- A positive natural dividend divided by a divisor greater than one decreases.

The original remainder equation bounds the divisor times its quotient by the
dividend. Equality of the quotient with that positive dividend would violate
strict growth of multiplication by the retained divisor. -/
public theorem div_lt_self {value divisor : Nat} (valuePositive : 0 < value)
    (divisorLarge : 1 < divisor) : value / divisor < value := by
  apply Nat.lt_of_le_of_ne (div_le_self value divisor)
  intro sameQuotient
  have reconstruction := mod_add_div value divisor
  rewrite [sameQuotient] at reconstruction
  have productBound : divisor * value ≤ value := by
    calc
      divisor * value ≤ value % divisor + divisor * value := Nat.le_add_left _ _
      _ = value := reconstruction
  have grows : 1 * value < divisor * value :=
    Nat.mul_lt_mul_of_pos_right divisorLarge valuePositive
  rewrite [Nat.one_mul] at grows
  exact Nat.not_le_of_gt grows productBound

/-- Dividing a positive natural number by itself gives the unit quotient.

The original quotient procedure cancels the displayed value as the factor in
its own unit multiple. No alternative quotient or division algorithm is used. -/
public theorem div_self {value : Nat} (positive : 0 < value) : value / value = 1 := by
  have cancellation := mul_div_cancel_left 1 positive
  rewrite [Nat.mul_one] at cancellation
  exact cancellation

/-- A positive natural divisor no larger than its dividend gives a positive quotient.

The retained bounds force the first subtraction step of ordinary division,
so its quotient is a successor regardless of the remaining dividend. -/
public theorem div_pos {divisor value : Nat} (bound : divisor ≤ value)
    (positive : 0 < divisor) : 0 < value / divisor := by
  rw [div_eq, if_pos ⟨positive, bound⟩]
  exact Nat.zero_lt_succ _

/-- Dividing zero by any natural divisor gives zero. -/
public theorem zero_div (divisor : Nat) : 0 / divisor = 0 := by
  rw [div_eq, if_neg (fun condition =>
    Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le condition.1 condition.2))]

/-- A natural dividend smaller than its divisor has zero quotient. -/
public theorem div_eq_of_lt {value divisor : Nat} (bound : value < divisor) :
    value / divisor = 0 := by
  rw [div_eq, if_neg (fun condition => Nat.not_le_of_gt bound condition.2)]

/-- Adding a natural multiple of a positive divisor shifts its quotient.

Each displayed multiple contributes one subtraction step to ordinary natural
division. The remaining dividend and its quotient are retained unchanged. -/
public theorem mul_add_div {divisor : Nat} (positive : 0 < divisor)
    (factor tail : Nat) :
    (divisor * factor + tail) / divisor = factor + tail / divisor := by
  induction factor with
  | zero => rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add]
  | succ factor ih =>
      rw [Nat.mul_succ, Nat.add_assoc, Nat.add_comm divisor tail,
        ← Nat.add_assoc, Nat.add_comm (divisor * factor + tail) divisor,
        div_eq, if_pos ⟨positive, Nat.le_add_right divisor _⟩,
        Subtraction.add_sub_cancel_left, ih]
      rw [Nat.add_assoc, Nat.add_comm (tail / divisor) 1, ← Nat.add_assoc]

/-- Common retained fuel preserves the order of two quotient computations.

Both dividends use the same positive divisor. Each successful subtraction
preserves their order and contributes one to both quotients. -/
private theorem core_mono (divisor : Nat) (positive : 0 < divisor)
    (fuel left right : Nat) (leftBound : left < fuel) (rightBound : right < fuel)
    (order : left ≤ right) :
    Nat.div.go divisor positive fuel left leftBound ≤
      Nat.div.go divisor positive fuel right rightBound := by
  induction fuel generalizing left right with
  | zero => exact (Nat.not_lt_zero left leftBound).elim
  | succ fuel ih =>
      rw [Nat.div.go, Nat.div.go]
      by_cases leftFits : divisor ≤ left
      · rw [dif_pos leftFits, dif_pos (Nat.le_trans leftFits order)]
        exact Nat.add_le_add_right (ih _ _ _ _ (Nat.sub_le_sub_right order divisor)) 1
      · rw [dif_neg leftFits]
        exact Nat.zero_le _

/-- Increasing a natural dividend cannot decrease its quotient.

The comparison uses the original subtraction procedure with common retained
fuel. Division by zero has the original total zero value on both sides. -/
public theorem div_le_div_right {left right : Nat} (order : left ≤ right)
    (divisor : Nat) : left / divisor ≤ right / divisor := by
  cases divisor with
  | zero =>
      rw [div_eq left 0, div_eq right 0,
        if_neg (fun condition => Nat.lt_irrefl 0 condition.1)]
      exact Nat.le_refl 0
  | succ divisor =>
      change Nat.div left (divisor + 1) ≤ Nat.div right (divisor + 1)
      unfold Nat.div
      rw [dif_pos (Nat.zero_lt_succ divisor), dif_pos (Nat.zero_lt_succ divisor)]
      rw [fuel_congr left (divisor + 1) (left + 1) (right + 1)
        (Nat.zero_lt_succ divisor) (Nat.lt_succ_self left)
        (Nat.lt_succ_of_le order)]
      exact core_mono (divisor + 1) (Nat.zero_lt_succ divisor) (right + 1)
        left right (Nat.lt_succ_of_le order) (Nat.lt_succ_self right) order

/-- A dividend below the next displayed divisor multiple has quotient at most the retained bound.

The quotient and remainder reconstruct the same natural dividend. If the
quotient exceeded the bound, monotonicity of multiplication would put that
next multiple inside the dividend, contradicting the supplied strict bound.
The zero-divisor case is covered by the impossible strict premise. -/
public theorem div_le_of_lt_mul_succ {value divisor bound : Nat}
    (below : value < divisor * (bound + 1)) : value / divisor ≤ bound := by
  have reconstructed := mod_add_div value divisor
  by_cases ordered : value / divisor ≤ bound
  · exact ordered
  · have beyond : bound + 1 ≤ value / divisor := Nat.lt_of_not_ge ordered
    have multiple := Nat.mul_le_mul_left divisor beyond
    have contained := Nat.le_add_left (divisor * (value / divisor)) (value % divisor)
    rw [reconstructed] at contained
    exact False.elim (Nat.not_lt_of_ge (Nat.le_trans multiple contained) below)

end Purelib.Data.Nat.Division
