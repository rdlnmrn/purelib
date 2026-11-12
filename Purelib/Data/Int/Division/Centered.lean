module

public import Purelib.Data.Int.Division
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Order
import Purelib.Tactic.QuotientFreeOmega

/-! # Centered division by an even positive modulus

The ordinary integer quotient selects a remainder in [-radius, radius).
Opposite parities exclude the lower endpoint and give a strict decrease
of the absolute value. All quotients and bounds are finite executable data.
-/

public section

namespace Purelib.Data.Int.Division.Centered

/-- Divide after shifting by one radius, using twice the radius as the modulus. -/
@[expose] def quotient (value : Int) (radius : Nat) : Int :=
  (value + (radius : Int)) / (2 * (radius : Int))

/-- Subtract the selected even multiple from the original integer. -/
@[expose] def remainder (value : Int) (radius : Nat) : Int :=
  value - 2 * (radius : Int) * quotient value radius

/-- Casting twice the natural radius reads the same integer modulus. -/
private theorem double_cast (radius : Nat) : ((2 * radius : Nat) : Int) = 2 * (radius : Int) := by
  rewrite [Int.natCast_mul]
  rfl

/-- A positive radius puts the original remainder in its centered half-open interval.

The two ordinary quotient bounds apply to the shifted dividend. Subtracting
that same selected even multiple gives both retained endpoint inequalities.
-/
theorem bounds (value : Int) {radius : Nat} (positive : 0 < radius) :
    -(radius : Int) ≤ remainder value radius ∧ remainder value radius < (radius : Int) := by
  have modulusPositive : 0 < 2 * radius := Nat.mul_pos (of_decide_eq_true rfl) positive
  have lower := Division.mul_ediv_self_le (value + (radius : Int)) modulusPositive
  have upper := Division.lt_mul_ediv_self_add (value + (radius : Int)) modulusPositive
  rewrite [double_cast] at lower upper
  change 2 * (radius : Int) * quotient value radius ≤ value + (radius : Int) at lower
  change value + (radius : Int) <
    2 * (radius : Int) * quotient value radius + 2 * (radius : Int) at upper
  constructor
  · unfold remainder
    omega0
  · unfold remainder
    omega0

/-- The centered remainder has the original integer's parity. -/
theorem parity (value : Int) (radius : Nat) : remainder value radius % 2 = value % 2 := by
  unfold remainder
  rewrite [Arithmetic.mul_assoc]
  omega0

/-- Opposite parities rule out both boundary magnitudes and strictly decrease absolute value.

The positive radius gives the finite centered bounds. The even selected
multiple preserves parity, so the possible lower endpoint is excluded
without choosing a sign or a greatest common divisor witness.
-/
theorem natAbs_lt (value : Int) {radius : Nat} (positive : 0 < radius)
    (different : value % 2 ≠ (radius : Int) % 2) : (remainder value radius).natAbs < radius := by
  have bounded := bounds value positive
  have sameParity := parity value radius
  have strictLower : -(radius : Int) < remainder value radius := by
    have endpointNe : remainder value radius ≠ -(radius : Int) := by
      intro equal
      rewrite [equal] at sameParity
      omega0
    omega0
  have absolute (scalar : Int) (first : -(radius : Int) < scalar) (last : scalar < (radius : Int)) :
      scalar.natAbs < radius := by
    cases scalar with
    | ofNat scalar =>
        change (scalar : Int) < (radius : Int) at last
        exact Order.natCast_lt_iff.mp last
    | negSucc scalar =>
        change -(radius : Int) < -((scalar + 1 : Nat) : Int) at first
        change scalar + 1 < radius
        omega0
  exact absolute _ strictLower bounded.2

end Purelib.Data.Int.Division.Centered

end
