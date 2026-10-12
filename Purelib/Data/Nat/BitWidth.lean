module

-- The exposed width uses the original binary logarithm operation.
public import Init.Data.Nat.Log2
import Purelib.Data.Nat.Division

/-!
# Displayed natural binary widths

The width is one plus the original natural binary logarithm. Its retained fuel
recursion compares ordered inputs and bounds each input by the corresponding
power of two, including the zero input.
-/

namespace Purelib.Data.Nat.BitWidth

/-- The fuel recursion in the logical model of the natural binary logarithm.

The fuel and value are displayed separately so that ordered computations can
be compared. This is the exact recursion used by `Nat.log2`. -/
-- Inline this proof model rather than emitting a separate recursor implementation.
@[macro_inline] private def log2Fuel (fuel value : Nat) : Nat :=
  fuel.rec (fun _ => 0)
    (fun _ ih input => (Nat.ble 2 input).rec 0 ((ih (input / 2)).succ)) value

/-- Increasing both retained fuel and value preserves logarithm order.

The two computations halve ordered values whenever the smaller value reaches
two. The smaller zero result otherwise gives the required lower bound. -/
private theorem log2Fuel_mono {firstFuel secondFuel left right : Nat}
    (fuelOrder : firstFuel ≤ secondFuel) (order : left ≤ right) :
    log2Fuel firstFuel left ≤ log2Fuel secondFuel right := by
  induction firstFuel generalizing secondFuel left right with
  | zero => exact Nat.zero_le _
  | succ firstFuel ih =>
      cases secondFuel with
      | zero => exact (Nat.not_succ_le_zero firstFuel fuelOrder).elim
      | succ secondFuel =>
          change Bool.rec (motive := fun _ => Nat) 0
              ((log2Fuel firstFuel (left / 2)).succ) (Nat.ble 2 left) ≤
            Bool.rec (motive := fun _ => Nat) 0
              ((log2Fuel secondFuel (right / 2)).succ) (Nat.ble 2 right)
          cases leftTest : Nat.ble 2 left with
          | false =>
              exact Nat.zero_le _
          | true =>
              have rightTest : Nat.ble 2 right = true :=
                Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true leftTest) order)
              rw [rightTest]
              exact Nat.succ_le_succ
                (ih (Nat.le_of_succ_le_succ fuelOrder) (Division.div_le_div_right order 2))

/-- A value covered by the fuel lies below its computed binary power ceiling.

A value below two uses the initial width one. Otherwise the retained quotient
fits the preceding fuel, and its remainder below two lifts the recursive
power ceiling to the next binary digit. -/
private theorem log2Fuel_upper {fuel value : Nat} (budget : value ≤ fuel) :
    value < 2 ^ (log2Fuel fuel value + 1) := by
  induction fuel generalizing value with
  | zero =>
      have zeroValue := Nat.eq_zero_of_le_zero budget
      cases zeroValue
      exact Nat.zero_lt_succ 1
  | succ fuel ih =>
      change value < 2 ^
        ((Nat.ble 2 value).rec 0 ((log2Fuel fuel (value / 2)).succ) + 1)
      cases test : Nat.ble 2 value with
      | false =>
          have small : value < 2 := Nat.lt_of_not_le (by
            intro large
            have same := Nat.ble_eq_true_of_le large
            rw [test] at same
            cases same)
          exact small
      | true =>
          have large : 2 ≤ value := Nat.le_of_ble_eq_true test
          have positive : 0 < value := Nat.lt_of_lt_of_le (by decide) large
          have quotientLess : value / 2 < value :=
            Division.div_lt_self positive (by decide)
          have quotientBudget : value / 2 ≤ fuel :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le quotientLess budget)
          have quotientBound := ih quotientBudget
          have remainderBound : value % 2 < 2 := Nat.mod_lt value (by decide)
          have reconstruct := Division.mod_add_div value 2
          calc
            value = value % 2 + 2 * (value / 2) := reconstruct.symm
            _ < 2 + 2 * (value / 2) := Nat.add_lt_add_right remainderBound _
            _ = 2 * (value / 2 + 1) := by
              rw [Nat.mul_succ]
              exact Nat.add_comm _ _
            _ ≤ 2 * 2 ^ (log2Fuel fuel (value / 2) + 1) :=
              Nat.mul_le_mul_left 2 quotientBound
            _ = 2 ^ ((log2Fuel fuel (value / 2)).succ + 1) := by
              rw [Nat.pow_succ]
              exact Nat.mul_comm _ _

/-- Compute one plus the natural base-two logarithm.

This width convention assigns one bit to zero and uses the integer binary
magnitude width for every positive value. -/
@[expose] public def natWidth (value : Nat) : Nat := Nat.log2 value + 1

/-- The natural binary width includes at least its zero/sign bit. -/
public theorem natWidth_positive (value : Nat) : 0 < natWidth value := by
  unfold natWidth
  exact Nat.zero_lt_succ _

/-- Increasing a natural value cannot decrease its displayed binary width.

The binary logarithm is compared through its exact retained fuel recursion,
with both fuel and input ordered by the supplied value bound. -/
public theorem natWidth_mono {left right : Nat} (order : left ≤ right) :
    natWidth left ≤ natWidth right := by
  change log2Fuel left left + 1 ≤ log2Fuel right right + 1
  exact Nat.add_le_add_right (log2Fuel_mono order order) 1

/-- A natural value is strictly below two raised to its binary width.

The original logarithm uses the value itself as fuel. The fuel-covered bound
therefore applies to every value, including zero, without selecting a different
logarithm computation. -/
public theorem lt_two_pow_natWidth (value : Nat) : value < 2 ^ natWidth value := by
  change value < 2 ^ (log2Fuel value value + 1)
  exact log2Fuel_upper (Nat.le_refl value)

/-- Doubling a positive natural value increases its displayed binary width.

Any value covering twice the positive input has at least one more binary digit.
The comparison uses the original logarithm fuel recursion and exact halving. -/
public theorem natWidth_lt_of_two_mul_le {left right : Nat}
    (positive : 0 < left) (twiceLe : 2 * left ≤ right) :
    natWidth left < natWidth right := by
  have doubled : natWidth left + 1 ≤ natWidth (2 * left) := by
    cases left with
    | zero => exact (Nat.not_lt_zero 0 positive).elim
    | succ value =>
        have test : Nat.ble 2 (2 * (value + 1)) = true :=
          Nat.ble_eq_true_of_le
            (Nat.mul_le_mul_left 2 (Nat.succ_le_succ (Nat.zero_le value)))
        have divided : (2 * (value + 1)) / 2 = value + 1 :=
          Division.mul_div_cancel_left (value + 1) (by decide)
        have fuelBound : value + 1 ≤ 2 * value + 1 :=
          Nat.succ_le_succ (Nat.le_mul_of_pos_left value (by decide))
        change log2Fuel (value + 1) (value + 1) + 1 + 1 ≤
          (Nat.ble 2 (2 * (value + 1))).rec 0
            ((log2Fuel (2 * value + 1) ((2 * (value + 1)) / 2)).succ) + 1
        rewrite [test, divided]
        exact Nat.add_le_add_right
          (log2Fuel_mono fuelBound (Nat.le_refl (value + 1))) 2
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (natWidth left))
    (Nat.le_trans doubled (natWidth_mono twiceLe))

end Purelib.Data.Nat.BitWidth
