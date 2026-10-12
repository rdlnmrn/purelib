module

public import Init.Data.Int.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Int.Divisibility

/-!
# Divisibility and product-order readbacks for natural integer casts

The original natural values and integer multiplier remain their nominal
owners. Constructive integer sign cases recover that same multiplier as a
natural whenever it divides two natural casts with positive divisor.
-/

open Purelib.Data

namespace Purelib.Data.Nat.Divisibility.IntCast

/-- Cancel a common right factor from a strict inequality of natural products.

Commutativity presents the original common factor on the left. The direct
natural order certificate determines the same strict order of the inputs. -/
public theorem nat_lt_of_mul_lt_mul_right
    {left right factor : Nat} (productLess : left * factor < right * factor) :
    left < right := by
  have reordered : factor * left < factor * right := by
    rw [Nat.mul_comm factor left, Nat.mul_comm factor right]
    exact productLess
  exact Nat.Order.lt_of_mul_lt_mul_left reordered

/-- Recover natural divisibility from divisibility between integer casts.

For a positive natural divisor the retained integer multiplier cannot be a
negative successor. Its natural sign case supplies its unchanged `toNat`
value as the factor, with the original integer equation cast back to Nat. -/
public theorem nat_dvd_of_int_natCast_dvd
    {divisor value : Nat} (divisorPositive : 0 < divisor)
    (integerDivides : (divisor : Int) ∣ (value : Int)) :
    divisor ∣ value := by
  obtain ⟨factor, factorEquation⟩ := integerDivides
  cases factor with
  | ofNat factor => exact ⟨factor, Int.ofNat.inj factorEquation⟩
  | negSucc factor =>
      cases divisor with
      | zero => exact (Nat.not_lt_zero _ divisorPositive).elim
      | succ divisor =>
          change Int.ofNat value =
            Int.negOfNat ((divisor + 1) * (factor + 1)) at factorEquation
          rw [Nat.mul_succ, Nat.add_succ] at factorEquation
          cases factorEquation

end Purelib.Data.Nat.Divisibility.IntCast
