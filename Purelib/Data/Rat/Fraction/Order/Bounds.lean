module
import Purelib.Algebra.NatCast
import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace Purelib.Data.Rat.Fraction.Order.Bounds

section TriangleSpreadRules

open Purelib.Data.Rat in
/-- For every rational, either it or its complement to one is at most one half. -/
theorem exercise_20_1 (spread : Fraction.Rational) :
    spread ≤ (1 : Fraction.Rational) / 2 ∨
      1 - spread ≤ (1 : Fraction.Rational) / 2 := by
  by_cases lowerHalf : spread ≤ (1 : Fraction.Rational) / 2
  · exact Or.inl lowerHalf
  · right
    have halfBelow : (1 : Fraction.Rational) / 2 < spread :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct lowerHalf
    have halfAtMost : (1 : Fraction.Rational) / 2 ≤ spread :=
      Fraction.Order.Arithmetic.le_of_lt_direct halfBelow
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct halfAtMost
    calc
      1 - spread = -spread + 1 := by ring1
      _ ≤ -((1 : Fraction.Rational) / 2) + 1 :=
        Fraction.Order.Arithmetic.add_le_add_right_direct reversed 1
      _ = (1 : Fraction.Rational) / 2 := by decide
end TriangleSpreadRules
end Purelib.Data.Rat.Fraction.Order.Bounds

end

namespace Purelib.Data.Rat.Fraction.Order.Bounds

open Purelib.Data.Rat

/-- A positive canonical rational is below one plus its natural numerator.

The retained positive numerator is an exact natural integer, and multiplying
by the positive stored denominator bounds the original rational strictly by
the successor of that same natural numerator. -/
public theorem positiveRational_lt_numerator_succ
    (value : Fraction.Rational) (positive : 0 < value) :
    value < (value.num.toNat + 1 : Nat) := by
  have numeratorPositive : (0 : Int) < value.num :=
    (Fraction.Order.Basic.zero_lt_iff_num_pos value).mp positive
  have numeratorCast : (value.num.toNat : Fraction.Rational) =
      (value.num : Fraction.Rational) := by
    obtain ⟨difference, equation⟩ := Purelib.Data.Int.Order.lt_dest numeratorPositive
    have numeratorEquation : ((difference + 1 : Nat) : Int) = value.num :=
      (Purelib.Data.Int.Arithmetic.zero_add _).symm.trans equation
    have integerEquality : (value.num.toNat : Int) = value.num := by
      rewrite [← numeratorEquation]
      rfl
    simpa only [Int.cast_natCast, -eq_self, -iff_self] using
      congrArg (fun integer : Int => (integer : Fraction.Rational)) integerEquality
  have denominatorPositive : (0 : Fraction.Rational) < (value.den : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct value.den_pos
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := (value.den : Fraction.Rational)) _ denominatorPositive
  change value *
      ((Fraction.Basic.representative value).den : Fraction.Rational) < _
  rw [Fraction.Cast.representative_mul_den value]
  have naturalCleared : value.num.toNat <
      (value.num.toNat + 1) * value.den := by
    have denominatorAtLeastOne : 1 ≤ value.den := value.den_pos
    calc
      value.num.toNat < value.num.toNat + 1 := Nat.lt_succ_self _
      _ = (value.num.toNat + 1) * 1 := by exact (Nat.mul_one _).symm
      _ ≤ (value.num.toNat + 1) * value.den :=
        Nat.mul_le_mul_left (value.num.toNat + 1) denominatorAtLeastOne
  have castCleared :=
    Fraction.Cast.Order.natCast_lt_direct naturalCleared
  change (value.num : Fraction.Rational) < _
  simpa only [Purelib.Algebra.NatCast.mul, Purelib.Algebra.NatCast.add, Nat.cast_one, numeratorCast, -eq_self,
    -iff_self] using
    castCleared

end Purelib.Data.Rat.Fraction.Order.Bounds
