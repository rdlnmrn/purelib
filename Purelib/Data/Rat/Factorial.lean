module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.Choose.Factorial
public import Purelib.Data.Nat.Factorial.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Field

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Nat.Choose
import Purelib.Tactic.Ring

section
public section

/-! Data Rat Factorial and its finite structural certificates. -/

namespace Purelib.Data.Rat.Factorial

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- The product of reciprocal factorials at complementary indices equals the binomial coefficient divided by the row
factorial. -/
theorem reciprocal_factorial_product (row column : Nat)
    (order : column ≤ row) :
    (1 / (Factorial.Basic.factorial column : Fraction.Rational)) *
        (1 / (Factorial.Basic.factorial (row - column) : Fraction.Rational)) =
      (Choose.Pascal.choose row column : Fraction.Rational) / (Factorial.Basic.factorial row : Fraction.Rational) := by
  rw [Fraction.Compatibility.one_div_mul_one_div]
  have leftNonzero :
      ((Factorial.Basic.factorial column : Fraction.Rational) *
        (Factorial.Basic.factorial (row - column) : Fraction.Rational)) ≠ 0 :=
    Fraction.Field.mul_ne_zero_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (Factorial.Basic.factorial_pos column)).ne'
      (Fraction.Cast.Order.natCast_pos_direct
        (Factorial.Basic.factorial_pos (row - column))).ne'
  have rightNonzero : (Factorial.Basic.factorial row : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (Factorial.Basic.factorial_pos row)).ne'
  apply Fraction.Field.div_eq_div_of_cross 1 _ (Choose.Pascal.choose row column :
    Fraction.Rational) _
    leftNonzero rightNonzero
  have castIdentity := congrArg (fun value : Nat => (value : Fraction.Rational))
    (Choose.Factorial.choose_mul_factorials row column order)
  simp only [Purelib.Algebra.NatCast.mul] at castIdentity
  calc
    (1 : Fraction.Rational) * (Factorial.Basic.factorial row : Fraction.Rational) =
        (Factorial.Basic.factorial row : Fraction.Rational) :=
      Fraction.Field.one_mul _
    _ = (Choose.Pascal.choose row column : Fraction.Rational) *
          (Factorial.Basic.factorial column : Fraction.Rational) *
            (Factorial.Basic.factorial (row - column) : Fraction.Rational) := castIdentity.symm
    _ = (Choose.Pascal.choose row column : Fraction.Rational) *
          ((Factorial.Basic.factorial column : Fraction.Rational) *
            (Factorial.Basic.factorial (row - column) : Fraction.Rational)) := by ring1
end Purelib.Data.Rat.Factorial

end
