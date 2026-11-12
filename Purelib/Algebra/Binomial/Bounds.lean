module

public import Purelib.Algebra.Binomial
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Nonnegative terms of the original finite binomial expansion

The same original prefix sum contains every nonnegative term. Its exact
finite binomial identity bounds one term without an infinite series.
-/

public section

namespace Purelib.Algebra.Binomial

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Algebra.FiniteSum
open Purelib.Data.Nat.Choose

/-- Each original nonnegative binomial term is at most the full finite power. -/
theorem term_le {first second : Rational} (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (row column : Nat) (within : column ≤ row) :
    (Pascal.choose row column : Rational) * first ^ (row - column) * second ^ column ≤ (first + second) ^ row := by
  have nonnegative (index : Nat) :
      0 ≤ second ^ index * first ^ (row - index) * (row.choose index : Rational) :=
    Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct (Order.Arithmetic.pow_nonneg_direct secondNonnegative index)
        (Order.Arithmetic.pow_nonneg_direct firstNonnegative (row - index)))
      (Cast.Order.natCast_le_direct (Nat.zero_le _))
  have bounded := Prefix.term_le_prefixSum (row + 1)
    (fun index => second ^ index * first ^ (row - index) * (row.choose index : Rational))
    nonnegative column (Nat.lt_succ_of_le within)
  have term : (Pascal.choose row column : Rational) * first ^ (row - column) * second ^ column =
      second ^ column * first ^ (row - column) * (row.choose column : Rational) := by
    rewrite [Pascal.eq_choose]
    ring1
  exact term.trans_le (bounded.trans_eq (binomial_theorem row first second).symm)

end Purelib.Algebra.Binomial

end
