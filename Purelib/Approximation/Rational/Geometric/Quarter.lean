module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Rational.Geometric.Quarter

/-- Split the quarter-power at an earlier successor stage. -/
public theorem quarterPower_shift (earlier index : Nat) :
    (1 / 4 : Fraction.Rational) ^ (earlier + 1 + index) =
      (1 / 4 : Fraction.Rational) ^ (earlier + 1) *
        (1 / 4 : Fraction.Rational) ^ index := by
  rw [pow_add]

/-- Multiplication by four removes one quarter-power step. -/
public theorem four_mul_quarterPower_succ (index : Nat) :
    4 * (1 / 4 : Fraction.Rational) ^ (index + 1) =
      (1 / 4 : Fraction.Rational) ^ index := by
  rw [pow_succ]
  calc
    4 * ((1 / 4 : Fraction.Rational) ^ index * (1 / 4)) =
        (1 / 4 : Fraction.Rational) ^ index * (4 * (1 / 4)) := by ring1
    _ = (1 / 4 : Fraction.Rational) ^ index * 1 := by
      rw [show (4 : Fraction.Rational) * (1 / 4) = 1 by decide]
    _ = (1 / 4 : Fraction.Rational) ^ index :=
      Fraction.Field.mul_one_direct _

end Purelib.Approximation.Rational.Geometric.Quarter

end
