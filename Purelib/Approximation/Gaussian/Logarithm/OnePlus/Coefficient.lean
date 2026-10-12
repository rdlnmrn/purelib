module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Alternating
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

open Purelib

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

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Coefficient

/-- The signed reciprocal coefficient at the successor degree.

The finite index chooses an alternating sign and the positive natural denominator `index + 1`. -/
def alternatingCoefficient (index : Nat) :
  Fraction.Rational :=
  Alternating.alternatingSign index / ((index + 1 : Nat) : Fraction.Rational)

/-- Multiplication by the coefficient's successor degree recovers its alternating sign. -/
theorem degree_mul_alternatingCoefficient (index :
  Nat) :
    (((index + 1 : Nat) : Fraction.Rational) *
      alternatingCoefficient index) =
      Alternating.alternatingSign index := by
  have denominatorPositive :
      0 < ((index + 1 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (by omega)
  rw [alternatingCoefficient]
  calc
    ((index + 1 : Nat) : Fraction.Rational) *
          (Alternating.alternatingSign index / ((index + 1 : Nat) : Fraction.Rational)) =
        (Alternating.alternatingSign index / ((index + 1 : Nat) : Fraction.Rational)) *
          ((index + 1 : Nat) : Fraction.Rational) :=
      Fraction.Field.mul_comm _ _
    _ = Alternating.alternatingSign index :=
      Fraction.Field.div_mul_cancel_of_ne _ _
        denominatorPositive.ne'
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Coefficient

end
