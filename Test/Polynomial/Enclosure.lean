module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Interval.Arithmetic
public import Purelib.Data.Rat.Interval.Gap
public import Purelib.Polynomial.Dense.Rational.Enclosure.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat

open Purelib.Data.Rat.Interval

open Purelib.Polynomial.Dense.Rational

section
@[expose] public section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

namespace Test.Polynomial.Enclosure

/-- Constants, negative scales, sign-changing multiplication, and a positive cubic enclosure are all checked by the
kernel on the executable constructors. -/
theorem exact_enclosure_regressions :
    (Enclosure.Basic.evaluate ⟨[1]⟩ ⟨-2, 3, by decide⟩).lower = 1 ∧
      (Enclosure.Basic.evaluate ⟨[1]⟩ ⟨-2, 3, by decide⟩).upper = 1 ∧
      (Interval.Arithmetic.scale (-2) ⟨1, 3, by decide⟩).lower = -6 ∧
      (Interval.Arithmetic.scale (-2) ⟨1, 3, by decide⟩).upper = -2 ∧
      (Interval.Arithmetic.mul ⟨-2, 3, by decide⟩ ⟨-4, 5, by decide⟩).lower = -12 ∧
      (Interval.Arithmetic.mul ⟨-2, 3, by decide⟩ ⟨-4, 5, by decide⟩).upper = 15 ∧
      (Enclosure.Basic.evaluate ⟨[1/16384, 3/1024, 3/64, 1/2]⟩ ⟨0, 1, by decide⟩).lower = 1/2 ∧
      (Enclosure.Basic.evaluate ⟨[1/16384, 3/1024, 3/64, 1/2]⟩ ⟨0, 1, by decide⟩).upper = 9009/16384 := by
  rw [show (16384 : Fraction.Rational) = Fraction.Cast.fromInt 16384 from
    Fraction.Cast.natCast_eq_fromInt 16384,
    show (9009 : Fraction.Rational) = Fraction.Cast.fromInt 9009 from
      Fraction.Cast.natCast_eq_fromInt 9009,
    show (1024 : Fraction.Rational) = Fraction.Cast.fromInt 1024 from
      Fraction.Cast.natCast_eq_fromInt 1024]
  decide +kernel

/-- Interval dependency can still give an inconclusive proposal for `(-2+4t)^2+1`, despite this polynomial being
positive at every rational `t`. -/
theorem dependent_enclosure_has_zero_gap :
    Gap.gap (Enclosure.Basic.evaluate ⟨[16, -16, 5]⟩ ⟨0, 1, by decide⟩) = 0 := by
  decide +kernel

end Test.Polynomial.Enclosure

end
