module
public import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Compositional quadratic-remainder certificates

A certificate is a finite tuple of displayed Gaussian rationals.  It records
an exact first-order expansion at one displayed increment and a rational
quadrance bound for its remainder.  Addition, negation, scalar multiplication,
and composition compute new factors from old ones.  Thus a composite
calculation retains an executable remainder budget instead of appealing to
limits, infinitesimals, or an unspecified big-O relation.
-/

namespace Purelib.Calculus.Jet.Quadratic.Basic
namespace Certificate

open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Compute twice the sum of slope quadrance and remainder factor.

This nonnegative rational quantity bounds output-displacement quadrance relative to increment quadrance on the unit
increment disk. -/
def sensitivity {increment : Basic.Canonical}
    (certificate : Certificate increment) : Fraction.Rational :=
  2 * (Basic.Canonical.normSq certificate.slope + certificate.factor)

/-- The displayed sensitivity is nonnegative for every quadratic certificate. -/
theorem sensitivity_nonneg {increment : Basic.Canonical}
    (certificate : Certificate increment) :
    0 ≤ certificate.sensitivity :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Basic.Canonical.normSq_nonneg certificate.slope)
      certificate.factor_nonneg)

/-- Bound output-displacement quadrance on the unit increment disk.

When increment quadrance is at most one, the displacement quadrance is at most sensitivity times increment quadrance.
The estimate uses the exact expansion and retained quadratic remainder bound. -/
theorem movement_le {increment : Basic.Canonical}
    (certificate : Certificate increment)
    (unit : Basic.Canonical.normSq increment ≤ 1) :
    Basic.Canonical.normSq (certificate.output - certificate.base) ≤
      certificate.sensitivity * Basic.Canonical.normSq increment := by
  have identity : certificate.output - certificate.base =
      increment * certificate.slope + certificate.remainder := by
    calc
      certificate.output - certificate.base =
          (certificate.output - certificate.base - increment * certificate.slope) +
            increment * certificate.slope := (sub_add_cancel _ _).symm
      _ = certificate.remainder + increment * certificate.slope :=
        congrArg (fun value => value + increment * certificate.slope) certificate.expansion
      _ = increment * certificate.slope + certificate.remainder :=
        Basic.Canonical.add_comm _ _
  have squareLe : Basic.Canonical.normSq increment ^ 2 ≤ Basic.Canonical.normSq increment := by
    calc
      Basic.Canonical.normSq increment ^ 2 = Basic.Canonical.normSq increment * Basic.Canonical.normSq increment :=
        pow_two _
      _ ≤ Basic.Canonical.normSq increment * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct unit
          (Basic.Canonical.normSq_nonneg increment)
      _ = Basic.Canonical.normSq increment := Fraction.Field.mul_one_direct _
  rw [identity]
  calc
    Basic.Canonical.normSq (increment * certificate.slope + certificate.remainder) ≤
        2 * (Basic.Canonical.normSq (increment * certificate.slope) +
          Basic.Canonical.normSq certificate.remainder) := by
          simpa only [Norm.Basic.normSq_eq_canonical] using
            Norm.Bounds.normSq_add_le_two
              (increment * certificate.slope) certificate.remainder
    _ ≤ 2 *
        (Basic.Canonical.normSq increment * Basic.Canonical.normSq certificate.slope +
          certificate.factor * Basic.Canonical.normSq increment ^ 2) := by
      rw [Basic.Canonical.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl certificate.remainder_le) (by decide)
    _ ≤ 2 *
        (Basic.Canonical.normSq increment * Basic.Canonical.normSq certificate.slope +
          certificate.factor * Basic.Canonical.normSq increment) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
        (by decide)
      exact add_le_add le_rfl
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          squareLe certificate.factor_nonneg)
    _ = certificate.sensitivity * Basic.Canonical.normSq increment := by
      unfold sensitivity
      ring1
end Certificate

end Purelib.Calculus.Jet.Quadratic.Basic

end
