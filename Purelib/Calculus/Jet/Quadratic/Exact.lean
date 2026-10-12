module
import Purelib.Data.Gaussian.Basic
public import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

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

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute the exact ratio of remainder quadrance to squared increment quadrance.

The zero-increment branch returns zero. At a nonzero increment, Gaussian quadrance is positive, so the denominator in
the displayed rational ratio is nonzero. -/
def exactFactor (increment remainder : Basic.Canonical) :
  Fraction.Rational :=
  if increment = 0 then 0
  else Basic.Canonical.normSq remainder / Basic.Canonical.normSq increment ^ 2

section
open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- The exact remainder ratio is nonnegative in both increment branches. -/
theorem exactFactor_nonneg (increment remainder :
  Basic.Canonical) :
    0 ≤ exactFactor increment remainder := by
  unfold exactFactor
  split
  · exact le_rfl
  · exact Fraction.Order.Field.div_nonneg_direct
      (Basic.Canonical.normSq_nonneg remainder)
      (Fraction.Order.Arithmetic.pow_nonneg_direct
        (Basic.Canonical.normSq_nonneg increment) 2)

/-- The exact ratio bounds the remainder when zero increments have zero remainder.

For nonzero increments, cancellation gives equality. The supplied implication handles the zero-increment branch. -/
theorem exactFactor_bound (increment remainder :
  Basic.Canonical)
    (zeroRemainder : increment = 0 → remainder = 0) :
    Basic.Canonical.normSq remainder ≤ exactFactor increment remainder *
      Basic.Canonical.normSq increment ^ 2 := by
  by_cases zero : increment = 0
  · rw [zeroRemainder zero, Basic.Canonical.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (exactFactor_nonneg increment 0)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Basic.Canonical.normSq_nonneg increment) 2)
  · rw [exactFactor, if_neg zero]
    have normPositive : 0 < Basic.Canonical.normSq increment := by
      simpa only [Norm.Basic.normSq_eq_canonical] using
        Norm.Basic.normSq_pos zero
    have denominatorPositive : 0 < Basic.Canonical.normSq increment ^ 2 :=
      Fraction.Order.Arithmetic.pow_pos_direct normPositive 2
    calc
      Basic.Canonical.normSq remainder ≤ Basic.Canonical.normSq remainder := le_rfl
      _ = Basic.Canonical.normSq remainder / Basic.Canonical.normSq increment ^ 2 *
          Basic.Canonical.normSq increment ^ 2 :=
        (Fraction.Field.div_mul_cancel_of_ne
          (Basic.Canonical.normSq remainder) (Basic.Canonical.normSq increment ^ 2)
            denominatorPositive.ne').symm

end

open Purelib.Calculus.Jet.Quadratic.Basic in
open Purelib.Data.Gaussian in
/-- Construct a quadratic certificate from an exact expansion and its zero-increment law.

All displayed values are retained. The constructor computes their exact remainder ratio, returning zero as the factor at
zero increment, and supplies its nonnegativity and quadrance bound. -/
def ofExpansion (increment base slope output remainder :
  Basic.Canonical)
    (expansion : output - base - increment * slope = remainder)
    (zeroRemainder : increment = 0 → remainder = 0) :
    Certificate increment :=
  { base := base
    slope := slope
    output := output
    remainder := remainder
    expansion := expansion
    factor := exactFactor increment remainder
    factor_nonneg := exactFactor_nonneg increment remainder
    remainder_le := exactFactor_bound increment remainder zeroRemainder }
end Certificate

end Purelib.Calculus.Jet.Quadratic.Basic

end
