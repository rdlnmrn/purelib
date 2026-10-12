module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

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

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- An exact first-order expansion with a quadratic quadrance bound at one increment.

The certificate retains Gaussian rational base, slope, output and remainder values. Its nonnegative rational factor
bounds the remainder quadrance by the square of the increment quadrance; the record describes this one displayed
increment. -/
structure Certificate (increment : Basic.Canonical) where
  /-- The displayed base value of the expansion. -/ base : Basic.Canonical
  /-- The displayed first-order Gaussian rational coefficient. -/ slope : Basic.Canonical
  /-- The displayed output value at the indexed increment. -/ output : Basic.Canonical
  /-- The exact residual after subtracting the base and first-order contribution. -/ remainder : Basic.Canonical
  /-- The retained values satisfy the exact first-order residual identity. -/ expansion : output - base - increment *
    slope = remainder
  /-- The rational factor in the quadratic quadrance bound. -/ factor : Fraction.Rational
  /-- The retained rational remainder factor is nonnegative. -/ factor_nonneg : 0 ≤ factor
  /-- The remainder quadrance is bounded by the factor times squared increment quadrance. -/ remainder_le :
    Basic.Canonical.normSq remainder ≤ factor * Basic.Canonical.normSq increment ^ 2

constructive_injectivity Certificate

namespace Certificate

open Purelib.Calculus.Jet.Quadratic.Basic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A zero increment forces the retained remainder to vanish.

The quadratic bound makes its quadrance at most zero, and positivity of Gaussian quadrance identifies the remainder with
zero. -/
theorem remainder_zero_of_increment_zero {increment : Basic.Canonical}
    (certificate : Certificate increment) (zero : increment = 0) :
    certificate.remainder = 0 := by
  subst increment
  have bound := certificate.remainder_le
  rw [Basic.Canonical.normSq_zero, zero_pow (by decide : (2 : Nat) ≠ 0),
    Fraction.Field.mul_zero_direct] at bound
  exact (Basic.Canonical.normSq_eq_zero certificate.remainder).mp
    (le_antisymm bound (Basic.Canonical.normSq_nonneg certificate.remainder))

open Purelib.Calculus.Jet.Quadratic.Basic in
open Purelib.Data.Gaussian in
/-- At a zero increment, the output equals the base.

The vanishing remainder and the exact expansion identity eliminate both terms in their difference. -/
theorem output_eq_base_of_increment_zero {increment : Basic.Canonical}
    (certificate : Certificate increment) (zero : increment = 0) :
    certificate.output = certificate.base := by
  subst increment
  have expansion := certificate.expansion
  have remainderZero := certificate.remainder_zero_of_increment_zero rfl
  rw [remainderZero] at expansion
  have difference : certificate.output - certificate.base = 0 := by
    calc
      certificate.output - certificate.base = certificate.output - certificate.base - 0 * certificate.slope := by ring1
      _ = 0 := expansion
  exact Purelib.Data.Gaussian.Basic.gaussian_eq_of_sub_eq_zero difference
end Certificate

end Purelib.Calculus.Jet.Quadratic.Basic

end
