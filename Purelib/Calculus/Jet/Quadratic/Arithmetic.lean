module
import Purelib.Calculus.Jet.Quadratic.Basic
public import Purelib.Calculus.Jet.Quadratic.Exact
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs
public import Purelib.Data.Gaussian.Field

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

section
open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Data.Gaussian
section
open Purelib.Data.Rat
/-- Certify an exact affine expansion with zero remainder and zero factor. -/
def affine (increment base slope : Basic.Canonical) :
  Certificate increment :=
  { base := base
    slope := slope
    output := base + increment * slope
    remainder := 0
    expansion := by
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im,
          Basic.zero_re, Basic.zero_im] <;> ring1
    factor := 0
    factor_nonneg := le_rfl
    remainder_le := by
      rw [Basic.Canonical.normSq_zero, Fraction.Field.zero_mul_direct] }

/-- Add two quadratic certificates at the same increment.

The displayed base, slope, output and remainder are added componentwise. Twice the sum of the original factors bounds
the quadrance of the summed remainder. -/
def add {increment : Basic.Canonical}
    (left right : Certificate increment) : Certificate increment :=
  { base := left.base + right.base
    slope := left.slope + right.slope
    output := left.output + right.output
    remainder := left.remainder + right.remainder
    expansion := by
      rw [← left.expansion, ← right.expansion]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
    factor := 2 * (left.factor + right.factor)
    factor_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg left.factor_nonneg right.factor_nonneg)
    remainder_le := by
      calc
        Basic.Canonical.normSq (left.remainder + right.remainder) ≤
            2 * (Basic.Canonical.normSq left.remainder + Basic.Canonical.normSq right.remainder) :=
          by simpa only [Norm.Basic.normSq_eq_canonical] using
            Norm.Bounds.normSq_add_le_two left.remainder right.remainder
        _ ≤ 2 *
            (left.factor * Basic.Canonical.normSq increment ^ 2 +
              right.factor * Basic.Canonical.normSq increment ^ 2) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add left.remainder_le right.remainder_le) (by decide)
        _ = 2 * (left.factor + right.factor) * Basic.Canonical.normSq increment ^ 2 := by
          ring1 }

end

/-- Negate the expansion while retaining its original nonnegative remainder factor. -/
def neg {increment : Basic.Canonical}
    (certificate : Certificate increment) : Certificate increment :=
  { base := -certificate.base
    slope := -certificate.slope
    output := -certificate.output
    remainder := -certificate.remainder
    expansion := by
      rw [← certificate.expansion]
      apply Basic.ext <;>
        simp only [Basic.neg_re, Basic.neg_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
    factor := certificate.factor
    factor_nonneg := certificate.factor_nonneg
    remainder_le := by
      rw [Basic.Canonical.normSq_neg]
      exact certificate.remainder_le }

/-- Multiply two expansions using the displayed product rule for their slopes.

The constructor computes the actual product remainder and its exact rational factor. The input certificates ensure that
this remainder vanishes at zero increment. -/
def mul {increment : Basic.Canonical}
    (left right : Certificate increment) : Certificate increment := by
  let base := left.base * right.base
  let slope := left.slope * right.base + left.base * right.slope
  let output := left.output * right.output
  let remainder := output - base - increment * slope
  apply Certificate.ofExpansion increment base slope output remainder rfl
  intro zero
  subst increment
  have leftAtBase := left.output_eq_base_of_increment_zero rfl
  have rightAtBase := right.output_eq_base_of_increment_zero rfl
  dsimp only [remainder, output, base, slope]
  rw [leftAtBase, rightAtBase]
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im,
      Basic.zero_re, Basic.zero_im] <;> ring1

/-- Construct the reciprocal expansion with inverse base and output values.

The slope is minus the original slope times the squared inverse base. The interface requires nonzero base and output
evidence; the remainder factor is computed from the exact displayed residual. -/
def reciprocal {increment : Basic.Canonical}
    (certificate : Certificate increment)
    (_baseNonzero : certificate.base ≠ 0)
    (_outputNonzero : certificate.output ≠ 0) : Certificate increment := by
  let base := certificate.base⁻¹
  let slope := -(certificate.slope *
    (certificate.base⁻¹ * certificate.base⁻¹))
  let output := certificate.output⁻¹
  let remainder := output - base - increment * slope
  apply Certificate.ofExpansion increment base slope output remainder rfl
  intro zero
  subst increment
  have atBase := certificate.output_eq_base_of_increment_zero rfl
  dsimp only [remainder, output, base, slope]
  rw [atBase]
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.neg_re, Basic.neg_im,
      Basic.zero_re, Basic.zero_im] <;> ring1

/-- Divide two expansions by multiplying the numerator with the denominator's reciprocal.

The denominator must have nonzero displayed base and output. Both stages retain the shared increment and compute their
exact residual factors. -/
def div {increment : Basic.Canonical}
    (numerator denominator : Certificate increment)
    (baseNonzero : denominator.base ≠ 0)
    (outputNonzero : denominator.output ≠ 0) : Certificate increment :=
  numerator.mul (denominator.reciprocal baseNonzero outputNonzero)

open Purelib.Data.Rat in
/-- Multiply a displayed expansion by one Gaussian rational scalar.

The scalar multiplies every Gaussian field. Its quadrance multiplies the original remainder factor, using
multiplicativity of Gaussian quadrance. -/
def scale (scalar : Basic.Canonical) {increment :
  Basic.Canonical}
    (certificate : Certificate increment) : Certificate increment :=
  { base := scalar * certificate.base
    slope := scalar * certificate.slope
    output := scalar * certificate.output
    remainder := scalar * certificate.remainder
    expansion := by
      rw [← certificate.expansion]
      apply Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
    factor := Basic.Canonical.normSq scalar * certificate.factor
    factor_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (Basic.Canonical.normSq_nonneg scalar)
        certificate.factor_nonneg
    remainder_le := by
      rw [Basic.Canonical.normSq_mul]
      calc
        Basic.Canonical.normSq scalar * Basic.Canonical.normSq certificate.remainder ≤
            Basic.Canonical.normSq scalar *
              (certificate.factor * Basic.Canonical.normSq increment ^ 2) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            certificate.remainder_le (Basic.Canonical.normSq_nonneg scalar)
        _ = (Basic.Canonical.normSq scalar * certificate.factor) *
            Basic.Canonical.normSq increment ^ 2 := by ring1 }
end

end Certificate

end Purelib.Calculus.Jet.Quadratic.Basic

end
