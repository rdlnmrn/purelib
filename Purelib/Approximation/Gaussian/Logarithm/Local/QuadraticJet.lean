module
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Sample
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Factorization
public import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Data.Gaussian.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.OnePlus

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative

open Purelib.Calculus.Jet

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

/-- Primitive certificate for the finite local logarithm at its rational origin. -/
def logarithm1p {increment : Data.Gaussian.Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq increment ≤ 1 / 4) (index : Nat) :
    Quadratic.Basic.Certificate increment :=
  { base := 0
    slope := 1
    output := Sample.log1pSample
      increment (index + 1)
    remainder := Sample.log1pSample
      increment (index + 1) - increment
    expansion := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im, Purelib.Data.Gaussian.Basic.zero_re,
          Purelib.Data.Gaussian.Basic.zero_im,
          Purelib.Data.Gaussian.Basic.one_re, Purelib.Data.Gaussian.Basic.one_im] <;> ring1
    factor := 4
    factor_nonneg := by decide
    remainder_le := by
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        Factorization.log1pSample_second_order_normSq_le
          disk index }

end Certificate

end Purelib.Calculus.Jet.Quadratic.Basic

end
