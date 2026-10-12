module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Sequence
public import Purelib.Approximation.Gaussian.Exponential.Horner.Differential
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Calculus.Jet.Quadratic.Basic
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

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Horner.Addition

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

/-- Primitive certificate for the finite translated exponential program. -/
def exponential {base increment : Data.Gaussian.Basic.Canonical}
    (baseUnit : Data.Gaussian.Norm.Basic.normSq base ≤ 1) (incrementUnit :
      Data.Gaussian.Norm.Basic.normSq increment ≤ 1)
    (index : Nat) : Quadratic.Basic.Certificate increment :=
  { base := Sample.sample base (index + 1)
    slope := Sample.sample base (index + 1)
    output := Sequence.expProductSample
      base increment (index + 1)
    remainder :=
      Sequence.expProductSample
          base increment (index + 1) -
        Sample.sample base (index + 1) -
        increment * Sample.sample base (index + 1)
    expansion := rfl
    factor := 10
    factor_nonneg := by decide
    remainder_le := by
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        (Differential.expProductSample_second_order_normSq_le
          baseUnit incrementUnit index) }
end Certificate

end Purelib.Calculus.Jet.Quadratic.Basic

end
