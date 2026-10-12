module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Scale

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Algebra.FiniteSum

open Purelib.Data.Gaussian

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

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative.Sample

/-- The displayed relative-logarithm term: the indexed power of the negated input divided by the successor index. -/
def log1pRelTerm (u :
  Canonical) (index : Nat) : Canonical :=
  Scale.scale
    (1 / ((index + 1 : Nat) : Fraction.Rational)) ((-u) ^ index)

/-- Sum the relative-logarithm terms through the displayed finite index.

The finite sample is defined directly at zero input as well as at nonzero Gaussian rationals. -/
def log1pRelSample (u :
  Canonical) (index : Nat) : Canonical :=
  Prefix.sum
    (log1pRelTerm u) (index + 1)

/-- The index-zero relative-logarithm term is one for every input. -/
@[simp] theorem log1pRelTerm_zero (u :
  Canonical) :
    log1pRelTerm u 0 = 1 := by
  rw [log1pRelTerm, pow_zero]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Scale.scale_re,
      Scale.scale_im, Basic.one_re, Basic.one_im] <;>
    rw [show (1 / ((0 + 1 : Nat) : Fraction.Rational)) = 1 by decide] <;> ring1
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative.Sample

end
