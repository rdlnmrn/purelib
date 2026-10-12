module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Sequence.Name
public import Purelib.Approximation.Gaussian.Logarithm.Rational.Sequence

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Rational.Name

/-- Package the finite rational logarithm approximation as its original sequence-backed name.

The input lies between one half and two; the name starts at the approximation's index-zero state. -/
def named (x : Fraction.Rational) (halfLe : 1 / 2 ≤ x)
  (leTwo : x ≤ 2) : Gaussian.Name.Basic.Named :=
  (Sequence.approximation x halfLe leTwo).toNamed
end Purelib.Approximation.Gaussian.Logarithm.Rational.Name

end
