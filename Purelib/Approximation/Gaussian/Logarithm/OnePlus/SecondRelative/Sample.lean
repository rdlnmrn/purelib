module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Data.Gaussian.Scale

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic

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

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Sample

/-! ## The second relative logarithm -/

/-- The displayed second-relative logarithm term: minus the indexed power of the negated input divided by index plus
two. -/
def log1pSecondRelTerm (u :
  Canonical) (index : Nat) : Canonical :=
  Scale.scale
    (-(1 / ((index + 2 : Nat) : Fraction.Rational))) ((-u) ^ index)

/-- Sum the second-relative logarithm terms through the displayed finite index.

Every term is finite Gaussian rational arithmetic, including at zero input. -/
def log1pSecondRelSample (u :
  Canonical) (index : Nat) : Canonical :=
  Prefix.sum
    (log1pSecondRelTerm u) (index + 1)
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Sample

end
