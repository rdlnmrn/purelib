module
import Purelib.Data.Gaussian.Basic
public import Purelib.Algebra.FiniteSum.Prefix

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs

open Purelib

open Purelib.Algebra.FiniteSum

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

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sample

/-! ## The derivative and its reciprocal law -/

/-- Compute the finite geometric derivative sample for the one-plus logarithm.

The result sums the first `index + 1` powers of the negated Gaussian rational input; it does not construct an infinite
series. -/
def log1pDerivativeSample (u :
  Data.Gaussian.Basic.Canonical) (index : Nat) : Data.Gaussian.Basic.Canonical :=
  Prefix.sum
    (fun termIndex => (-u) ^ termIndex) (index + 1)
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sample

end
