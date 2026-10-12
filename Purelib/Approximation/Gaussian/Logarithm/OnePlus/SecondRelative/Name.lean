module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Sequence

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative

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

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Name

/-- Turn the finite second-relative logarithm approximation on the quarter-quadrance disk into a productive Gaussian
process name. -/
def log1pSecondRelNamed (u :
  Data.Gaussian.Basic.Canonical)
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) : Gaussian.Name.Basic.Named :=
  (Sequence.log1pSecondRelApproximation u disk).toNamed
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Name

end
