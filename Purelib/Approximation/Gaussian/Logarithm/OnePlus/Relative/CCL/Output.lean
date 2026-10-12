module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence.CCL.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative.Name
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative.Sequence
import Purelib.Data.CCL.Transducer.Machine.Advance

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative

open Purelib.Data.CCL.Transducer.Machine

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

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative.CCL.Output

/-- The relative logarithm name on the retained quarter disk emits exactly the requested finite bit count and preserves
its initial prefix. -/
theorem log1pRelNamed_productive (u :
  Data.Gaussian.Basic.Canonical) (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4)
    (count : Nat) :
    (Name.log1pRelNamed u disk).machine.emitted.IsPrefix
        (Advance.advance
          (Name.log1pRelNamed u disk).machine count).emitted ∧
      (Advance.advance
          (Name.log1pRelNamed u disk).machine count).emitted.length = count :=
  (Sequence.log1pRelApproximation u disk).output_productive count
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative.CCL.Output

end
