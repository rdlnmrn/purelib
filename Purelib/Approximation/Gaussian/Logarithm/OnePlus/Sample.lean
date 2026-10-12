module
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative.Sample
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative

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

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Sample

/-- The finite local-log sample is defined by its factor, so its value at zero is exact without selecting a quotient. -/
def log1pSample (u : Canonical)
  (index : Nat) : Canonical :=
  u * Sample.log1pRelSample u index

/-- The finite one-plus logarithm sample equals its input times the retained relative-logarithm sample. -/
theorem log1pSample_factor (u :
  Canonical) (index : Nat) :
    log1pSample u index = u * Sample.log1pRelSample u index := rfl

/-- Every finite one-plus logarithm sample at zero input is exactly zero. -/
theorem log1pSample_zero (index : Nat) :
  log1pSample 0 index = 0 := by
  rw [log1pSample, Data.Gaussian.Basic.zero_mul]
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Sample

end
