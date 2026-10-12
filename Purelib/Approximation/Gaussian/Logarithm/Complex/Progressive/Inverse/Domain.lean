module
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.UnitDisk

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Approximation.Gaussian.Logarithm.Local.Horner

open Purelib.Approximation.Gaussian.Name

section
@[expose] public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Domain

/-- The sharper finite Horner estimate places every explicitly possible local complex-log reading in the local
exponential unit disk. -/
theorem localComplexLogUnitDisk
  (input : Gaussian.Name.Basic.Named)
    (disk : Domain.Disk input) :
    Approximation.Gaussian.Name.UnitDisk
      (Name.named input disk) where
  possible_unit := by
    intro value possible
    change (Name.approximation
      input disk).Possible 0 value at possible
    rcases possible with ⟨later, _order, rfl⟩
    exact Sample.sample_bounded_one
      (Sampling.inputSample_bound disk later)
      later
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Domain

end
