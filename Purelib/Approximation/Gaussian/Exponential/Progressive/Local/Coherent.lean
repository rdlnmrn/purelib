module
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Sequence.Coherence

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Exponential.Progressive.Local

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

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Coherent

/-- The local unit-disk exponential output is coherent because its process is generated from the explicit finite Horner
approximation. -/
def localExpCoherent (input :
  Gaussian.Name.Basic.Named)
    (domain : Approximation.Gaussian.Name.UnitDisk input) :
    Gaussian.Process.Coherence.Basic.Coherent (Name.named input domain).process :=
  Gaussian.Process.Coherence.Basic.Coherent.ofApproximation
    (Name.approximation input domain)
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Coherent

end
