module
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Sequence.Coherence

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local

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

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Coherent

/-- The local positive-real logarithm output is coherent by its explicit finite approximation. -/
def localLogCoherent (input :
  Gaussian.Name.Basic.Named)
    (chart : Domain.Chart input) :
    Gaussian.Process.Coherence.Basic.Coherent (Name.named input chart).process :=
  Gaussian.Process.Coherence.Basic.Coherent.ofApproximation
    (Name.approximation input chart)
end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Coherent

end
