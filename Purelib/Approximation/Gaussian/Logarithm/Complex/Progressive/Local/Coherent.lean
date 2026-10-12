module
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Sequence.Coherence

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

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

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Coherent

/-- The local complex logarithm output of a supplied disk chart is coherent. -/
def localComplexLogCoherent (input :
  Gaussian.Name.Basic.Named)
    (disk : Domain.Disk input) :
    Gaussian.Process.Coherence.Basic.Coherent
      (Name.named input disk).process :=
  Gaussian.Process.Coherence.Basic.Coherent.ofApproximation
    (Name.approximation input disk)
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Coherent

end
