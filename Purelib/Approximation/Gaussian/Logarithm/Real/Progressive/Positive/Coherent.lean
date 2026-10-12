module
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.PositiveReal.Basic
import Purelib.Approximation.Gaussian.Name.PositiveReal.Preparation
import Purelib.Approximation.Gaussian.Process.Coherence.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.PositiveReal

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

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive.Coherent

/-- The automatically charted global positive-real logarithm output is coherent. -/
def positiveLogNamedCoherent (input :
  Gaussian.Name.Basic.Named)
    (positive : Approximation.Gaussian.Name.PositiveReal input) :
    Gaussian.Process.Coherence.Basic.Coherent
      (Name.named input positive).process :=
  Coherent.logRangeNamedCoherent
    (Preparation.refinedInput positive)
    (Name.automaticChart positive)

/-- Package the automatically charted positive-real logarithm output with its finite coherence certificate. -/
def positiveLog (input :
  Gaussian.Name.Basic.Named)
    (positive : Approximation.Gaussian.Name.PositiveReal input) :
    Coherent.CoherentNamed :=
  { name := Name.named input positive
    coherent := positiveLogNamedCoherent input
      positive }
end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive.Coherent

end
