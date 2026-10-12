module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Sequence.Name

namespace Purelib.Approximation.Gaussian.Sequence.Name.Equivalence

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

/-- Lift an approximation equivalence through both ordinary productive CCL controllers. -/
@[expose] def approximationEquivalent_toNamed {left right : ApproximationData}
    (equivalent : Gaussian.Equivalence.Equivalent left right) :
    Gaussian.Equivalence.NamedEquivalent left.toNamed right.toNamed :=
  Equivalent.toNamed equivalent

/-- Every CCL name is operationally equivalent to the productive wrapper of its own canonical finite sampler. -/
@[expose] def named_toSamplingNamed (name : Gaussian.Name.Basic.Named) :
    Gaussian.Equivalence.NamedEquivalent name
      (Sampling.approximation name).toNamed :=
  Equivalent.symm
    (Equivalent.toNamed_sampling
      (Sampling.approximation name))

end

end Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
