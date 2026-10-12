module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Approximation.Gaussian.Sequence.Constant
public import Purelib.Approximation.Gaussian.Sequence.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name

namespace Purelib.Approximation.Gaussian.Sequence.Name.Exact

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Name

section
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

open Purelib.Approximation

/-- The exact-name process and the constant finite approximation for the same displayed rational are operationally
equal. -/
@[expose] def exact_toConstantNamed (value : Data.Gaussian.Basic.Canonical) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.exact value)
      (Constant.constantApproximation value).toNamed :=
  NamedEquivalent.trans
    (Equivalence.named_toSamplingNamed
      (Named.exact value))
    (Equivalence.approximationEquivalent_toNamed
      (Equivalence.approximationEquivalentOfSamplesEq
        (Sampling.approximation
          (Named.exact value))
        (Constant.constantApproximation value)
        (by intro index; rfl)))

end

public section

/-!
# Operational branch certificates for the complex logarithm

The geometric `Chart` data proves that its finite local recurrence is safe
and productive.  It intentionally permits any additive correction name.
This module records the additional semantic obligation needed to call that
correction a logarithm branch: exponentiating it must reproduce the inverse
of the chart's displayed scale, in finite operational equality.

Once the local inverse law and the exponential addition law are established,
this certificate is the missing branch datum in the calculation

`Exp(localLog(factor * input) + correction) = input`.

The exponentiation, equality, and inverse factor below are all CCL programs
or displayed Gaussian rationals.  No completed complex number or global
single-valued logarithm is introduced.
-/

open Purelib.Approximation

/-- Every canonical sample of an exact Gaussian name equals the displayed Gaussian value. -/
theorem exactNamedSample (input : Data.Gaussian.Basic.Canonical) (index : Nat) :
    (Sampling.approximation
      (Named.exact input)).sample index =
        input := rfl

/-- The constant exact-input approximation is operationally equivalent to the canonical sampler of the exact name. -/
@[expose] def exactInput_to_exactNamed_equivalent (input : Data.Gaussian.Basic.Canonical) :
    Gaussian.Equivalence.Equivalent (Constant.exactInputApproximation input)
      (Sampling.approximation
        (Named.exact input)) :=
  Equivalent.of_constant_samples
    (Constant.exactInputApproximation input)
    (Sampling.approximation
      (Named.exact input))
    input (fun _ => rfl) (Approximation.Gaussian.Sequence.Name.Exact.exactNamedSample input)

end

end

end Purelib.Approximation.Gaussian.Sequence.Name.Exact
