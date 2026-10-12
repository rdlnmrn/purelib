module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Exact

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Basic

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

/-- Actual CCL multiplication of two exact displayed rational names is operationally the exact displayed product. -/
@[expose] def exactMul_named_equivalent (left right : Data.Gaussian.Basic.Canonical) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Named.exact left)
        (Named.exact right))
      (Named.exact (left * right)) :=
  Equivalent.of_constant_samples
    _ _ (left * right) (by intro index; rfl) (by intro index; rfl)

end

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Exact
