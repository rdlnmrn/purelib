module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Name

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence

open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
open Purelib.Approximation.Gaussian.Sequence.Name

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

/-- Stateful multiplication respects operational equality independently in both coherent operands. -/
@[expose] def coherentMul_respects
    (leftOne leftTwo rightOne rightTwo : Coherent.CoherentNamed)
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent rightOne.name rightTwo.name) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        leftOne.name rightOne.name)
      (Named.mul
        leftTwo.name rightTwo.name) :=
  NamedEquivalent.trans
    (Bridge.coherentMul_toNamed leftOne rightOne)
    (NamedEquivalent.trans
      (Equivalence.approximationEquivalent_toNamed
        (Congruence.sampledProductApproximation_respects
          leftEquivalent rightEquivalent))
      (NamedEquivalent.symm
        (Bridge.coherentMul_toNamed leftTwo rightTwo)))

end

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
