module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power
public import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square.Congruence

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude

namespace Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Congruence

open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Arithmetic
open Purelib.Approximation.Gaussian.Name.Arithmetic.Power
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square

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

/-- Any fixed finite number of actual repeated CCL squarings respects operational equality of coherent starting names.
-/
@[expose] def squareIterate_respects : (exponent : Nat) →
    (left right : Coherent.CoherentNamed) →
    Gaussian.Equivalence.NamedEquivalent left.name right.name →
    Gaussian.Equivalence.NamedEquivalent
      (Power.squareIterate
        exponent left.name)
      (Power.squareIterate
        exponent right.name)
  | 0, _left, _right, equivalent => equivalent
  | exponent + 1, left, right, equivalent => by
      let previousLeft : Coherent.CoherentNamed :=
        { name := Power.squareIterate
            exponent left.name
          coherent := Coherent.squareIterateCoherent exponent left.name left.coherent }
      let previousRight : Coherent.CoherentNamed :=
        { name := Power.squareIterate
            exponent right.name
          coherent := Coherent.squareIterateCoherent exponent right.name right.coherent }
      exact Congruence.coherentSquare_respects previousLeft previousRight
        (Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Congruence.squareIterate_respects exponent left right
          equivalent)

end

end Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Congruence
