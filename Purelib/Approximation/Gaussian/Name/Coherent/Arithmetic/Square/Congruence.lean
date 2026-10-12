module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square.Bridge
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Name

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square.Congruence

open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square
open Purelib.Approximation.Gaussian.Sequence.Arithmetic
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

/-- Stateful squaring respects operational equality of coherent CCL names. -/
@[expose] def coherentSquare_respects (left right : Coherent.CoherentNamed)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul left.name left.name)
      (Named.mul right.name right.name) :=
  NamedEquivalent.trans
    (Bridge.coherentSquare_toNamed left)
    (NamedEquivalent.trans
      (Equivalence.approximationEquivalent_toNamed
        (Square.squareApproximation_respects equivalent))
      (NamedEquivalent.symm
        (Bridge.coherentSquare_toNamed right)))

end

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square.Congruence
