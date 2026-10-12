module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum.Congruence
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence

import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
import Purelib.Approximation.Gaussian.Sequence.Name

/-!
# Addition of coherent names respects finite equivalence

The two stateful sums are compared through their sampled approximations and
the retained bridges from each original pair of coherent input names.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Sequence.Name

/-- Stateful addition respects operational equality independently in both coherent operands.

Each stateful sum retains its bridge to the corresponding sampled sum.
The component equivalences compare those sampled sums and compose the two bridges. -/
@[expose] public def coherentAdd_respects
    (leftOne leftTwo rightOne rightTwo : Coherent.CoherentNamed)
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent rightOne.name rightTwo.name) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        leftOne.name rightOne.name)
      (Named.add
        leftTwo.name rightTwo.name) :=
  NamedEquivalent.trans
    (Bridge.coherentAdd_toNamed leftOne rightOne)
    (NamedEquivalent.trans
      (Sequence.Name.Equivalence.approximationEquivalent_toNamed
        (Sequence.Arithmetic.Sum.Congruence.sampledSumApproximation_respects leftEquivalent rightEquivalent))
      (NamedEquivalent.symm
        (Bridge.coherentAdd_toNamed leftTwo rightTwo)))
end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
