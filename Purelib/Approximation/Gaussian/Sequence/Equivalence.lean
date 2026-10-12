module
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Sequence.Equivalence

open Purelib.Approximation.Gaussian.Equivalence
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

open Purelib.Approximation

/-- Approximations with identical displayed samples are operationally equivalent, irrespective of their conservative
error bookkeeping. -/
@[expose] def approximationEquivalentOfSamplesEq (left right : ApproximationData)
    (samples : ∀ index, left.sample index = right.sample index) :
    Gaussian.Equivalence.Equivalent left right where
  compare := by
    intro leftStart rightStart target positive
    let comparison :=
      (Equivalent.refl left).compare
        leftStart rightStart target positive
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          rw [← samples rightLater]
          exact comparison.close leftOrder rightOrder }

end

end Purelib.Approximation.Gaussian.Sequence.Equivalence
