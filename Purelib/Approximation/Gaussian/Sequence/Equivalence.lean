module
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Gaussian.Sequence

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Sequence.Equivalence

open Purelib.Approximation.Rational.Geometric
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

/-- Compare an original approximation with an exact constant from its geometric sample bounds.

The coefficient-computed finite search selects an index no earlier than the
original left start. Every later original sample meets the requested tolerance;
the right constant retains its own independent starting index.
-/
@[expose] def equivalent_constant (approximation : ApproximationData)
    (value : Purelib.Data.Gaussian.Basic.Canonical)
    (scale : Purelib.Data.Rat.Fraction.Rational) (nonnegative : 0 ≤ scale)
    (samples : ∀ index, Purelib.Data.Gaussian.Norm.Basic.normSq
      (approximation.sample index - value) ≤
        Rational.Geometric.Basic.quarterRadius scale index) :
    Gaussian.Equivalence.Equivalent approximation (Constant.constantApproximation value) where
  compare firstStart secondStart target targetPositive := by
    let index := Search.firstQuarterBelow scale firstStart target
    exact
      { leftIndex := index
        rightIndex := secondStart
        left_ge := Search.firstQuarterBelow_ge scale firstStart target
        right_ge := Nat.le_refl secondStart
        close := by
          intro firstLater secondLater firstOrder secondOrder
          change Purelib.Data.Gaussian.Norm.Basic.normSq
            (approximation.sample firstLater - value) < target
          exact (samples firstLater).trans_lt
            ((Rational.Geometric.Basic.quarterRadius_antitone nonnegative firstOrder).trans_lt
              (Search.firstQuarterBelow_accurate scale nonnegative
                firstStart target targetPositive)) }

/-- Compare an original approximation with a constant using a geometric bound valid after one retained stage.

The computed index follows both the caller's original start and the retained
bound's floor. Every later original sample meets the tolerance, while the
right constant keeps its own independent starting stage.
-/
@[expose] def equivalent_constant_after (approximation : ApproximationData)
    (value : Purelib.Data.Gaussian.Basic.Canonical) (floor : Nat)
    (scale : Purelib.Data.Rat.Fraction.Rational) (nonnegative : 0 ≤ scale)
    (samples : ∀ index, floor ≤ index → Purelib.Data.Gaussian.Norm.Basic.normSq
      (approximation.sample index - value) ≤ Rational.Geometric.Basic.quarterRadius scale index) :
    Gaussian.Equivalence.Equivalent approximation (Constant.constantApproximation value) where
  compare firstStart secondStart target positive := by
    let start := max firstStart floor
    have firstLe : firstStart ≤ start := by
      change firstStart ≤ max firstStart floor
      rewrite [Purelib.Data.Nat.Order.max_eq_natMax]
      exact Purelib.Data.Nat.Order.le_max_left _ _
    have floorLe : floor ≤ start := by
      change floor ≤ max firstStart floor
      rewrite [Purelib.Data.Nat.Order.max_eq_natMax]
      exact Purelib.Data.Nat.Order.le_max_right _ _
    let index := Search.firstQuarterBelow scale start target
    have startLe := Search.firstQuarterBelow_ge scale start target
    exact
      { leftIndex := index
        rightIndex := secondStart
        left_ge := firstLe.trans startLe
        right_ge := Nat.le_refl secondStart
        close := by
          intro firstLater secondLater firstOrder secondOrder
          change Purelib.Data.Gaussian.Norm.Basic.normSq (approximation.sample firstLater - value) < target
          exact (samples firstLater (floorLe.trans (startLe.trans firstOrder))).trans_lt
            ((Rational.Geometric.Basic.quarterRadius_antitone nonnegative firstOrder).trans_lt
              (Search.firstQuarterBelow_accurate scale nonnegative start target positive)) }

end

end Purelib.Approximation.Gaussian.Sequence.Equivalence
