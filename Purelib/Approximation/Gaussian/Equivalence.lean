module
public import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Gaussian.Name.Basic (Named)

/-!
# Retained finite operational comparisons

Finite comparison records retain their original approximation owners, selected
indices and sample bounds. All comparison builders use the same executable
refinement and sampling programs and their original cached observations.
-/

namespace Purelib.Approximation.Gaussian.Equivalence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Nat

set_option genInjectivity false in
/-- One finite tail comparison below a displayed squared tolerance.

The two retained approximation owners and starting indices determine this
finite comparison. Its computed later indices retain both start bounds and the
squared-distance certificate for every pair of still later original samples. -/
public structure Comparison (left right : ApproximationData)
    (leftStart rightStart : Nat) (target : Fraction.Rational) where
  /-- The computed comparison index for the left approximation. -/ leftIndex : Nat
  /-- The computed comparison index for the right approximation. -/ rightIndex : Nat
  /-- The left comparison index is no earlier than the requested start. -/ left_ge : leftStart ≤ leftIndex
  /-- The right comparison index is no earlier than the requested start. -/ right_ge : rightStart ≤ rightIndex
  /-- Every pair of samples beyond the computed indices has squared distance below the displayed target. -/ close : ∀
    {leftLater rightLater : Nat},
    leftIndex ≤ leftLater → rightIndex ≤ rightLater →
      Data.Gaussian.Norm.Basic.normSq (left.sample leftLater - right.sample rightLater) < target

constructive_injectivity Comparison

set_option genInjectivity false in
/-- Two approximation sidechannels have the same finite operational value when their displayed tails can be synchronized
below every positive rational squared tolerance.

For each pair of finite starting indices and positive rational tolerance,
the retained comparison function returns explicit later indices and certificates
for the original approximation samples at all permitted later stages. -/
public structure Equivalent (left right : ApproximationData) where
  /-- Compute later comparison indices for any two starts and any positive rational squared tolerance. -/ compare : ∀
    (leftStart rightStart : Nat) (target : Fraction.Rational),
    0 < target → Comparison left right leftStart rightStart target

constructive_injectivity Equivalent

/-- Every approximation is operationally equivalent to itself.

The original maximum starting index is refined once at one quarter of
the requested tolerance. Both retained comparison indices use that same
refinement and its finite pairwise-error certificate. -/
@[expose] public def Equivalent.refl (approximation : ApproximationData) :
    Equivalent approximation approximation where
  compare := by
    intro leftStart rightStart target positive
    let start := max leftStart rightStart
    have leftMaximum : leftStart ≤ start := by
      change leftStart ≤ max leftStart rightStart
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have rightMaximum : rightStart ≤ start := by
      change rightStart ≤ max leftStart rightStart
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    let index := approximation.refineIndex start (target / 4)
      (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive)
    have radiusSmall : approximation.radiusSq index < target / 4 :=
      approximation.refineIndex_accurate start (target / 4)
        (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive)
    exact
      { leftIndex := index
        rightIndex := index
        left_ge := leftMaximum.trans
          (approximation.refineIndex_ge start (target / 4)
            (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive))
        right_ge := rightMaximum.trans
          (approximation.refineIndex_ge start (target / 4)
            (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive))
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftClose := approximation.later_close leftOrder
          have rightClose := approximation.later_close rightOrder
          have rightClose' :
              Data.Gaussian.Norm.Basic.normSq
                (approximation.sample index -
                  approximation.sample rightLater) ≤
                approximation.radiusSq index := by
            rw [show approximation.sample index - approximation.sample rightLater =
                -(approximation.sample rightLater - approximation.sample index) by
                  apply Basic.ext <;>
                    simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im] <;> ring1,
              Norm.Basic.normSq_neg]
            exact rightClose
          calc
            Data.Gaussian.Norm.Basic.normSq
                (approximation.sample leftLater -
                  approximation.sample rightLater) ≤
                2 * (Data.Gaussian.Norm.Basic.normSq
                    (approximation.sample leftLater -
                      approximation.sample index) +
                  Data.Gaussian.Norm.Basic.normSq
                    (approximation.sample index -
                      approximation.sample rightLater)) :=
              Norm.Bounds.normSq_sub_le_via _ _ _
            _ ≤ 2 *
                (approximation.radiusSq index +
                  approximation.radiusSq index) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add leftClose rightClose') (by decide)
            _ < 2 * (target / 4 + target / 4) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  radiusSmall radiusSmall)
            _ = target := by
              have quarterSum : target / 4 + target / 4 = target / 2 := by
                apply Fraction.Field.mul_right_cancel_of_ne
                  (show (4 : Fraction.Rational) ≠ 0 by decide)
                calc
                  (target / 4 + target / 4) * 4 =
                      (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
                  _ = target + target := by
                    rw [show target / 4 * 4 = target from
                      Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
                  _ = target * 2 := by ring1
                  _ = ((target / 2) * 2) * 2 := by
                    rw [show target / 2 * 2 = target from
                      Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
                  _ = (target / 2) * (2 * 2) :=
                    Fraction.Field.mul_assoc (target / 2) 2 2
                  _ = (target / 2) * 4 := by
                    rw [show (2 : Fraction.Rational) * 2 = 4 by decide]
              rw [quarterSum, Fraction.Field.mul_comm]
              exact Fraction.Field.div_mul_cancel_of_ne target 2 (by decide) }

/-- Operational equivalence is symmetric.

The comparison calls the original forward comparison with exchanged
starts. It retains the computed indices in reverse order and transports the
same squared-distance bound through Gaussian negation. -/
@[expose] public def Equivalent.symm {left right : ApproximationData}
    (equivalent : Equivalent left right) : Equivalent right left where
  compare := by
    intro rightStart leftStart target positive
    let comparison := equivalent.compare leftStart rightStart target positive
    exact
      { leftIndex := comparison.rightIndex
        rightIndex := comparison.leftIndex
        left_ge := comparison.right_ge
        right_ge := comparison.left_ge
        close := by
          intro rightLater leftLater rightOrder leftOrder
          have close := comparison.close leftOrder rightOrder
          have identity :
              right.sample rightLater - left.sample leftLater =
                -(left.sample leftLater - right.sample rightLater) := by
            apply Basic.ext <;>
              simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im] <;> ring1
          rw [identity, Norm.Basic.normSq_neg]
          exact close }

/-- Operational equivalence is transitive by sequentially synchronizing the middle approximation.

The first comparison selects the left and middle indices, and the second
starts at that retained middle index. Both use a quarter of the requested
tolerance, so their original squared-distance bounds compose at the same middle sample. -/
@[expose] public def Equivalent.trans {left middle right : ApproximationData}
    (leftMiddle : Equivalent left middle)
    (middleRight : Equivalent middle right) : Equivalent left right where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let first := leftMiddle.compare leftStart 0 smallTarget smallPositive
    let second := middleRight.compare first.rightIndex rightStart
      smallTarget smallPositive
    exact
      { leftIndex := first.leftIndex
        rightIndex := second.rightIndex
        left_ge := first.left_ge
        right_ge := second.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftClose :
              Data.Gaussian.Norm.Basic.normSq
                (left.sample leftLater -
                  middle.sample second.leftIndex) < smallTarget :=
            first.close leftOrder second.left_ge
          have rightClose :
              Data.Gaussian.Norm.Basic.normSq
                (middle.sample second.leftIndex -
                  right.sample rightLater) < smallTarget :=
            second.close (Nat.le_refl _) rightOrder
          calc
            Data.Gaussian.Norm.Basic.normSq (left.sample leftLater - right.sample rightLater) ≤
                2 * (Data.Gaussian.Norm.Basic.normSq
                    (left.sample leftLater -
                      middle.sample second.leftIndex) +
                  Data.Gaussian.Norm.Basic.normSq
                    (middle.sample second.leftIndex -
                      right.sample rightLater)) :=
              Norm.Bounds.normSq_sub_le_via _ _ _
            _ < 2 * (smallTarget + smallTarget) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  leftClose rightClose)
            _ = target := by
              dsimp only [smallTarget]
              have quarterSum : target / 4 + target / 4 = target / 2 := by
                apply Fraction.Field.mul_right_cancel_of_ne
                  (show (4 : Fraction.Rational) ≠ 0 by decide)
                calc
                  (target / 4 + target / 4) * 4 =
                      (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
                  _ = target + target := by
                    rw [show target / 4 * 4 = target from
                      Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
                  _ = target * 2 := by ring1
                  _ = ((target / 2) * 2) * 2 := by
                    rw [show target / 2 * 2 = target from
                      Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
                  _ = (target / 2) * (2 * 2) :=
                    Fraction.Field.mul_assoc (target / 2) 2 2
                  _ = (target / 2) * 4 := by
                    rw [show (2 : Fraction.Rational) * 2 = 4 by decide]
              rw [quarterSum, Fraction.Field.mul_comm]
              exact Fraction.Field.div_mul_cancel_of_ne target 2 (by decide) }

/-- Two finite approximation programs which display one and the same exact Gaussian rational at every index are
operationally equivalent.

Every sample of each original approximation equals the displayed Gaussian
rational witness. The supplied starting indices already form a comparison,
and their zero separation meets every positive rational tolerance. -/
@[expose] public def Equivalent.of_constant_samples (left right : ApproximationData)
    (value : Basic.Canonical)
    (leftSample : ∀ index, left.sample index = value)
    (rightSample : ∀ index, right.sample index = value) :
    Equivalent left right where
  compare := by
    intro leftStart rightStart target positive
    exact
      { leftIndex := leftStart
        rightIndex := rightStart
        left_ge := Nat.le_refl _
        right_ge := Nat.le_refl _
        close := by
          intro leftLater rightLater _ _
          rw [leftSample leftLater, rightSample rightLater, _root_.sub_self,
            Norm.Basic.normSq_zero]
          exact positive }

/-- Operational equality of finite-request arithmetic CCL programs is equality of the nested finite witness
approximations calculated from their current states. This definition compares only displayed rational samples and
rational error requests; it does not quantify over completed values.

The two original names supply their own retained sampling approximations.
The resulting comparison retains those owners and synchronizes their actual
finite witness readings for each displayed positive rational tolerance. -/
@[expose] public def NamedEquivalent (left right : Named) :=
  Equivalent
    (Gaussian.Name.Sampling.approximation left)
    (Gaussian.Name.Sampling.approximation right)

/-- Every Gaussian name is operationally equivalent to itself.

The original name is sampled through its retained process and starting
state. Reflexivity retains the same sampled approximation on both sides. -/
@[expose] public def NamedEquivalent.refl (name : Named) : NamedEquivalent name name :=
  Equivalent.refl _

/-- Reverse a retained finite-request operational equivalence of names.

The two names retain their original sampled approximation owners.
Reversing the supplied comparison exchanges its indices and squared-distance evidence. -/
@[expose] public def NamedEquivalent.symm {left right : Named} (equivalent : NamedEquivalent left
  right) :
    NamedEquivalent right left :=
  Equivalent.symm equivalent

/-- Compose two finite-request operational equivalences through their common middle name.

The middle name supplies the common retained sampled approximation.
The two given comparisons are composed through its actual samples and indices. -/
@[expose] public def NamedEquivalent.trans {left middle right : Named}
    (leftMiddle : NamedEquivalent left middle)
    (middleRight : NamedEquivalent middle right) :
    NamedEquivalent left right :=
  Equivalent.trans leftMiddle middleRight

end Purelib.Approximation.Gaussian.Equivalence
