module
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Bounds.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

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

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Congruence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Sampling
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

/-- The progressive local exponential respects finite operational equality of unit-disk input names.

One finite synchronized pair of input readings is compared by the Horner sensitivity theorem; two explicitly bounded
finite depth tails complete the output comparison. -/
@[expose] public def localExpApproximation_respects {left right : Gaussian.Name.Basic.Named}
    (leftDomain : Name.UnitDisk left)
    (rightDomain : Name.UnitDisk right)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left right) :
    Gaussian.Equivalence.Equivalent
      (Name.approximation left leftDomain)
      (Name.approximation right rightDomain) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    let inputTarget := smallTarget / 16
    have inputPositive : 0 < inputTarget :=
      Fraction.Order.Field.div_pos_direct smallPositive (by decide)
    let inputComparison :=
      equivalent.compare leftStart rightStart inputTarget inputPositive
    let start := max (max leftStart rightStart)
      (max inputComparison.leftIndex inputComparison.rightIndex)
    let depth := Search.firstQuarterBelow
      10 start smallTarget
    have startLeDepth : start ≤ depth :=
      Search.firstQuarterBelow_ge
        10 start smallTarget
    have tailSmall :
        Geometric.Basic.quarterRadius 10 depth <
          smallTarget :=
      Search.firstQuarterBelow_accurate
        10 (by decide) start smallTarget smallPositive
    have inputLeftLeDepth : inputComparison.leftIndex ≤ depth :=
      (Purelib.Data.Nat.Order.le_max_left inputComparison.leftIndex
        inputComparison.rightIndex).trans
        ((Purelib.Data.Nat.Order.le_max_right (max leftStart rightStart)
          (max inputComparison.leftIndex inputComparison.rightIndex)).trans
          startLeDepth)
    have inputRightLeDepth : inputComparison.rightIndex ≤ depth :=
      (Purelib.Data.Nat.Order.le_max_right inputComparison.leftIndex
        inputComparison.rightIndex).trans
        ((Purelib.Data.Nat.Order.le_max_right (max leftStart rightStart)
          (max inputComparison.leftIndex inputComparison.rightIndex)).trans
          startLeDepth)
    exact
      { leftIndex := depth
        rightIndex := depth
        left_ge := (Purelib.Data.Nat.Order.le_max_left leftStart rightStart).trans
          ((Purelib.Data.Nat.Order.le_max_left (max leftStart rightStart)
            (max inputComparison.leftIndex inputComparison.rightIndex)).trans
            startLeDepth)
        right_ge := (Purelib.Data.Nat.Order.le_max_right leftStart rightStart).trans
          ((Purelib.Data.Nat.Order.le_max_left (max leftStart rightStart)
            (max inputComparison.leftIndex inputComparison.rightIndex)).trans
            startLeDepth)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          let leftInput :=
            Exp.inputSample left leftLater
          let rightInput :=
            Exp.inputSample right rightLater
          have leftInputUnit : Data.Gaussian.Norm.Basic.normSq leftInput ≤ 1 :=
            Sampling.inputSample_unit
              leftDomain leftLater
          have rightInputUnit : Data.Gaussian.Norm.Basic.normSq rightInput ≤ 1 :=
            Sampling.inputSample_unit
              rightDomain rightLater
          have inputClose : Data.Gaussian.Norm.Basic.normSq (leftInput - rightInput) < inputTarget :=
            inputComparison.close
              (inputLeftLeDepth.trans leftOrder)
              (inputRightLeDepth.trans rightOrder)
          have directLe :=
            Horner.Sample.sample_input_close
              leftInput rightInput leftInputUnit rightInputUnit depth
          have direct :
              Data.Gaussian.Norm.Basic.normSq
                  (Horner.Sample.sample leftInput depth -
                    Horner.Sample.sample rightInput depth) <
                smallTarget := by
            calc
              Data.Gaussian.Norm.Basic.normSq
                  (Horner.Sample.sample leftInput depth -
                    Horner.Sample.sample rightInput depth) ≤
                16 * Data.Gaussian.Norm.Basic.normSq (leftInput - rightInput) := directLe
              _ < 16 * inputTarget :=
                Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                  (by decide) inputClose
              _ = smallTarget := by
                dsimp only [inputTarget]
                exact Purelib.Data.Rat.Bounds.Fraction.sixteenths smallTarget
          have leftTail :
              Data.Gaussian.Norm.Basic.normSq
                  (Horner.Sample.sample leftInput leftLater -
                    Horner.Sample.sample leftInput depth) <
                smallTarget :=
            (Horner.Sample.sample_later_close
              leftInput leftInputUnit leftOrder).trans_lt tailSmall
          have rightTailForward :
              Data.Gaussian.Norm.Basic.normSq
                  (Horner.Sample.sample rightInput rightLater -
                    Horner.Sample.sample rightInput depth) <
                smallTarget :=
            (Horner.Sample.sample_later_close
              rightInput rightInputUnit rightOrder).trans_lt tailSmall
          have rightTail :
              Data.Gaussian.Norm.Basic.normSq
                  (Horner.Sample.sample rightInput depth -
                    Horner.Sample.sample rightInput rightLater) <
                smallTarget := by
            have identity :
                Horner.Sample.sample rightInput depth -
                    Horner.Sample.sample rightInput rightLater =
                  -(Horner.Sample.sample rightInput rightLater -
                    Horner.Sample.sample rightInput depth) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                  Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
            rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
            exact rightTailForward
          have middle :
              Data.Gaussian.Norm.Basic.normSq
                  (Horner.Sample.sample leftInput depth -
                    Horner.Sample.sample rightInput rightLater) <
                2 * (smallTarget + smallTarget) :=
            (Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans_lt
              (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  direct rightTail))
          change Data.Gaussian.Norm.Basic.normSq
              (Horner.Sample.sample leftInput leftLater -
                Horner.Sample.sample rightInput rightLater) < target
          calc
            Data.Gaussian.Norm.Basic.normSq
                (Horner.Sample.sample leftInput leftLater -
                  Horner.Sample.sample rightInput rightLater) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    (Horner.Sample.sample leftInput leftLater -
                      Horner.Sample.sample leftInput depth) +
                  Data.Gaussian.Norm.Basic.normSq
                    (Horner.Sample.sample leftInput depth -
                      Horner.Sample.sample rightInput rightLater)) :=
                Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
            _ < 2 *
                (smallTarget + 2 * (smallTarget + smallTarget)) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct leftTail middle)
            _ = 10 * smallTarget := by ring1
            _ < target := by
              dsimp only [smallTarget]
              exact Purelib.Data.Rat.Bounds.Fraction.ten_sixteenths_lt positive }

/-- Productive-name form of local exponential congruence. -/
@[expose] public def localExpNamed_respects {left right : Gaussian.Name.Basic.Named}
    (leftDomain : Name.UnitDisk left)
    (rightDomain : Name.UnitDisk right)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left right) :
    Gaussian.Equivalence.NamedEquivalent
      (Name.named left leftDomain)
      (Name.named right rightDomain) :=
  Equivalent.trans
    (Equivalent.toNamed_sampling
      (Name.approximation left leftDomain))
    (Equivalent.trans
      (Approximation.Gaussian.Exponential.Progressive.Local.Congruence.localExpApproximation_respects leftDomain
        rightDomain equivalent)
      (Equivalent.symm
        (Equivalent.toNamed_sampling
          (Name.approximation right rightDomain))))
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Congruence

end
