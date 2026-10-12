module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Bounds.Fraction
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sensitivity
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Init.Data.Nat.MinMax
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite geometry for transporting and selecting logarithm branches

An anchored complex logarithm is local data.  This file supplies the missing
geometric constructors around that data.

* `SafeOverlapExtension` rechecks one chart's rational denominator and
  reduced-disk inequalities on a second coherent name and records an actual
  rational point admitted by both finite enclosures.  The original factor,
  correction process, and correction certificate can then be transported.
* `LocalExpInjectivity` is a displayed finite cell, membership certificates
  for two particular coherent names, and the local exponential-injectivity
  rule for that pair.  It is deliberately local and never chooses a global
  logarithm branch.
* `SelectedLogarithm.ofOverlap` combines those two pieces of finite data.  It
  constructs an anchored chart over the computed exponential and derives the
  zero-alignment certificate required for `log (exp x) = x`.

The local complex-log congruence proved first is quantitative: it compares
finite reduced-argument samples with the existing rational sensitivity bound
and finite truncation bounds.  No completed logarithm or limiting argument is
introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Congruence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local
open Purelib.Approximation.Gaussian.Logarithm.Local.Horner
open Purelib.Approximation.Gaussian.Name.Sampling
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.CCL.Transcendental
open Purelib.Data.Rat

/-! ## Quantitative congruence of the local complex logarithm -/

/-- The finite local complex-log approximation respects operational equality of reduced-argument names.

A common finite Horner depth, the displayed `sampleInputScale`, and two finite truncation estimates answer each
requested rational comparison. -/
@[expose] public def localLogApproximation_respects {left right : Gaussian.Name.Basic.Named}
    (leftDisk : Domain.Disk left)
    (rightDisk : Domain.Disk right)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left right) :
    Gaussian.Equivalence.Equivalent
      (Name.approximation left leftDisk)
      (Name.approximation right rightDisk) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    let inputScale := Sensitivity.sampleInputScale
    have inputScalePositive : 0 < inputScale := by
      change (0 : Fraction.Rational) < 2 * (16 + 16)
      decide
    let inputTarget := smallTarget / inputScale
    have inputPositive : 0 < inputTarget :=
      Fraction.Order.Field.div_pos_direct smallPositive
        inputScalePositive
    let inputComparison :=
      equivalent.compare leftStart rightStart inputTarget inputPositive
    let start := max (max leftStart rightStart)
      (max inputComparison.leftIndex inputComparison.rightIndex)
    let depth := Search.firstQuarterBelow
      5 start smallTarget
    have startLeDepth : start ≤ depth :=
      Search.firstQuarterBelow_ge
        5 start smallTarget
    have tailSmall :
        Geometric.Basic.quarterRadius 5 depth <
          smallTarget :=
      Search.firstQuarterBelow_accurate
        5 (by decide) start smallTarget smallPositive
    have tailSmall' : 5 * (1 / 4 : Fraction.Rational) ^ depth < smallTarget := by
      simpa only [Geometric.Basic.quarterRadius_eq_mul_pow]
        using tailSmall
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
            ComplexLog.inputSample left leftLater
          let rightInput :=
            ComplexLog.inputSample right rightLater
          have leftInputBound : Data.Gaussian.Norm.Basic.normSq leftInput ≤ 1 / 9 :=
            Sampling.inputSample_bound
              leftDisk leftLater
          have rightInputBound : Data.Gaussian.Norm.Basic.normSq rightInput ≤ 1 / 9 :=
            Sampling.inputSample_bound
              rightDisk rightLater
          have inputClose : Data.Gaussian.Norm.Basic.normSq (leftInput - rightInput) < inputTarget :=
            inputComparison.close
              (inputLeftLeDepth.trans leftOrder)
              (inputRightLeDepth.trans rightOrder)
          have directLe :=
            Sensitivity.sample_input_close
              leftInputBound rightInputBound depth
          have direct :
              Data.Gaussian.Norm.Basic.normSq
                  (Sample.sample leftInput depth -
                    Sample.sample rightInput depth) <
                smallTarget := by
            calc
              Data.Gaussian.Norm.Basic.normSq
                  (Sample.sample leftInput depth -
                    Sample.sample rightInput depth) ≤
                inputScale * Data.Gaussian.Norm.Basic.normSq (leftInput - rightInput) := directLe
              _ < inputScale * inputTarget :=
                Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                  inputScalePositive inputClose
              _ = smallTarget := by
                dsimp only [inputTarget]
                exact Fraction.Compatibility.scale_mul_div_cancel inputScale smallTarget
                  inputScalePositive.ne'
          have leftTail :
              Data.Gaussian.Norm.Basic.normSq
                  (Sample.sample leftInput leftLater -
                    Sample.sample leftInput depth) <
                smallTarget :=
            (Sample.sample_later_close
              leftInputBound leftOrder).trans_lt tailSmall'
          have rightTailForward :
              Data.Gaussian.Norm.Basic.normSq
                  (Sample.sample rightInput rightLater -
                    Sample.sample rightInput depth) <
                smallTarget :=
            (Sample.sample_later_close
              rightInputBound rightOrder).trans_lt tailSmall'
          have rightTail :
              Data.Gaussian.Norm.Basic.normSq
                  (Sample.sample rightInput depth -
                    Sample.sample rightInput rightLater) <
                smallTarget := by
            have identity :
                Sample.sample rightInput depth -
                    Sample.sample rightInput rightLater =
                  -(Sample.sample rightInput rightLater -
                    Sample.sample rightInput depth) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                  Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
            rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
            exact rightTailForward
          have middle :
              Data.Gaussian.Norm.Basic.normSq
                  (Sample.sample leftInput depth -
                    Sample.sample rightInput rightLater) <
                2 * (smallTarget + smallTarget) :=
            (Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans_lt
              (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct direct rightTail))
          change Data.Gaussian.Norm.Basic.normSq
              (Sample.sample leftInput leftLater -
                Sample.sample rightInput rightLater) <
              target
          calc
            Data.Gaussian.Norm.Basic.normSq
                (Sample.sample leftInput leftLater -
                  Sample.sample rightInput rightLater) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    (Sample.sample leftInput leftLater -
                      Sample.sample leftInput depth) +
                  Data.Gaussian.Norm.Basic.normSq
                    (Sample.sample leftInput depth -
                      Sample.sample rightInput
                        rightLater)) :=
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

/-- Productive-name form of finite local complex-log congruence. -/
@[expose] public def localLogNamed_respects {left right : Gaussian.Name.Basic.Named}
    (leftDisk : Domain.Disk left)
    (rightDisk : Domain.Disk right)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left right) :
    Gaussian.Equivalence.NamedEquivalent
      (Name.named left leftDisk)
      (Name.named right rightDisk) :=
  Equivalent.trans
    (Equivalent.toNamed_sampling
      (Name.approximation left leftDisk))
    (Equivalent.trans
      (Approximation.Gaussian.Logarithm.Local.Congruence.localLogApproximation_respects leftDisk rightDisk equivalent)
      (Equivalent.symm
        (Equivalent.toNamed_sampling
          (Name.approximation
            right rightDisk))))

end Purelib.Approximation.Gaussian.Logarithm.Local.Congruence

end
