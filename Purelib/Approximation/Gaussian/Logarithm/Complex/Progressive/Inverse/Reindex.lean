module
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Data.Rat.Bounds.Fraction
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Budget
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Domain
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Sampling
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Bounds.Sum
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local
open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone quarterRadius_scale_mono)

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

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reindex

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.CCL.Transcendental
open Purelib.Data
open Purelib.Data.Rat

/-- The rational scale combining exponential truncation and local-logarithm resampling error. -/
@[expose] public def dynamicLocalExpLogReindexDirectScale : Fraction.Rational := 2 * (10 + 16)

/-- The direct exponential–logarithm resampling scale is nonnegative. -/
theorem dynamicLocalExpLogReindexDirectScale_nonneg :
    0 ≤ dynamicLocalExpLogReindexDirectScale :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))

/-- The combined scale for diagonal movement, progressive exponential movement and direct resampling error. -/
@[expose] public def dynamicLocalExpLogReindexMasterScale : Fraction.Rational :=
  Diagonal.dynamicLocalExpLogErrorScale +
    Budget.errorScale +
      dynamicLocalExpLogReindexDirectScale

/-- The combined exponential–logarithm resampling scale is nonnegative. -/
theorem dynamicLocalExpLogReindexMasterScale_nonneg :
    0 ≤ dynamicLocalExpLogReindexMasterScale :=
  add_nonneg
    (add_nonneg Diagonal.dynamicLocalExpLogErrorScale_nonneg
      Budget.errorScale_nonneg)
    dynamicLocalExpLogReindexDirectScale_nonneg

/-- The combined resampling scale bounds the diagonal exponential–logarithm error scale. -/
private theorem dynamicLocalExpLogScale_le_reindexMaster :
    Diagonal.dynamicLocalExpLogErrorScale ≤
      dynamicLocalExpLogReindexMasterScale
        := by
  unfold dynamicLocalExpLogReindexMasterScale
  calc
    Diagonal.dynamicLocalExpLogErrorScale ≤
        Diagonal.dynamicLocalExpLogErrorScale +
          Exponential.Progressive.Local.Budget.errorScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        Budget.errorScale_nonneg
    _ ≤ Diagonal.dynamicLocalExpLogErrorScale +
          Budget.errorScale +
            Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        dynamicLocalExpLogReindexDirectScale_nonneg

/-- The combined resampling scale bounds the progressive local-exponential error scale. -/
private theorem progressiveExpScale_le_dynamicLocalExpLogReindexMaster :
    Budget.errorScale ≤
      dynamicLocalExpLogReindexMasterScale
        := by
  unfold dynamicLocalExpLogReindexMasterScale
  calc
    Budget.errorScale ≤
        Diagonal.dynamicLocalExpLogErrorScale +
          Exponential.Progressive.Local.Budget.errorScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_left _ _
        Diagonal.dynamicLocalExpLogErrorScale_nonneg
    _ ≤ Diagonal.dynamicLocalExpLogErrorScale +
          Budget.errorScale +
            Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        dynamicLocalExpLogReindexDirectScale_nonneg

/-- The combined resampling scale bounds the direct comparison error scale. -/
public theorem dynamicLocalExpLogReindexDirectScale_le_master :
    dynamicLocalExpLogReindexDirectScale ≤
      dynamicLocalExpLogReindexMasterScale
        := by
  unfold dynamicLocalExpLogReindexMasterScale
  exact Fraction.Compatibility.coordinate_le_add_of_nonneg_left _ _
    (add_nonneg Diagonal.dynamicLocalExpLogErrorScale_nonneg
      Budget.errorScale_nonneg)

/-- Finite resampling bridge between the diagonal `exp_(2n+1)(log_n(z_n))` program and the productive local exponential
reading the progressive local logarithm at its own requested source indices. -/
@[expose] public def dynamicLocalExpLogReindexEquivalent (input : Name.Basic.Named)
    (disk : Local.Domain.Disk input) :
    Equivalent
      (Diagonal.dynamicLocalExpLogApproximation input disk)
      (Name.approximation
        (Local.Name.named input disk)
        (Domain.localComplexLogUnitDisk input disk)) := by
  let source :=
    Local.Name.approximation input disk
  let wrapperDomain := Domain.localComplexLogUnitDisk input disk
  let wrapperExp := Name.approximation
    source.toNamed wrapperDomain
  exact
    { compare := by
        intro leftStart rightStart target positive
        let smallTarget := target / 16
        have smallPositive : 0 < smallTarget :=
          Field.div_pos_direct positive (by decide)
        let start := max leftStart rightStart
        let rightIndex := Search.firstQuarterBelow
          dynamicLocalExpLogReindexMasterScale start smallTarget
        have startLeRight : start ≤ rightIndex :=
          Search.firstQuarterBelow_ge
            dynamicLocalExpLogReindexMasterScale start smallTarget
        have masterSmall :
            Basic.quarterRadius
                dynamicLocalExpLogReindexMasterScale rightIndex <
                  smallTarget :=
          Search.firstQuarterBelow_accurate
            dynamicLocalExpLogReindexMasterScale
              dynamicLocalExpLogReindexMasterScale_nonneg start
                smallTarget
                smallPositive
        let sourceIndex :=
          Sampling.emittedSampleIndex
            source rightIndex
        let leftIndex := max rightIndex sourceIndex
        have rightLeLeft : rightIndex ≤ leftIndex := Data.Nat.Order.le_max_left _ _
        have sourceLeLeft : sourceIndex ≤ leftIndex := Data.Nat.Order.le_max_right _ _
        have sourceRadiusSmall :
            source.radiusSq sourceIndex <
              Process.Sampling.refinementTarget rightIndex :=
          Process.Sampling.stateAt_accurate
            source.toProcess (show source.toProcess.State from (0 : Nat))
              rightIndex
        have sourceMovement := source.later_close sourceLeLeft
        have inputMovement :
            Gaussian.Norm.Basic.normSq (source.sample leftIndex - source.sample sourceIndex) <
              Process.Sampling.refinementTarget rightIndex :=
          sourceMovement.trans_lt sourceRadiusSmall
        have leftInputUnit : Gaussian.Norm.Basic.normSq (source.sample leftIndex) ≤ 1 := by
          exact Local.Horner.Sample.sample_bounded_one
            (Local.Sampling.inputSample_bound
              disk leftIndex) leftIndex
        have rightInputUnit : Gaussian.Norm.Basic.normSq (source.sample sourceIndex) ≤ 1 := by
          exact Local.Horner.Sample.sample_bounded_one
            (Local.Sampling.inputSample_bound
              disk sourceIndex) sourceIndex
        have depthOrder : rightIndex ≤ 2 * leftIndex + 1 := by
          have doubled : 2 * leftIndex = leftIndex + leftIndex := by
            rewrite [Data.Nat.Multiplication.right_distrib 1 1 leftIndex,
              Nat.one_mul]
            exact Eq.refl _
          rewrite [doubled]
          exact Nat.le_trans rightLeLeft
            (Nat.le_trans (Nat.le_add_right leftIndex leftIndex) (Nat.le_succ _))
        have truncation := Horner.Sample.sample_later_close
          (source.sample leftIndex) leftInputUnit depthOrder
        have inputEffect := Horner.Sample.sample_input_close
          (source.sample leftIndex) (source.sample sourceIndex)
            leftInputUnit rightInputUnit rightIndex
        have inputStrict :
            Gaussian.Norm.Basic.normSq
                (Horner.Sample.sample
                    (source.sample leftIndex) rightIndex -
                  Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex) <
              16 * Process.Sampling.refinementTarget
                rightIndex :=
          inputEffect.trans_lt
            (Arithmetic.mul_lt_mul_of_pos_left_direct
              (by decide) inputMovement)
        have direct :
            Gaussian.Norm.Basic.normSq
                (Horner.Sample.sample
                    (source.sample leftIndex) (2 * leftIndex + 1) -
                  Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex) <
              Basic.quarterRadius

                  dynamicLocalExpLogReindexDirectScale
                  rightIndex := by
          calc
            Gaussian.Norm.Basic.normSq
                (Horner.Sample.sample
                    (source.sample leftIndex) (2 * leftIndex + 1) -
                  Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex) ≤
              2 *
                (Gaussian.Norm.Basic.normSq
                    (Horner.Sample.sample
                        (source.sample leftIndex) (2 * leftIndex + 1) -
                      Horner.Sample.sample
                        (source.sample leftIndex) rightIndex) +
                  Gaussian.Norm.Basic.normSq
                    (Horner.Sample.sample
                        (source.sample leftIndex) rightIndex -
                      Horner.Sample.sample
                        (source.sample sourceIndex) rightIndex)) :=
              Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
            _ < 2 *
                (Basic.quarterRadius 10 rightIndex +
                  16 * Process.Sampling.refinementTarget
                    rightIndex) :=
              Bounds.Sum.twice_add_lt_twice_add_of_le_of_lt truncation inputStrict
            _ = Basic.quarterRadius

                  dynamicLocalExpLogReindexDirectScale
                  rightIndex := by
              unfold
                dynamicLocalExpLogReindexDirectScale
              rw [Basic.quarterRadius_eq_mul_pow,
                Process.Sampling.refinementTarget,
                Basic.quarterRadius_eq_mul_pow,
                Basic.quarterRadius_eq_mul_pow]
              ring1
        have directSmall := direct.trans
          ((quarterRadius_scale_mono
              dynamicLocalExpLogReindexDirectScale_le_master
                rightIndex).trans_lt
            masterSmall)
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := (Data.Nat.Order.le_max_left leftStart rightStart).trans
              (startLeRight.trans rightLeLeft)
            right_ge := (Data.Nat.Order.le_max_right leftStart rightStart).trans startLeRight
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have leftTail :=
                (Diagonal.dynamicLocalExpLogApproximation input disk).later_close
                  leftOrder
              have leftRadiusToMaster :
                  Basic.quarterRadius
                      Diagonal.dynamicLocalExpLogErrorScale leftIndex ≤
                    Basic.quarterRadius
                      dynamicLocalExpLogReindexMasterScale rightIndex :=
                (quarterRadius_scale_mono
                    dynamicLocalExpLogScale_le_reindexMaster
                      leftIndex).trans
                  (quarterRadius_antitone
                    dynamicLocalExpLogReindexMasterScale_nonneg
                      rightLeLeft)
              have leftTailSmall := leftTail.trans_lt
                (leftRadiusToMaster.trans_lt masterSmall)
              have rightTail := wrapperExp.later_close rightOrder
              have rightTailSmall := rightTail.trans_lt
                ((quarterRadius_scale_mono
                    progressiveExpScale_le_dynamicLocalExpLogReindexMaster
                    rightIndex).trans_lt masterSmall)
              have rightTailReverse :
                  Gaussian.Norm.Basic.normSq
                      (wrapperExp.sample rightIndex -
                        wrapperExp.sample rightLater) < smallTarget := by
                have identity : wrapperExp.sample rightIndex -
                      wrapperExp.sample rightLater =
                    -(wrapperExp.sample rightLater -
                      wrapperExp.sample rightIndex) := by
                  apply Gaussian.Basic.ext <;>
                    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
                      Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1
                rw [identity, Gaussian.Norm.Basic.normSq_neg]
                exact rightTailSmall
              have baseIdentity :
                  (Diagonal.dynamicLocalExpLogApproximation input disk).sample
                      leftIndex =
                    Horner.Sample.sample
                      (source.sample leftIndex) (2 * leftIndex + 1) := by
                rfl
              have wrapperIdentity : wrapperExp.sample rightIndex =
                  Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex := rfl
              rw [← baseIdentity, ← wrapperIdentity] at directSmall
              have middle := (Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans_lt
                (Arithmetic.mul_lt_mul_of_pos_left_direct
                  (by decide)
                  (Arithmetic.add_lt_add_direct
                    directSmall rightTailReverse))
              calc
                Gaussian.Norm.Basic.normSq
                    ((Diagonal.dynamicLocalExpLogApproximation input disk).sample
                        leftLater - wrapperExp.sample rightLater) ≤
                  2 *
                    (Gaussian.Norm.Basic.normSq
                        ((Diagonal.dynamicLocalExpLogApproximation input
                          disk).sample
                            leftLater -
                          (Diagonal.dynamicLocalExpLogApproximation input
                            disk).sample
                            leftIndex) +
                      Gaussian.Norm.Basic.normSq
                        ((Diagonal.dynamicLocalExpLogApproximation input
                          disk).sample
                            leftIndex - wrapperExp.sample rightLater)) :=
                  Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
                _ < 2 *
                    (smallTarget + 2 * (smallTarget + smallTarget)) :=
                  Arithmetic.mul_lt_mul_of_pos_left_direct
                    (by decide)
                    (Arithmetic.add_lt_add_direct
                      leftTailSmall middle)
                _ = 10 * smallTarget := by ring1
                _ < target := by
                  dsimp only [smallTarget]
                  exact Bounds.Fraction.ten_sixteenths_lt positive } }

/-- Name-level form of the finite resampling bridge for local exp-log. -/
@[expose] public def dynamicLocalExpLog_toLocalExp (input : Name.Basic.Named)
    (disk : Local.Domain.Disk input) :
    NamedEquivalent
      (Diagonal.dynamicLocalExpLogApproximation input disk).toNamed
      (Name.named
        (Local.Name.named input disk)
        (Domain.localComplexLogUnitDisk input disk)) :=
  Equivalence.approximationEquivalent_toNamed
    (dynamicLocalExpLogReindexEquivalent input disk)
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reindex

end
