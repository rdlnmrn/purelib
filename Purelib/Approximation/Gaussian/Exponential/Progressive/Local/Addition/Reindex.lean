module
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Sequence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Budget
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Bounds.Sum
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Bounds.Fraction
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

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

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Reindex

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.CCL.Transcendental
open Purelib.Data
open Purelib.Data.Rat

/-- The rational scale combining truncation and input resampling error in the dynamic exponential-sum comparison. -/
@[expose] public def dynamicSumReindexDirectScale : Fraction.Rational := 2 * (10 + 16)

/-- The direct exponential-sum resampling error scale is nonnegative. -/
theorem dynamicSumReindexDirectScale_nonneg :
    0 ≤ dynamicSumReindexDirectScale :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))

/-- The sum of the dynamic-sum, progressive-exponential and direct-resampling error scales. -/
@[expose] public def dynamicSumReindexMasterScale : Fraction.Rational :=
  Sequence.dynamicExpSumErrorScale + Budget.errorScale +
    dynamicSumReindexDirectScale

/-- The combined exponential-sum comparison scale is nonnegative. -/
theorem dynamicSumReindexMasterScale_nonneg :
    0 ≤ dynamicSumReindexMasterScale :=
  add_nonneg
    (add_nonneg Sequence.dynamicExpSumErrorScale_nonneg
      Budget.errorScale_nonneg)
    dynamicSumReindexDirectScale_nonneg

/-- The combined comparison scale bounds the dynamic exponential-sum scale. -/
private theorem dynamicSumScale_le_reindexMaster :
    Sequence.dynamicExpSumErrorScale ≤
      dynamicSumReindexMasterScale := by
  unfold dynamicSumReindexMasterScale
  calc
    Sequence.dynamicExpSumErrorScale ≤
        Sequence.dynamicExpSumErrorScale +
          Budget.errorScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        Budget.errorScale_nonneg
    _ ≤ Sequence.dynamicExpSumErrorScale +
          Budget.errorScale +
            Approximation.Gaussian.Exponential.Progressive.Local.Addition.Reindex.dynamicSumReindexDirectScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        dynamicSumReindexDirectScale_nonneg

/-- The combined comparison scale bounds the progressive local-exponential scale. -/
private theorem progressiveExpScale_le_reindexMaster :
    Budget.errorScale ≤
      dynamicSumReindexMasterScale := by
  unfold dynamicSumReindexMasterScale
  calc
    Budget.errorScale ≤
      Sequence.dynamicExpSumErrorScale + Budget.errorScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_left _ _ Sequence.dynamicExpSumErrorScale_nonneg
    _ ≤ Sequence.dynamicExpSumErrorScale + Budget.errorScale +
          Approximation.Gaussian.Exponential.Progressive.Local.Addition.Reindex.dynamicSumReindexDirectScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        dynamicSumReindexDirectScale_nonneg

/-- The combined comparison scale bounds the direct resampling scale. -/
public theorem reindexDirectScale_le_master :
    dynamicSumReindexDirectScale ≤
      dynamicSumReindexMasterScale := by
  unfold dynamicSumReindexMasterScale
  calc
    dynamicSumReindexDirectScale ≤
        (Sequence.dynamicExpSumErrorScale +
          Budget.errorScale) +
            Approximation.Gaussian.Exponential.Progressive.Local.Addition.Reindex.dynamicSumReindexDirectScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_left _ _
        (add_nonneg Sequence.dynamicExpSumErrorScale_nonneg
          Budget.errorScale_nonneg)

/-- Finite resampling bridge from the canonical dynamic sum-Horner program to local exponential evaluation on the
productive sampled-sum input wrapper. -/
@[expose] public def dynamicExpSumReindexEquivalent (left right : Coherent.CoherentNamed)
    (sumDomain : UnitDisk
      (Named.add
        left.name right.name)) :
    Equivalent
      (Sequence.dynamicExpSumApproximation left.name right.name sumDomain)
      (Name.approximation
        (Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name).toNamed
        (Sequence.sampledSumUnitDisk left right sumDomain)) := by
  let source := Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name
  let wrapperDomain := Sequence.sampledSumUnitDisk left right sumDomain
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
          dynamicSumReindexMasterScale start
            smallTarget
        have startLeRight : start ≤ rightIndex :=
          Search.firstQuarterBelow_ge
            dynamicSumReindexMasterScale start
              smallTarget
        have masterSmall :
            Basic.quarterRadius
                dynamicSumReindexMasterScale
                  rightIndex < smallTarget :=
          Search.firstQuarterBelow_accurate
            dynamicSumReindexMasterScale
              dynamicSumReindexMasterScale_nonneg
                start smallTarget
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
          rw [Sequence.Arithmetic.Sum.sampledSumApproximation_sample]
          exact Sequence.dynamicInputSum_unit left.name right.name sumDomain leftIndex
        have rightInputUnit : Gaussian.Norm.Basic.normSq (source.sample sourceIndex) ≤ 1 := by
          rw [Sequence.Arithmetic.Sum.sampledSumApproximation_sample]
          exact Sequence.dynamicInputSum_unit left.name right.name sumDomain sourceIndex
        have truncation := Sample.sample_later_close
          (source.sample leftIndex) leftInputUnit rightLeLeft
        have inputEffect := Sample.sample_input_close
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
                    (source.sample leftIndex) leftIndex -
                  Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex) <
              Basic.quarterRadius

                  dynamicSumReindexDirectScale
                  rightIndex := by
          calc
            Gaussian.Norm.Basic.normSq
                (Horner.Sample.sample
                    (source.sample leftIndex) leftIndex -
                  Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex) ≤
              2 *
                (Gaussian.Norm.Basic.normSq
                    (Horner.Sample.sample
                        (source.sample leftIndex) leftIndex -
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

                  dynamicSumReindexDirectScale
                  rightIndex := by
              unfold
                dynamicSumReindexDirectScale
              rw [Basic.quarterRadius_eq_mul_pow,
                Process.Sampling.refinementTarget,
                Basic.quarterRadius_eq_mul_pow,
                Basic.quarterRadius_eq_mul_pow]
              ring1
        have directSmall :
            Gaussian.Norm.Basic.normSq
                (Horner.Sample.sample
                    (source.sample leftIndex) leftIndex -
                  Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex) < smallTarget :=
          direct.trans
            ((quarterRadius_scale_mono
              reindexDirectScale_le_master
              rightIndex).trans_lt masterSmall)
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := (Data.Nat.Order.le_max_left leftStart rightStart).trans
              (startLeRight.trans rightLeLeft)
            right_ge := (Data.Nat.Order.le_max_right leftStart rightStart).trans startLeRight
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have leftTail :=
                (Sequence.dynamicExpSumApproximation left.name right.name
                  sumDomain).later_close leftOrder
              have leftRadiusToMaster :
                  Basic.quarterRadius
                      Sequence.dynamicExpSumErrorScale leftIndex ≤
                    Basic.quarterRadius
                      dynamicSumReindexMasterScale
                        rightIndex :=
                (quarterRadius_scale_mono
                  dynamicSumScale_le_reindexMaster
                  leftIndex).trans
                    (quarterRadius_antitone

                        dynamicSumReindexMasterScale_nonneg
                        rightLeLeft)
              have leftTailSmall := leftTail.trans_lt
                (leftRadiusToMaster.trans_lt masterSmall)
              have rightTail := wrapperExp.later_close rightOrder
              have rightTailSmall := rightTail.trans_lt
                ((quarterRadius_scale_mono
                  progressiveExpScale_le_reindexMaster
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
                  (Sequence.dynamicExpSumApproximation left.name right.name
                    sumDomain).sample leftIndex =
                    Horner.Sample.sample
                      (source.sample leftIndex) leftIndex := by
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
                    ((Sequence.dynamicExpSumApproximation left.name right.name
                      sumDomain).sample leftLater -
                        wrapperExp.sample rightLater) ≤
                  2 *
                    (Gaussian.Norm.Basic.normSq
                        ((Sequence.dynamicExpSumApproximation left.name right.name
                            sumDomain).sample leftLater -
                          (Sequence.dynamicExpSumApproximation left.name right.name
                            sumDomain).sample leftIndex) +
                      Gaussian.Norm.Basic.normSq
                        ((Sequence.dynamicExpSumApproximation left.name right.name
                            sumDomain).sample leftIndex -
                          wrapperExp.sample rightLater)) :=
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

/-- Named form of the finite resampling bridge. -/
@[expose] public def dynamicExpSum_toSampledLocalExp (left right : Coherent.CoherentNamed)
    (sumDomain : UnitDisk
      (Named.add
        left.name right.name)) :
    NamedEquivalent
      (Sequence.dynamicExpSumApproximation left.name right.name sumDomain).toNamed
      (Name.named
        (Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name).toNamed
        (Sequence.sampledSumUnitDisk left right sumDomain)) :=
  Equivalence.approximationEquivalent_toNamed
    (dynamicExpSumReindexEquivalent left right
      sumDomain)
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Reindex

end
