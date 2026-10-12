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
    0 ≤ Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))

/-- The combined scale for diagonal movement, progressive exponential movement and direct resampling error. -/
@[expose] public def dynamicLocalExpLogReindexMasterScale : Fraction.Rational :=
  Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale +
    Exponential.Progressive.Local.Budget.errorScale +
      Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale

/-- The combined exponential–logarithm resampling scale is nonnegative. -/
theorem dynamicLocalExpLogReindexMasterScale_nonneg :
    0 ≤ Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale :=
  add_nonneg
    (add_nonneg Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale_nonneg
      Exponential.Progressive.Local.Budget.errorScale_nonneg)
    Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale_nonneg

/-- The combined resampling scale bounds the diagonal exponential–logarithm error scale. -/
private theorem dynamicLocalExpLogScale_le_reindexMaster :
    Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale ≤
      Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale
        := by
  unfold Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale
  calc
    Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale ≤
        Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale +
          Exponential.Progressive.Local.Budget.errorScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        Exponential.Progressive.Local.Budget.errorScale_nonneg
    _ ≤ Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale +
          Exponential.Progressive.Local.Budget.errorScale +
            Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale_nonneg

/-- The combined resampling scale bounds the progressive local-exponential error scale. -/
private theorem progressiveExpScale_le_dynamicLocalExpLogReindexMaster :
    Exponential.Progressive.Local.Budget.errorScale ≤
      Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale
        := by
  unfold Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale
  calc
    Exponential.Progressive.Local.Budget.errorScale ≤
        Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale +
          Exponential.Progressive.Local.Budget.errorScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_left _ _
        Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale_nonneg
    _ ≤ Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale +
          Exponential.Progressive.Local.Budget.errorScale +
            Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale_nonneg

/-- The combined resampling scale bounds the direct comparison error scale. -/
public theorem dynamicLocalExpLogReindexDirectScale_le_master :
    Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale ≤
      Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale
        := by
  unfold Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale
  exact Fraction.Compatibility.coordinate_le_add_of_nonneg_left _ _
    (add_nonneg Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale_nonneg
      Exponential.Progressive.Local.Budget.errorScale_nonneg)

/-- Finite resampling bridge between the diagonal `exp_(2n+1)(log_n(z_n))` program and the productive local exponential
reading the progressive local logarithm at its own requested source indices. -/
@[expose] public def dynamicLocalExpLogReindexEquivalent (input : Gaussian.Name.Basic.Named)
    (disk : Logarithm.Complex.Progressive.Local.Domain.Disk input) :
    Gaussian.Equivalence.Equivalent
      (Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogApproximation input disk)
      (Exponential.Progressive.Local.Name.approximation
        (Logarithm.Complex.Progressive.Local.Name.named input disk)
        (Logarithm.Complex.Progressive.Inverse.Domain.localComplexLogUnitDisk input disk)) := by
  let source :=
    Logarithm.Complex.Progressive.Local.Name.approximation input disk
  let wrapperDomain := Logarithm.Complex.Progressive.Inverse.Domain.localComplexLogUnitDisk input disk
  let wrapperExp := Exponential.Progressive.Local.Name.approximation
    source.toNamed wrapperDomain
  exact
    { compare := by
        intro leftStart rightStart target positive
        let smallTarget := target / 16
        have smallPositive : 0 < smallTarget :=
          Fraction.Order.Field.div_pos_direct positive (by decide)
        let start := max leftStart rightStart
        let rightIndex := Search.firstQuarterBelow
          Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale start smallTarget
        have startLeRight : start ≤ rightIndex :=
          Search.firstQuarterBelow_ge
            Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale start smallTarget
        have masterSmall :
            Geometric.Basic.quarterRadius
                Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale rightIndex <
                  smallTarget :=
          Search.firstQuarterBelow_accurate
            Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale
              Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale_nonneg start
                smallTarget
                smallPositive
        let sourceIndex :=
          Sampling.emittedSampleIndex
            source rightIndex
        let leftIndex := max rightIndex sourceIndex
        have rightLeLeft : rightIndex ≤ leftIndex := Purelib.Data.Nat.Order.le_max_left _ _
        have sourceLeLeft : sourceIndex ≤ leftIndex := Purelib.Data.Nat.Order.le_max_right _ _
        have sourceRadiusSmall :
            source.radiusSq sourceIndex <
              Gaussian.Process.Sampling.refinementTarget rightIndex :=
          Gaussian.Process.Sampling.stateAt_accurate
            source.toProcess (show source.toProcess.State from (0 : Nat))
              rightIndex
        have sourceMovement := source.later_close sourceLeLeft
        have inputMovement :
            Data.Gaussian.Norm.Basic.normSq (source.sample leftIndex - source.sample sourceIndex) <
              Gaussian.Process.Sampling.refinementTarget rightIndex :=
          sourceMovement.trans_lt sourceRadiusSmall
        have leftInputUnit : Data.Gaussian.Norm.Basic.normSq (source.sample leftIndex) ≤ 1 := by
          exact Logarithm.Local.Horner.Sample.sample_bounded_one
            (Logarithm.Complex.Progressive.Local.Sampling.inputSample_bound
              disk leftIndex) leftIndex
        have rightInputUnit : Data.Gaussian.Norm.Basic.normSq (source.sample sourceIndex) ≤ 1 := by
          exact Logarithm.Local.Horner.Sample.sample_bounded_one
            (Logarithm.Complex.Progressive.Local.Sampling.inputSample_bound
              disk sourceIndex) sourceIndex
        have depthOrder : rightIndex ≤ 2 * leftIndex + 1 := by
          have doubled : 2 * leftIndex = leftIndex + leftIndex := by
            rewrite [Purelib.Data.Nat.Multiplication.right_distrib 1 1 leftIndex,
              Nat.one_mul]
            exact Eq.refl _
          rewrite [doubled]
          exact Nat.le_trans rightLeLeft
            (Nat.le_trans (Nat.le_add_right leftIndex leftIndex) (Nat.le_succ _))
        have truncation := Exponential.Horner.Sample.sample_later_close
          (source.sample leftIndex) leftInputUnit depthOrder
        have inputEffect := Exponential.Horner.Sample.sample_input_close
          (source.sample leftIndex) (source.sample sourceIndex)
            leftInputUnit rightInputUnit rightIndex
        have inputStrict :
            Data.Gaussian.Norm.Basic.normSq
                (Exponential.Horner.Sample.sample
                    (source.sample leftIndex) rightIndex -
                  Exponential.Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex) <
              16 * Gaussian.Process.Sampling.refinementTarget
                rightIndex :=
          inputEffect.trans_lt
            (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              (by decide) inputMovement)
        have direct :
            Data.Gaussian.Norm.Basic.normSq
                (Exponential.Horner.Sample.sample
                    (source.sample leftIndex) (2 * leftIndex + 1) -
                  Exponential.Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex) <
              Geometric.Basic.quarterRadius

                  dynamicLocalExpLogReindexDirectScale
                  rightIndex := by
          calc
            Data.Gaussian.Norm.Basic.normSq
                (Exponential.Horner.Sample.sample
                    (source.sample leftIndex) (2 * leftIndex + 1) -
                  Exponential.Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    (Exponential.Horner.Sample.sample
                        (source.sample leftIndex) (2 * leftIndex + 1) -
                      Exponential.Horner.Sample.sample
                        (source.sample leftIndex) rightIndex) +
                  Data.Gaussian.Norm.Basic.normSq
                    (Exponential.Horner.Sample.sample
                        (source.sample leftIndex) rightIndex -
                      Exponential.Horner.Sample.sample
                        (source.sample sourceIndex) rightIndex)) :=
              Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
            _ < 2 *
                (Geometric.Basic.quarterRadius 10 rightIndex +
                  16 * Gaussian.Process.Sampling.refinementTarget
                    rightIndex) :=
              Purelib.Data.Rat.Bounds.Sum.twice_add_lt_twice_add_of_le_of_lt truncation inputStrict
            _ = Geometric.Basic.quarterRadius

                  dynamicLocalExpLogReindexDirectScale
                  rightIndex := by
              unfold
                dynamicLocalExpLogReindexDirectScale
              rw [Geometric.Basic.quarterRadius_eq_mul_pow,
                Gaussian.Process.Sampling.refinementTarget,
                Geometric.Basic.quarterRadius_eq_mul_pow,
                Geometric.Basic.quarterRadius_eq_mul_pow]
              ring1
        have directSmall := direct.trans
          ((quarterRadius_scale_mono
              Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexDirectScale_le_master
                rightIndex).trans_lt
            masterSmall)
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := (Purelib.Data.Nat.Order.le_max_left leftStart rightStart).trans
              (startLeRight.trans rightLeLeft)
            right_ge := (Purelib.Data.Nat.Order.le_max_right leftStart rightStart).trans startLeRight
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have leftTail :=
                (Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogApproximation input disk).later_close
                  leftOrder
              have leftRadiusToMaster :
                  Geometric.Basic.quarterRadius
                      Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale leftIndex ≤
                    Geometric.Basic.quarterRadius
                      Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale rightIndex :=
                (quarterRadius_scale_mono
                    Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogScale_le_reindexMaster
                      leftIndex).trans
                  (quarterRadius_antitone
                    Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexMasterScale_nonneg
                      rightLeLeft)
              have leftTailSmall := leftTail.trans_lt
                (leftRadiusToMaster.trans_lt masterSmall)
              have rightTail := wrapperExp.later_close rightOrder
              have rightTailSmall := rightTail.trans_lt
                ((quarterRadius_scale_mono
                    Logarithm.Complex.Progressive.Inverse.Reindex.progressiveExpScale_le_dynamicLocalExpLogReindexMaster
                    rightIndex).trans_lt masterSmall)
              have rightTailReverse :
                  Data.Gaussian.Norm.Basic.normSq
                      (wrapperExp.sample rightIndex -
                        wrapperExp.sample rightLater) < smallTarget := by
                have identity : wrapperExp.sample rightIndex -
                      wrapperExp.sample rightLater =
                    -(wrapperExp.sample rightLater -
                      wrapperExp.sample rightIndex) := by
                  apply Data.Gaussian.Basic.ext <;>
                    simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                      Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
                rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
                exact rightTailSmall
              have baseIdentity :
                  (Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogApproximation input disk).sample
                      leftIndex =
                    Exponential.Horner.Sample.sample
                      (source.sample leftIndex) (2 * leftIndex + 1) := by
                rfl
              have wrapperIdentity : wrapperExp.sample rightIndex =
                  Exponential.Horner.Sample.sample
                    (source.sample sourceIndex) rightIndex := rfl
              rw [← baseIdentity, ← wrapperIdentity] at directSmall
              have middle := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans_lt
                (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                  (by decide)
                  (Fraction.Order.Arithmetic.add_lt_add_direct
                    directSmall rightTailReverse))
              calc
                Data.Gaussian.Norm.Basic.normSq
                    ((Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogApproximation input disk).sample
                        leftLater - wrapperExp.sample rightLater) ≤
                  2 *
                    (Data.Gaussian.Norm.Basic.normSq
                        ((Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogApproximation input
                          disk).sample
                            leftLater -
                          (Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogApproximation input
                            disk).sample
                            leftIndex) +
                      Data.Gaussian.Norm.Basic.normSq
                        ((Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogApproximation input
                          disk).sample
                            leftIndex - wrapperExp.sample rightLater)) :=
                  Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
                _ < 2 *
                    (smallTarget + 2 * (smallTarget + smallTarget)) :=
                  Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                    (by decide)
                    (Fraction.Order.Arithmetic.add_lt_add_direct
                      leftTailSmall middle)
                _ = 10 * smallTarget := by ring1
                _ < target := by
                  dsimp only [smallTarget]
                  exact Purelib.Data.Rat.Bounds.Fraction.ten_sixteenths_lt positive } }

/-- Name-level form of the finite resampling bridge for local exp-log. -/
@[expose] public def dynamicLocalExpLog_toLocalExp (input : Gaussian.Name.Basic.Named)
    (disk : Logarithm.Complex.Progressive.Local.Domain.Disk input) :
    Gaussian.Equivalence.NamedEquivalent
      (Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogApproximation input disk).toNamed
      (Exponential.Progressive.Local.Name.named
        (Logarithm.Complex.Progressive.Local.Name.named input disk)
        (Logarithm.Complex.Progressive.Inverse.Domain.localComplexLogUnitDisk input disk)) :=
  Equivalence.approximationEquivalent_toNamed
    (Logarithm.Complex.Progressive.Inverse.Reindex.dynamicLocalExpLogReindexEquivalent input disk)
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reindex

end
