module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Fraction
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Sequence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Reindex
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Sequence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sample
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Budget
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Sequence.UnitDisk
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

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential.Horner.Addition
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.CCL.Transcendental
open Purelib.Data.Rat

/-- The combined rational scale for dynamic exponential-product and sum errors and the direct finite addition estimate.
-/
@[expose] public def dynamicExpAdditionMasterScale : Fraction.Rational :=
  Sequence.dynamicExpProductErrorScale + Sequence.dynamicExpSumErrorScale + 16

/-- The combined dynamic exponential-addition scale is nonnegative. -/
theorem dynamicExpAdditionMasterScale_nonneg :
    0 ≤ Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale :=
  add_nonneg
    (add_nonneg Sequence.dynamicExpProductErrorScale_nonneg
      Sequence.dynamicExpSumErrorScale_nonneg)
    (by decide)

/-- The combined addition scale bounds the dynamic product error scale. -/
theorem dynamicExpProductErrorScale_le_master :
    Sequence.dynamicExpProductErrorScale ≤
      Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale := by
  unfold Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale
  calc
    Sequence.dynamicExpProductErrorScale ≤
        Sequence.dynamicExpProductErrorScale + Sequence.dynamicExpSumErrorScale :=
      le_add_of_nonneg_right Sequence.dynamicExpSumErrorScale_nonneg
    _ ≤ Sequence.dynamicExpProductErrorScale + Sequence.dynamicExpSumErrorScale + 16 :=
      le_add_of_nonneg_right (show (0 : Fraction.Rational) ≤ 16 by decide)

/-- The combined addition scale bounds the dynamic sum error scale. -/
theorem dynamicExpSumErrorScale_le_master :
    Sequence.dynamicExpSumErrorScale ≤
      Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale := by
  unfold Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale
  calc
    Sequence.dynamicExpSumErrorScale ≤
        Sequence.dynamicExpProductErrorScale + Sequence.dynamicExpSumErrorScale :=
      le_add_of_nonneg_left Sequence.dynamicExpProductErrorScale_nonneg
    _ ≤ Sequence.dynamicExpProductErrorScale + Sequence.dynamicExpSumErrorScale + 16 :=
      le_add_of_nonneg_right (show (0 : Fraction.Rational) ≤ 16 by decide)

/-- The combined dynamic addition scale bounds the direct finite addition-error coefficient sixteen. -/
theorem sixteen_le_dynamicExpAdditionMasterScale :
    (16 : Fraction.Rational) ≤
      Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale := by
  unfold Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale
  calc
    (16 : Fraction.Rational) ≤
        16 + (Sequence.dynamicExpProductErrorScale + Sequence.dynamicExpSumErrorScale) :=
      le_add_of_nonneg_right
        (add_nonneg Sequence.dynamicExpProductErrorScale_nonneg
          Sequence.dynamicExpSumErrorScale_nonneg)
    _ = Sequence.dynamicExpProductErrorScale + Sequence.dynamicExpSumErrorScale + 16 := by
      ring1

/-- Dynamic finite Horner addition law.

At one computed odd depth the exact finite polynomial estimate is instantiated with the displayed operand readings at
that depth; explicit tails absorb all later dynamic readings. -/
@[expose] public def dynamicLocalExp_add_equivalent {left right : Gaussian.Name.Basic.Named}
    (leftDomain : Name.UnitDisk left)
    (rightDomain : Name.UnitDisk right)
    (sumDomain : Name.UnitDisk
      (Named.add left right)) :
    Gaussian.Equivalence.Equivalent
      (Sequence.dynamicExpProductApproximation leftDomain rightDomain)
      (Sequence.dynamicExpSumApproximation left right sumDomain) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    let start := max leftStart rightStart
    let index := Search.firstQuarterBelow
      Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale start smallTarget
    let synchronized := 2 * index + 1
    have indexGe : start ≤ index :=
      Search.firstQuarterBelow_ge
        Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale start
          smallTarget
    have synchronizedGeIndex : index ≤ synchronized := by
      dsimp only [synchronized]
      omega
    have masterSmall :
        Geometric.Basic.quarterRadius
            Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale index <
              smallTarget :=
      Search.firstQuarterBelow_accurate
        Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale
          Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale_nonneg
          start smallTarget smallPositive
    exact
      { leftIndex := synchronized
        rightIndex := synchronized
        left_ge := (Purelib.Data.Nat.Order.le_max_left _ _).trans
          (indexGe.trans synchronizedGeIndex)
        right_ge := (Purelib.Data.Nat.Order.le_max_right _ _).trans
          (indexGe.trans synchronizedGeIndex)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have masterAtSynchronized :
              Geometric.Basic.quarterRadius
                  Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale
                    synchronized ≤
                Geometric.Basic.quarterRadius
                  Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale index
                    :=
            quarterRadius_antitone
              Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpAdditionMasterScale_nonneg
                synchronizedGeIndex
          have productTail :
              Data.Gaussian.Norm.Basic.normSq
                  ((Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                      leftLater -
                    (Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                      synchronized) < smallTarget :=
            by
              have movement :=
                (Sequence.dynamicExpProductApproximation leftDomain rightDomain).later_close
                  leftOrder
              change Data.Gaussian.Norm.Basic.normSq
                  ((Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                      leftLater -
                    (Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                      synchronized) ≤
                Geometric.Basic.quarterRadius
                  Sequence.dynamicExpProductErrorScale synchronized at movement
              exact movement.trans_lt
                ((quarterRadius_scale_mono

                      dynamicExpProductErrorScale_le_master
                      synchronized).trans_lt
                  (masterAtSynchronized.trans_lt masterSmall))
          have sumTailForward :
              Data.Gaussian.Norm.Basic.normSq
                  ((Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      rightLater -
                    (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      synchronized) < smallTarget :=
            by
              have movement :=
                (Sequence.dynamicExpSumApproximation left right sumDomain).later_close
                  rightOrder
              change Data.Gaussian.Norm.Basic.normSq
                  ((Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      rightLater -
                    (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      synchronized) ≤
                Geometric.Basic.quarterRadius
                  Sequence.dynamicExpSumErrorScale synchronized at movement
              exact movement.trans_lt
                ((quarterRadius_scale_mono
                    Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicExpSumErrorScale_le_master
                      synchronized).trans_lt
                  (masterAtSynchronized.trans_lt masterSmall))
          have sumTailReverse :
              Data.Gaussian.Norm.Basic.normSq
                  ((Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      synchronized -
                    (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      rightLater) < smallTarget := by
            have reverseIdentity :
                (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      synchronized -
                    (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      rightLater =
                  -((Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      rightLater -
                    (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      synchronized) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                  Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
            rw [reverseIdentity, Data.Gaussian.Norm.Basic.normSq_neg]
            exact sumTailForward
          have directLe :=
            Sequence.expProductSample_addition_error_odd
              (Sampling.inputSample_unit
                leftDomain synchronized)
              (Sampling.inputSample_unit
                rightDomain synchronized)
              index
          have direct :
              Data.Gaussian.Norm.Basic.normSq
                  ((Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                      synchronized -
                    (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      synchronized) < smallTarget := by
            have directBound :
                Data.Gaussian.Norm.Basic.normSq
                    ((Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                        synchronized -
                      (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                        synchronized) ≤
                  Geometric.Basic.quarterRadius 16 index := by
              simpa only
                [Sequence.dynamicExpProductApproximation_sample,

                  Sequence.dynamicExpSumApproximation_sample,
                Name.approximation,
                Name.domainSample,
                Sample.sampleFrom,
                Sampling.unitDiskSamples,
                Sequence.expProductSample,
                Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Sequence.dynamicInputSum] using
                  directLe
            exact directBound.trans_lt
              ((quarterRadius_scale_mono

                    sixteen_le_dynamicExpAdditionMasterScale
                    index).trans_lt
                masterSmall)
          have middle :
              Data.Gaussian.Norm.Basic.normSq
                  ((Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                      synchronized -
                    (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                      rightLater) <
                2 * (smallTarget + smallTarget) :=
            (Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans_lt
              (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  direct sumTailReverse))
          calc
            Data.Gaussian.Norm.Basic.normSq
                ((Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                    leftLater -
                  (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                    rightLater) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    ((Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                        leftLater -
                      (Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                        synchronized) +
                  Data.Gaussian.Norm.Basic.normSq
                    ((Sequence.dynamicExpProductApproximation leftDomain rightDomain).sample
                        synchronized -
                      (Sequence.dynamicExpSumApproximation left right sumDomain).sample
                        rightLater)) :=
              Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
            _ < 2 *
                (smallTarget + 2 * (smallTarget + smallTarget)) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  productTail middle)
            _ = 10 * smallTarget := by ring1
            _ < target := by
              dsimp only [smallTarget]
              exact Purelib.Data.Rat.Bounds.Fraction.ten_sixteenths_lt positive }

/-- CCL-name form of the dynamic finite Horner addition law. -/
@[expose] public def dynamicLocalExp_add_named_equivalent {left right : Gaussian.Name.Basic.Named}
    (leftDomain : Name.UnitDisk left)
    (rightDomain : Name.UnitDisk right)
    (sumDomain : Name.UnitDisk
      (Named.add left right)) :
    Gaussian.Equivalence.NamedEquivalent
      (Sequence.dynamicExpProductApproximation leftDomain rightDomain).toNamed
      (Sequence.dynamicExpSumApproximation left right sumDomain).toNamed :=
  Equivalence.approximationEquivalent_toNamed
    (Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicLocalExp_add_equivalent leftDomain
      rightDomain sumDomain)

/-- The actual multiplication tree of the two arbitrary local exponential outputs reaches the canonical dynamic
sum-Horner name. -/
@[expose] public def localExpMul_toDynamicSum {left right : Gaussian.Name.Basic.Named}
    (leftDomain : Name.UnitDisk left)
    (rightDomain : Name.UnitDisk right)
    (sumDomain : Name.UnitDisk
      (Named.add left right)) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Name.named left leftDomain)
        (Name.named right rightDomain))
      (Sequence.dynamicExpSumApproximation left right sumDomain).toNamed :=
  NamedEquivalent.trans
    (Sequence.localExpMul_toDynamic leftDomain rightDomain)
    (Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.dynamicLocalExp_add_named_equivalent
      leftDomain rightDomain sumDomain)

/-- The local exponential addition law for arbitrary coherent productive CCL inputs.

All three unit-disk hypotheses concern possible finite readings; the conclusion compares the actual multiplication,
addition, and local exponential processes rather than idealized pointwise streams. -/
@[expose] public def coherentLocalExp_add_named_equivalent (left right : Coherent.CoherentNamed)
    (leftDomain : Name.UnitDisk left.name)
    (rightDomain : Name.UnitDisk right.name)
    (sumDomain : Name.UnitDisk
      (Named.add
        left.name right.name)) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Name.named left.name leftDomain)
        (Name.named right.name rightDomain))
      (Name.named
        (Named.add
          left.name right.name) sumDomain) :=
  NamedEquivalent.trans
    (Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law.localExpMul_toDynamicSum leftDomain rightDomain
      sumDomain)
    (NamedEquivalent.trans
      (Reindex.dynamicExpSum_toSampledLocalExp left right sumDomain)
      (NamedEquivalent.symm
        (Sequence.localExp_sum_toSampled left right sumDomain)))
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law

end
