module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Budget
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Congruence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

section
public section

/-! Approximation Gaussian Exponential Progressive Local Addition Sequence and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Sequence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Sampling
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

/-- A unit-disk certificate for an actual coherent sum transfers to the canonical equal-index sampled-sum wrapper.

Every possible wrapper value is one explicitly witnessed later sum of possible operand readings. -/
theorem sampledSumUnitDisk (left right : Coherent.CoherentNamed)
    (sumDomain : UnitDisk
      (Named.add
        left.name right.name)) :
    UnitDisk
      (Arithmetic.Sum.sampledSumApproximation left.name right.name).toNamed where
  possible_unit := by
    intro value possible
    change (Arithmetic.Sum.sampledSumApproximation left.name right.name).Possible 0 value at possible
    rcases possible with ⟨later, _order, rfl⟩
    rw [Arithmetic.Sum.sampledSumApproximation_sample]
    apply sumDomain.possible_unit
    exact
      ⟨(Sampling.approximation left.name).sample
          later,
        (Sampling.approximation right.name).sample
          later,
        Process.Sampling.witnessAt_possible_start
          left.name.process left.name.state later,
        Process.Sampling.witnessAt_possible_start
          right.name.process right.name.state later,
        rfl⟩

/-- Local exponential evaluation on an actual coherent sum may be replaced by evaluation on its canonical sampled-sum
wrapper. -/
@[expose] public def localExp_sum_toSampled (left right : Coherent.CoherentNamed)
    (sumDomain : UnitDisk
      (Named.add
        left.name right.name)) :
    NamedEquivalent
      (Name.named
        (Named.add
          left.name right.name) sumDomain)
      (Name.named
        (Arithmetic.Sum.sampledSumApproximation left.name right.name).toNamed
        (sampledSumUnitDisk left right
          sumDomain)) :=
  Congruence.localExpNamed_respects sumDomain
    (sampledSumUnitDisk left right sumDomain)
    (Bridge.coherentAdd_toNamed left right)

/-- The geometric squared-error scale for the product of the two dynamic local exponential samplers. -/
@[expose] public def dynamicExpProductErrorScale : Fraction.Rational :=
  40 * Budget.errorScale

/-- The dynamic exponential product error scale is nonnegative. -/
theorem dynamicExpProductErrorScale_nonneg :
    0 ≤ dynamicExpProductErrorScale :=
  Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 40) (by decide)).le
    Budget.errorScale_nonneg

/-- Pointwise product of the two dynamic local Horner programs. -/
@[expose] public def dynamicExpProductApproximation {left right : Named}
    (leftDomain : UnitDisk left)
    (rightDomain : UnitDisk right) :
    ApproximationData where
  sample index :=
    (Name.approximation left leftDomain).sample index *
      (Name.approximation right rightDomain).sample
        index
  radiusSq := Basic.quarterRadius
    dynamicExpProductErrorScale
  radiusSq_nonneg :=
    Basic.quarterRadius_nonneg
      dynamicExpProductErrorScale_nonneg
  later_close := by
    intro earlier later order
    let leftSource :=
      Name.approximation left leftDomain
    let rightSource :=
      Name.approximation right rightDomain
    have leftMovement := leftSource.later_close order
    have rightMovement := rightSource.later_close order
    have firstTerm :
        Basic.normSq
            ((leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later) ≤
          Basic.quarterRadius
              Budget.errorScale earlier * 10 := by
      rw [Basic.normSq_mul]
      exact Arithmetic.mul_le_mul_direct leftMovement
        (rightSource.sample_bounded later) (Basic.normSq_nonneg _)
        (Basic.quarterRadius_nonneg
          Budget.errorScale_nonneg _)
    have secondTerm :
        Basic.normSq
            (leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
          10 * Basic.quarterRadius
            Budget.errorScale earlier := by
      rw [Basic.normSq_mul]
      exact Arithmetic.mul_le_mul_direct
        (leftSource.sample_bounded earlier) rightMovement (Basic.normSq_nonneg _)
        (by decide)
    have identity :
        leftSource.sample later * rightSource.sample later -
            leftSource.sample earlier * rightSource.sample earlier =
          (leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later +
            leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
          Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re,
          Data.Gaussian.Basic.mul_im] <;> ring1
    change Basic.normSq
        (leftSource.sample later * rightSource.sample later -
          leftSource.sample earlier * rightSource.sample earlier) ≤
      Basic.quarterRadius
        dynamicExpProductErrorScale
          earlier
    rw [identity]
    calc
      Basic.normSq
          ((leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later +
            leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (Basic.normSq
              ((leftSource.sample later - leftSource.sample earlier) *
                rightSource.sample later) +
            Basic.normSq
              (leftSource.sample earlier *
                (rightSource.sample later - rightSource.sample earlier))) :=
        Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (Basic.quarterRadius
                Budget.errorScale earlier * 10 +
            10 * Basic.quarterRadius
              Budget.errorScale earlier) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = Basic.quarterRadius
          dynamicExpProductErrorScale
            earlier := by
        rw [Basic.quarterRadius_eq_mul_pow,
          Basic.quarterRadius_eq_mul_pow]
        unfold
          dynamicExpProductErrorScale
        ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow
      dynamicExpProductErrorScale current
        target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      dynamicExpProductErrorScale current
        target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate
      dynamicExpProductErrorScale
        dynamicExpProductErrorScale_nonneg
  centerBound := 10 * 10
  centerBound_nonneg :=
    Arithmetic.mul_nonneg_direct (by decide) (by decide)
  sample_bounded := by
    intro index
    rw [Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      ((Name.approximation left leftDomain).sample_bounded
        index)
      ((Name.approximation right rightDomain).sample_bounded
        index)
      (Basic.normSq_nonneg _) (by decide)

/-- A sample of the dynamic exponential product is the product of the two original local exponential samples at the same
index. -/
@[simp] theorem dynamicExpProductApproximation_sample
    {left right : Named}
    (leftDomain : UnitDisk left)
    (rightDomain : UnitDisk right)
    (index : Nat) :
    (dynamicExpProductApproximation leftDomain
      rightDomain).sample index =
      (Name.approximation left leftDomain).sample
          index *
        (Name.approximation right rightDomain).sample
          index :=
  rfl

/-- Actual multiplication of the two local progressive exponential names is operationally their dynamic pointwise Horner
product. -/
@[expose] public def localExpMul_toDynamic {left right : Named}
    (leftDomain : UnitDisk left)
    (rightDomain : UnitDisk right) :
    NamedEquivalent
      (Named.mul
        (Name.named left leftDomain)
        (Name.named right rightDomain))
      (dynamicExpProductApproximation leftDomain
        rightDomain).toNamed :=
  Bridge.mulToNamed_equivalent_pointwise
    (Name.approximation left leftDomain)
    (Name.approximation right rightDomain)
    (dynamicExpProductApproximation leftDomain
      rightDomain)
    (by intro index; rfl)

/-- Add the two original finite input readings at a shared index. -/
@[expose] public def dynamicInputSum (left right : Named) (index : Nat) :
  Data.Gaussian.Basic.Canonical :=
  Exp.inputSample left index +
    Exp.inputSample right index

/-- A unit-disk certificate for the actual sum contains each equal-index dynamic input sum. -/
theorem dynamicInputSum_unit (left right : Named)
    (sumDomain : UnitDisk
      (Named.add left right))
    (index : Nat) : Basic.normSq
      (dynamicInputSum left right index) ≤ 1 :=
      by
  apply sumDomain.possible_unit
  exact
    ⟨Exp.inputSample left index,
      Exp.inputSample right index,
      Exp.inputSample_possible_start left index,
      Exp.inputSample_possible_start right index,
      rfl⟩

/-- Later equal-index input sums remain within the scale-sixteen geometric squared-error radius at the earlier index. -/
theorem dynamicInputSum_later_close (left right : Named)
    {earlier later : Nat} (order : earlier ≤ later) :
    Basic.normSq
        (dynamicInputSum left right later -
          dynamicInputSum left right earlier) ≤
      Basic.quarterRadius 16 earlier := by
  have leftMovement :=
    Process.Sampling.witnessAt_later_close
      left.process left.state order
  have rightMovement :=
    Process.Sampling.witnessAt_later_close
      right.process right.state order
  have identity :
      dynamicInputSum left right later -
        dynamicInputSum left right earlier =
        (Exp.inputSample left later -
          Exp.inputSample left earlier) +
        (Exp.inputSample right later -
          Exp.inputSample right earlier) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [dynamicInputSum,
        Exp.inputSample,
        Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im]
          <;> ring1
  rw [identity]
  calc
    Basic.normSq
        ((Exp.inputSample left later -
            Exp.inputSample left earlier) +
          (Exp.inputSample right later -
            Exp.inputSample right earlier)) ≤
      2 *
        (Basic.normSq
            (Exp.inputSample left later -
              Exp.inputSample left earlier) +
          Basic.normSq
            (Exp.inputSample right later -
              Exp.inputSample right earlier)) :=
      Bounds.normSq_add_le_two _ _
    _ ≤ 2 *
        (Basic.quarterRadius 4 earlier +
          Basic.quarterRadius 4 earlier) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftMovement rightMovement) (by decide)
    _ = Basic.quarterRadius 16 earlier := by
      rw [Basic.quarterRadius_eq_mul_pow,
        Basic.quarterRadius_eq_mul_pow]
      ring1

/-- The rational error scale combining exponential truncation with sensitivity to the dynamic input sum. -/
@[expose] public def dynamicExpSumErrorScale : Fraction.Rational := 2 * (10 + 16 * 16)

/-- The dynamic exponential sum error scale is nonnegative. -/
theorem dynamicExpSumErrorScale_nonneg : 0 ≤
  dynamicExpSumErrorScale :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide)
      (Arithmetic.mul_nonneg_direct (by decide) (by decide)))

/-- Dynamic local Horner program evaluated at the explicit equal-index sums of the two operand readings. -/
@[expose] public def dynamicExpSumApproximation (left right : Named)
    (sumDomain : UnitDisk
      (Named.add left right)) :
    ApproximationData where
  sample index := Horner.Sample.sample
    (dynamicInputSum left right index) index
  radiusSq := Basic.quarterRadius
    dynamicExpSumErrorScale
  radiusSq_nonneg :=
    Basic.quarterRadius_nonneg
      dynamicExpSumErrorScale_nonneg
  later_close := by
    intro earlier later order
    let earlierInput := dynamicInputSum left
      right earlier
    let laterInput := dynamicInputSum left right
      later
    have earlierUnit := dynamicInputSum_unit left
      right sumDomain earlier
    have laterUnit := dynamicInputSum_unit left
      right sumDomain later
    have truncation := Sample.sample_later_close
      laterInput laterUnit order
    have inputMovement :=
      dynamicInputSum_later_close left right
      order
    have inputEffect := Sample.sample_input_close
      laterInput earlierInput laterUnit earlierUnit earlier
    change Basic.normSq
        (Horner.Sample.sample laterInput later -
          Horner.Sample.sample earlierInput earlier) ≤
      Basic.quarterRadius
        dynamicExpSumErrorScale earlier
    calc
      Basic.normSq
          (Horner.Sample.sample laterInput later -
            Horner.Sample.sample earlierInput earlier) ≤
        2 *
          (Basic.normSq
              (Horner.Sample.sample laterInput later -
                Horner.Sample.sample laterInput earlier) +
            Basic.normSq
              (Horner.Sample.sample laterInput earlier -
                Horner.Sample.sample earlierInput earlier)) :=
        Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 *
          (Basic.quarterRadius 10 earlier +
            16 * Basic.quarterRadius 16 earlier) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add truncation
            (inputEffect.trans
              (Arithmetic.mul_le_mul_of_nonneg_left_direct
                inputMovement (by decide))))
          (by decide)
      _ = Basic.quarterRadius
          dynamicExpSumErrorScale earlier
            := by
        rw [Basic.quarterRadius_eq_mul_pow,
          Basic.quarterRadius_eq_mul_pow,
          Basic.quarterRadius_eq_mul_pow]
        unfold dynamicExpSumErrorScale
        ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow
      dynamicExpSumErrorScale current
        target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      dynamicExpSumErrorScale current
        target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate
      dynamicExpSumErrorScale
        dynamicExpSumErrorScale_nonneg
  centerBound := 10
  centerBound_nonneg := by decide
  sample_bounded := by
    intro index
    exact Sample.sample_bounded _
      (dynamicInputSum_unit left right sumDomain
        index) index

/-- Sampling the dynamic exponential sum evaluates the finite exponential at the same-index input sum and depth. -/
@[simp] theorem dynamicExpSumApproximation_sample
    (left right : Named)
    (sumDomain : UnitDisk
      (Named.add left right))
    (index : Nat) :
    (dynamicExpSumApproximation left right
      sumDomain).sample index =
      Horner.Sample.sample
        (dynamicInputSum left right index) index
          :=
  rfl
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Sequence

end
