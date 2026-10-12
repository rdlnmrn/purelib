module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Matrix
import Purelib.Approximation.Rational.Budget.Quotient
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate
import Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Quotient
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Purelib.Riemann.Periods.PeriodMatrix
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Table.Basic
import Purelib.Approximation.Gaussian.Table.Request
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Operational realization of synchronized period normalization

The persistent normalized period entries use stateful CCL arithmetic, while
the finite energy argument uses one equal-index Gaussian-rational calculation
of `A⁻¹B`.  This module connects those two presentations without introducing
a completed matrix.  Its basic tool is an equal-index geometric quotient with
an explicit positive lower bound on every displayed denominator sample.
-/

namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Division
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Integration.Energy
open Purelib.Curves.Hyperelliptic.Periods.Matrix
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Gaussian
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Inverse
open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PeriodMatrix
open Purelib.LinearAlgebra.Gaussian.QuadraticForm
open Purelib.Riemann.Periods.PeriodMatrix.ScaledInverseCertificate

/-- Exact rational error bounds and comparison targets. -/
abbrev Coordinate := Fraction.Rational
/-- Exact Gaussian rational samples and matrix entries. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- A retained Gaussian sample sequence with finite quantitative approximation data. -/
abbrev Approximation := Gaussian.Sequence.ApproximationData
/-- Operational equivalence of the two retained Gaussian approximation sequences. -/
abbrev Equivalent := Gaussian.Equivalence.Equivalent
/-- Operational equivalence of the retained named Gaussian quantities. -/
abbrev NamedEquivalent := Gaussian.Equivalence.NamedEquivalent
/-- A Gaussian name retaining its coherent sample realization. -/
abbrev CoherentNamed := Coherent.CoherentNamed
/-- A Gaussian sample sequence with retained geometric convergence bounds. -/
abbrev GeometricApproximation :=
  Gaussian.Geometric.GeometricApproximation

open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- A positive rational lower bound for every displayed sample of one geometric approximation.

It is weaker than whole-ball apartness and is exactly what equal-index finite division requires. -/
structure SampleLower (source :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation) where
  /-- The retained uniform squared-norm lower bound for the original denominator samples. -/ lowerSq :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate
  /-- The retained denominator lower bound is strictly positive. -/ positive : 0 < lowerSq
  /-- Every original denominator sample satisfies the retained uniform squared-norm lower bound. -/ sample_lower :
    forall index, lowerSq <= Data.Gaussian.Norm.Basic.normSq (source.sample index)

constructive_injectivity SampleLower

namespace SampleLower

/-- The positive uniform squared-norm lower bound makes every original denominator sample nonzero. -/
theorem sample_nonzero {source :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation}
    (lower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower source) (index : Nat) :
      source.sample index ≠ 0 := by
  intro zero
  have positive := lower.positive.trans_le (lower.sample_lower index)
  rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at positive
  exact (lt_irrefl _ positive).elim

end SampleLower

/-- Geometric error scale for an equal-index quotient of arbitrary geometric sources. -/
@[expose] def quotientErrorScale (numerator denominator :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    (lower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower denominator) : Coordinate
      :=
  (2 * (numerator.errorScale * denominator.centerBound +
    numerator.centerBound * denominator.errorScale)) /
      (lower.lowerSq * lower.lowerSq)

/-- The retained quotient error scale is nonnegative. -/
theorem quotientErrorScale_nonnegative
    (numerator denominator :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    (lower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower denominator) :
    0 <= Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientErrorScale numerator
      denominator lower := by
  unfold Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientErrorScale
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          numerator.errorScale_nonneg denominator.centerBound_nonneg)
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          numerator.centerBound_nonneg denominator.errorScale_nonneg)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct lower.positive.le
      lower.positive.le)

/-- Equal-index finite quotients of geometric Gaussian-rational samples. -/
@[expose] def quotientApproximation (numerator denominator :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    (lower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower denominator) :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation where
  sample index := numerator.sample index / denominator.sample index
  errorScale := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientErrorScale numerator
    denominator lower
  errorScale_nonneg :=
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientErrorScale_nonnegative numerator
    denominator lower
  later_close := by
    intro earlier later order
    have numeratorMovement := numerator.later_close order
    have denominatorMovementForward := denominator.later_close order
    have denominatorMovement :
        Data.Gaussian.Norm.Basic.normSq (denominator.sample earlier - denominator.sample later) <=
          Geometric.Basic.quarterRadius denominator.errorScale earlier := by
      have identity : denominator.sample earlier - denominator.sample later =
          -(denominator.sample later - denominator.sample earlier) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
            Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
      rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
      exact denominatorMovementForward
    have quotientBound :=
      Quotient.IntegrationQuotientVariation.normSq_div_sub_div_le
        lower.positive
        (leftNumerator := numerator.sample later)
        (rightNumerator := numerator.sample earlier)
        (leftDenominator := denominator.sample later)
        (rightDenominator := denominator.sample earlier)
        (numeratorSlope := (1 : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate))
        (numeratorBound := numerator.centerBound)
        (denominatorBound := denominator.centerBound)
        (pointMovement :=
          Geometric.Basic.quarterRadius numerator.errorScale earlier)
        (rootMovement :=
          Geometric.Basic.quarterRadius denominator.errorScale earlier)
        (by
            simpa only [Fraction.Field.one_mul]
              using numeratorMovement)
        (numerator.sample_bounded earlier)
        (denominator.sample_bounded earlier)
        denominatorMovement
        (lower.sample_lower later) (lower.sample_lower earlier)
    calc
      Data.Gaussian.Norm.Basic.normSq (numerator.sample later / denominator.sample later -
          numerator.sample earlier / denominator.sample earlier) <=
        Purelib.Approximation.Rational.Budget.Quotient.quotientBound
          1 numerator.centerBound denominator.centerBound lower.lowerSq
          (Geometric.Basic.quarterRadius numerator.errorScale earlier)
          (Geometric.Basic.quarterRadius denominator.errorScale earlier) :=
        quotientBound
      _ = Geometric.Basic.quarterRadius
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientErrorScale numerator denominator
            lower) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        unfold Purelib.Approximation.Rational.Budget.Quotient.quotientBound
          Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientErrorScale
        let geometric : Coordinate := (1 / 4 :
          Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) ^ earlier
        change
          (2 * (1 * (numerator.errorScale * geometric) *
              denominator.centerBound +
            numerator.centerBound * (denominator.errorScale * geometric))) /
              (lower.lowerSq * lower.lowerSq) =
            ((2 * (numerator.errorScale * denominator.centerBound +
                numerator.centerBound * denominator.errorScale)) /
              (lower.lowerSq * lower.lowerSq)) * geometric
        rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
          Algebra.Field.ExplicitField.div_eq_mul_inv]
        ring1
  centerBound := numerator.centerBound / lower.lowerSq
  centerBound_nonneg := Fraction.Order.Field.div_nonneg_direct
    numerator.centerBound_nonneg lower.positive.le
  sample_bounded := by
    intro index
    rw [Data.Gaussian.Field.normSq_div _ _ (lower.sample_nonzero index)]
    calc
      Data.Gaussian.Norm.Basic.normSq (numerator.sample index) / Data.Gaussian.Norm.Basic.normSq
        (denominator.sample index) <=
          Data.Gaussian.Norm.Basic.normSq (numerator.sample index) / lower.lowerSq :=
        Fraction.Order.Field.div_le_div_of_nonneg_left_direct
          (Data.Gaussian.Norm.Basic.normSq_nonneg _) lower.positive (lower.sample_lower index)
      _ <= numerator.centerBound / lower.lowerSq := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (numerator.sample_bounded index)
          (Fraction.Order.Field.inv_pos_direct lower.positive).le

/-- Each quotient sample uses the original numerator and denominator at the same index. -/
@[simp] theorem quotientApproximation_sample
    (numerator denominator :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    (lower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower denominator) (index : Nat)
      :
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation numerator denominator
      lower).sample index =
      numerator.sample index / denominator.sample index :=
  rfl

/-- One positive lower bound shared by two equal-index denominator streams. -/
@[expose] def commonLower {first second :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation}
    (firstLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower first) (secondLower :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower second) :
    Coordinate :=
  min firstLower.lowerSq secondLower.lowerSq

/-- The minimum of the two retained positive denominator bounds is positive. -/
theorem commonLower_positive {first second :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation}
    (firstLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower first) (secondLower :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower second) :
    0 < Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.commonLower firstLower secondLower :=
  Fraction.Order.Basic.lt_min firstLower.positive secondLower.positive

/-- Sensitivity coefficient for replacing both operands of a finite equal-index quotient. -/
@[expose] def quotientComparisonCoefficient
    (secondNumerator secondDenominator :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    {firstDenominator : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation}
    (firstLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower firstDenominator)
    (secondLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower secondDenominator) :
      Coordinate :=
  (2 * (secondDenominator.centerBound + secondNumerator.centerBound)) /
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.commonLower firstLower secondLower *
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.commonLower firstLower secondLower)

/-- The quotient comparison coefficient is nonnegative. -/
theorem quotientComparisonCoefficient_nonnegative
    (secondNumerator secondDenominator :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    {firstDenominator : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation}
    (firstLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower firstDenominator)
    (secondLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower secondDenominator) :
    0 <= Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonCoefficient
      secondNumerator secondDenominator
      firstLower secondLower := by
  unfold Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonCoefficient
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg secondDenominator.centerBound_nonneg
        secondNumerator.centerBound_nonneg))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.commonLower_positive firstLower
        secondLower).le
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.commonLower_positive firstLower
        secondLower).le)

/-- Divide the positive target by one plus the quotient comparison coefficient. -/
@[expose] def quotientComparisonTarget
    (secondNumerator secondDenominator :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    {firstDenominator : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation}
    (firstLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower firstDenominator)
    (secondLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower secondDenominator)
    (target : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) : Coordinate :=
  target / (1 + Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonCoefficient
    secondNumerator
    secondDenominator firstLower secondLower)

/-- The adjusted quotient comparison target is positive. -/
theorem quotientComparisonTarget_positive
    (secondNumerator secondDenominator :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    {firstDenominator : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation}
    (firstLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower firstDenominator)
    (secondLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower secondDenominator)
    {target : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate} (positive : 0 < target) :
    0 < Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonTarget secondNumerator
      secondDenominator
      firstLower secondLower target :=
  Fraction.Order.Field.div_pos_direct positive
    (add_pos_of_pos_of_nonneg (by decide)
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonCoefficient_nonnegative
        secondNumerator
        secondDenominator firstLower secondLower))

/-- The adjusted target times the comparison coefficient is strictly below the original target. -/
theorem quotientComparisonTarget_budget_lt
    (secondNumerator secondDenominator :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    {firstDenominator : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation}
    (firstLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower firstDenominator)
    (secondLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower secondDenominator)
    {target : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate} (positive : 0 < target) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonTarget secondNumerator
      secondDenominator
        firstLower secondLower target *
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonCoefficient secondNumerator
        secondDenominator
        firstLower secondLower < target := by
  let coefficient := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonCoefficient
    secondNumerator
    secondDenominator firstLower secondLower
  have coefficientNonnegative : 0 <= coefficient :=
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonCoefficient_nonnegative
      secondNumerator
      secondDenominator firstLower secondLower
  have denominatorPositive : 0 < 1 + coefficient :=
    add_pos_of_pos_of_nonneg (by decide) coefficientNonnegative
  have fractionLt : coefficient / (1 + coefficient) < 1 := by
    apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
    calc
      coefficient = 0 + coefficient :=
        (Fraction.Field.zero_add coefficient).symm
      _ < 1 + coefficient :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct (by decide) _
      _ = 1 * (1 + coefficient) := by ring1
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    positive fractionLt
  change target / (1 + coefficient) * coefficient < target
  calc
    target / (1 + coefficient) * coefficient =
        target * (coefficient / (1 + coefficient)) := by
      rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
        Algebra.Field.ExplicitField.div_eq_mul_inv]
      ring1
    _ < target * 1 := scaled
    _ = target := Fraction.Field.mul_one_direct _

/-- Equal-index geometric quotients respect operational equality of both sources, using only a displayed positive sample
lower bound on each denominator. -/
@[expose] def quotientApproximation_respects
    (firstNumerator secondNumerator firstDenominator secondDenominator :
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    (firstLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower firstDenominator)
    (secondLower : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower secondDenominator)
    (numeratorEquivalent : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      firstNumerator.toApproximation
      secondNumerator.toApproximation)
    (denominatorEquivalent : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      firstDenominator.toApproximation
      secondDenominator.toApproximation) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation firstNumerator
        firstDenominator firstLower).toApproximation
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation secondNumerator
        secondDenominator secondLower).toApproximation where
  compare := by
    intro firstStart secondStart target positive
    let inputTarget := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonTarget
      secondNumerator
      secondDenominator firstLower secondLower target
    have inputPositive : 0 < inputTarget :=
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonTarget_positive
        secondNumerator secondDenominator
        firstLower secondLower positive
    let numeratorComparison := numeratorEquivalent.compare firstStart
      secondStart inputTarget inputPositive
    let denominatorComparison := denominatorEquivalent.compare firstStart
      secondStart inputTarget inputPositive
    let firstIndex := max numeratorComparison.leftIndex
      denominatorComparison.leftIndex
    let secondIndex := max numeratorComparison.rightIndex
      denominatorComparison.rightIndex
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := numeratorComparison.left_ge.trans (Purelib.Data.Nat.Order.le_max_left _ _)
        right_ge := numeratorComparison.right_ge.trans (Purelib.Data.Nat.Order.le_max_left _ _)
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have numeratorClose := numeratorComparison.close
            ((Purelib.Data.Nat.Order.le_max_left numeratorComparison.leftIndex
              denominatorComparison.leftIndex).trans firstOrder)
            ((Purelib.Data.Nat.Order.le_max_left numeratorComparison.rightIndex
              denominatorComparison.rightIndex).trans secondOrder)
          have numeratorClose' :
              Data.Gaussian.Norm.Basic.normSq (firstNumerator.sample firstLater -
                secondNumerator.sample secondLater) < inputTarget := by
            simpa only [
              Gaussian.Geometric.GeometricApproximation.toApproximation_sample]
              using numeratorClose
          have denominatorCloseForward := denominatorComparison.close
            ((Purelib.Data.Nat.Order.le_max_right numeratorComparison.leftIndex
              denominatorComparison.leftIndex).trans firstOrder)
            ((Purelib.Data.Nat.Order.le_max_right numeratorComparison.rightIndex
              denominatorComparison.rightIndex).trans secondOrder)
          have denominatorCloseForward' :
              Data.Gaussian.Norm.Basic.normSq (firstDenominator.sample firstLater -
                secondDenominator.sample secondLater) < inputTarget := by
            simpa only [
              Gaussian.Geometric.GeometricApproximation.toApproximation_sample]
              using denominatorCloseForward
          have denominatorClose :
              Data.Gaussian.Norm.Basic.normSq (secondDenominator.sample secondLater -
                  firstDenominator.sample firstLater) <= inputTarget := by
            have identity :
                secondDenominator.sample secondLater -
                    firstDenominator.sample firstLater =
                  -(firstDenominator.sample firstLater -
                    secondDenominator.sample secondLater) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                  Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
            rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
            exact denominatorCloseForward'.le
          have commonFirst : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.commonLower firstLower
            secondLower <=
              Data.Gaussian.Norm.Basic.normSq (firstDenominator.sample firstLater) :=
            (Fraction.Order.Basic.min_le_left _ _).trans (firstLower.sample_lower firstLater)
          have commonSecond : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.commonLower
            firstLower secondLower <=
              Data.Gaussian.Norm.Basic.normSq (secondDenominator.sample secondLater) :=
            (Fraction.Order.Basic.min_le_right _ _).trans (secondLower.sample_lower secondLater)
          have quotientBound :=
            Quotient.IntegrationQuotientVariation.normSq_div_sub_div_le
              (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.commonLower_positive firstLower
                secondLower)
              (leftNumerator := firstNumerator.sample firstLater)
              (rightNumerator := secondNumerator.sample secondLater)
              (leftDenominator := firstDenominator.sample firstLater)
              (rightDenominator := secondDenominator.sample secondLater)
              (numeratorSlope := (1 : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate))
              (numeratorBound := secondNumerator.centerBound)
              (denominatorBound := secondDenominator.centerBound)
              (pointMovement := inputTarget)
              (rootMovement := inputTarget)
              (by
                  simpa only [Fraction.Field.one_mul]
                    using numeratorClose'.le)
              (secondNumerator.sample_bounded secondLater)
              (secondDenominator.sample_bounded secondLater)
              denominatorClose commonFirst commonSecond
          change Data.Gaussian.Norm.Basic.normSq
              (firstNumerator.sample firstLater /
                  firstDenominator.sample firstLater -
                secondNumerator.sample secondLater /
                  secondDenominator.sample secondLater) < target
          calc
            Data.Gaussian.Norm.Basic.normSq
                (firstNumerator.sample firstLater /
                    firstDenominator.sample firstLater -
                  secondNumerator.sample secondLater /
                    secondDenominator.sample secondLater) <=
              Purelib.Approximation.Rational.Budget.Quotient.quotientBound
                1 secondNumerator.centerBound secondDenominator.centerBound
                (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.commonLower firstLower
                  secondLower) inputTarget inputTarget :=
              quotientBound
            _ = inputTarget *
                Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonCoefficient
                  secondNumerator
                  secondDenominator firstLower secondLower := by
              unfold Purelib.Approximation.Rational.Budget.Quotient.quotientBound
                Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonCoefficient
              rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
                Algebra.Field.ExplicitField.div_eq_mul_inv]
              ring1
            _ < target :=
              Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientComparisonTarget_budget_lt
              secondNumerator secondDenominator firstLower secondLower positive }

/-! ## Synchronized normalization sources -/

/-- Equal-index numerator `adj(A)B` underlying one normalized period entry. -/
@[expose] def normalizationNumerator {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) (row column : Fin genus) :
    GeometricApproximation :=
  ScaledInverseCertificate.geometricProductEntry (PeriodMatrix.canonicalScaledInverse data.aMatrix).inverse
    (PeriodMatrix.geometricMatrixOfNamed data.bMatrix) row column

/-- Equal-index fraction-free inverse scalar underlying normalization. -/
@[expose] def normalizationDenominator {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) : GeometricApproximation :=
  (PeriodMatrix.canonicalScaledInverse data.aMatrix).scalar

/-- The finite inverse-separation certificate is precisely a sample lower bound for the synchronized denominator stream.
-/
@[expose] def normalizationDenominatorLower {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data) where
  lowerSq := inverseLower.lowerSq
  positive := inverseLower.positive
  sample_lower := inverseLower.sample_lower

/-- One raw equal-index normalized period entry, now carrying its own geometric refinement and boundedness data. -/
@[expose] def synchronizedEntryApproximation {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) : GeometricApproximation :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row column)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominatorLower inverseLower)

/-- The raw equal-index quotient of the canonical numerator and denominator is literally the synchronized normalized
matrix entry. -/
theorem synchronizedEntry_core {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (row column : Fin genus) (index : Nat) :
    (Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
      column).sample index /
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).sample index
        =
      Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data index
        row column := by
  let aSource := PeriodMatrix.geometricMatrixOfNamed data.aMatrix
  let bSource := PeriodMatrix.geometricMatrixOfNamed data.bMatrix
  let computed := PeriodMatrix.canonicalScaledInverse data.aMatrix
  let sampledA := PeriodMatrix.sampledMatrix data.aMatrix index
  let inverse :=
    PivotedScaledInverse.completeScaledInverse sampledA
  have inverseSamples :=
    PivotedScaledInverse.completeApproximation_sample aSource index
  have aSourceSample :
      Approximation.Matrix.sampleMatrix aSource index =
        sampledA := by
    exact PeriodMatrix.sample_geometricMatrixOfNamed data.aMatrix index
  rw [aSourceSample] at inverseSamples
  have computedScalarSample : computed.scalar.sample index = inverse.scalar := by
    simpa only [computed, PeriodMatrix.canonicalScaledInverse, aSource] using inverseSamples.1
  have computedInverseSample :
      Approximation.Matrix.sampleMatrix computed.inverse
          index = inverse.inverse := by
    simpa only [computed, PeriodMatrix.canonicalScaledInverse, aSource] using inverseSamples.2
  have bSourceSample :
      Approximation.Matrix.sampleMatrix bSource index =
        PeriodMatrix.sampledMatrix data.bMatrix index := by
    exact PeriodMatrix.sample_geometricMatrixOfNamed data.bMatrix index
  rw [show (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
    column).sample index =
      Multiplication.mul inverse.inverse
        (PeriodMatrix.sampledMatrix data.bMatrix index) row column by
    unfold Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator
    rw [ScaledInverseCertificate.geometricProductEntry_sample]
    change Multiplication.mul
        (Approximation.Matrix.sampleMatrix computed.inverse
          index)
        (Approximation.Matrix.sampleMatrix bSource index)
          row column = _
    rw [bSourceSample, computedInverseSample]]
  rw [show (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).sample
    index = inverse.scalar by
    exact computedScalarSample]
  unfold Certificate.synchronizedNormalizedMatrix
    Certificate.synchronizedScaledInverse
  rw [Energy.divideGaussianMatrix_apply]

/-- The geometric normalization source displays literally the raw matrix entry used by the finite energy transport
argument at every index. -/
theorem synchronizedEntryApproximation_sample {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) (index : Nat) :
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntryApproximation data
      inverseLower row column).sample index =
      Certificate.synchronizedNormalizedMatrix data index
        row column := by
  rw [show (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntryApproximation data
    inverseLower row column).sample
      index =
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
          column).sample index /
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).sample
            index by rfl]
  exact Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntry_core data row column
    index

/-! ## Dropped sources for a certified tail anchor -/

/-- One anchor value and the approximation's later-movement bound control the squared norm of every retained sample. -/
private theorem drop_sample_normSq_lower (source :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.GeometricApproximation)
    (anchor index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (source.sample anchor) / 2 -
        Geometric.Basic.quarterRadius source.errorScale anchor <=
      Data.Gaussian.Norm.Basic.normSq
        ((source.drop anchor).sample index) := by
  rw [GeometricApproximation.drop_sample]
  have order : anchor <= anchor + index := Nat.le_add_right anchor index
  have movementForward := source.later_close order
  have reverseDifference :
      source.sample anchor - source.sample (anchor + index) =
        -(source.sample (anchor + index) - source.sample anchor) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.neg_re,
        Data.Gaussian.Basic.neg_im] <;> ring1
  have movement :
      Data.Gaussian.Norm.Basic.normSq
          (source.sample anchor - source.sample (anchor + index)) <=
        Geometric.Basic.quarterRadius source.errorScale anchor := by
    rw [reverseDifference, Data.Gaussian.Norm.Basic.normSq_neg]
    exact movementForward
  have triangle :=
    Data.Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub
      (source.sample anchor) (source.sample (anchor + index))
  apply (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).2
  calc
    Data.Gaussian.Norm.Basic.normSq (source.sample anchor) / 2 <=
        Data.Gaussian.Norm.Basic.normSq
            (source.sample anchor - source.sample (anchor + index)) +
          Data.Gaussian.Norm.Basic.normSq
            (source.sample (anchor + index)) :=
      (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).1 triangle
    _ <= Geometric.Basic.quarterRadius source.errorScale anchor +
        Data.Gaussian.Norm.Basic.normSq
          (source.sample (anchor + index)) :=
      Fraction.Order.Arithmetic.add_le_add_right_direct movement _
    _ = Data.Gaussian.Norm.Basic.normSq
          (source.sample (anchor + index)) +
        Geometric.Basic.quarterRadius source.errorScale anchor :=
      Fraction.Field.add_comm _ _

/-- The certified tail anchor is a uniform sample lower bound for the dropped canonical denominator stream. -/
@[expose] def tailDenominatorLower {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower
      ((Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).drop
      certificate.anchor) where
  lowerSq := certificate.lowerSq
  positive := certificate.lowerSq_positive
  sample_lower := by
    intro index
    exact Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.drop_sample_normSq_lower
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data)
      certificate.anchor index

/-- One dropped equal-index normalized entry.

Its samples are the raw synchronized matrix at the shifted retained index. -/
@[expose] def droppedSynchronizedEntryApproximation {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (row column : Fin genus) : GeometricApproximation :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation
    ((Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row column).drop
      certificate.anchor)
    ((Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).drop
      certificate.anchor)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailDenominatorLower certificate)

/-- The dropped normalization source displays the raw matrix entry at the shifted retained index. -/
theorem droppedSynchronizedEntryApproximation_sample {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (row column : Fin genus) (index : Nat) :
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedSynchronizedEntryApproximation data
      certificate row column).sample
        index =
      Certificate.synchronizedNormalizedMatrix data
        (certificate.anchor + index) row column := by
  change (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
    column).sample
        (certificate.anchor + index) /
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).sample
        (certificate.anchor + index) = _
  exact Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntry_core data row column
    (certificate.anchor + index)

/-- Persistent fraction-free matrix multiplication realizes the canonical equal-index `adj(A)B` numerator for any scaled
inverse presentation, since the adjugate is presentation-independent. -/
@[expose] def normalizationNumerator_equivalent_scaled {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverse : PeriodMatrix.ScaledInverseCertificate data.aMatrix) (row column : Fin genus) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (PeriodMatrix.matrixMul inverse.adjugate data.bMatrix row column).name
      (PeriodMatrix.geometricNamed
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
        column)).name := by
  let computed := PeriodMatrix.canonicalScaledInverse data.aMatrix
  let bSource := PeriodMatrix.geometricMatrixOfNamed data.bMatrix
  have equivalent := ScaledInverseCertificate.matrixMul_equivalent_geometricProduct
    inverse.adjugate data.bMatrix computed.inverse bSource
    (fun leftRow leftColumn => by
      simpa only [ScaledInverseCertificate.adjugate,
        PeriodMatrix.canonicalAdjugate_apply, computed] using
        NamedEquivalent.refl
          (PeriodMatrix.geometricNamed (computed.inverse leftRow leftColumn)).name)
    (fun rightRow rightColumn => by
      simpa only [bSource, PeriodMatrix.geometricMatrixOfNamed_apply] using
        ScaledInverseCertificate.named_equivalent_geometricOfNamed
          (data.bMatrix rightRow rightColumn))
    row column
  simpa only [computed, bSource,
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator] using equivalent

/-- Canonical sampler of one prepared scalar name. -/
@[expose] def preparedScalarSource {size : Nat} {matrix : PeriodMatrix.NamedMatrix size}
    (inverse : PeriodMatrix.ScaledInverseCertificate matrix) : GeometricApproximation :=
  GeometricApproximation.ofNamed
    inverse.scalar.name

/-- Whole-ball apartness of the prepared scalar supplies the weaker sample lower bound needed by its equal-index
quotient. -/
@[expose] def preparedScalarLower {size : Nat} {matrix : PeriodMatrix.NamedMatrix size}
    (inverse : PeriodMatrix.ScaledInverseCertificate matrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedScalarSource inverse) where
  lowerSq := inverse.scalarApart.certificate.lowerSq
  positive := inverse.scalarApart.certificate.positive
  sample_lower := by
    intro index
    exact Apart.Sampling.sampled_lower inverse.scalar
      inverse.scalarApart index

/-- Equal-index reciprocal using the canonical sampler of the prepared stateful denominator. -/
@[expose] def preparedScalarReciprocal {size : Nat} {matrix : PeriodMatrix.NamedMatrix size}
    (inverse : PeriodMatrix.ScaledInverseCertificate matrix) : GeometricApproximation :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation
    (GeometricApproximation.ofNamed
      (Coherence.exact 1).name)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedScalarSource inverse)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedScalarLower inverse)

/-- Equal-index reciprocal of the anchor-dropped raw scalar stream. -/
@[expose] def droppedRawReciprocal {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix) :
    GeometricApproximation :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation
    (GeometricApproximation.exact 1)
    ((Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).drop
      certificate.anchor)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailDenominatorLower certificate)

/-- Prepared scalar samples are operationally the anchor-dropped raw scalar samples. -/
@[expose] def preparedScalar_equivalent_droppedRaw {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedScalarSource
        certificate.toScaledInverseCertificate).toApproximation
      ((Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).drop
        certificate.anchor).toApproximation := by
  let inverse := certificate.toScaledInverseCertificate
  let raw := (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).drop
    certificate.anchor
  let prepared := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedScalarSource inverse
  have preparedToSampler : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
    prepared.toApproximation
      (Sampling.approximation inverse.scalar.name) :=
    Equivalence.approximationEquivalentOfSamplesEq _ _ (by intro index; rfl)
  have preparedToWrappedRaw : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Sampling.approximation inverse.scalar.name)
      (Sampling.approximation (PeriodMatrix.geometricNamed raw).name) := by
    change Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent inverse.scalar.name
      (PeriodMatrix.geometricNamed raw).name
    exact NamedEquivalent.trans
      (NamedEquivalent.symm inverse.canonicalScalarEquivalent)
      (by
        simpa only [inverse, raw,
          Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator,
          ScalarTailSeparationCertificate.scalarSource] using
          certificate.sourceEquivalent)
  have wrappedRawToRaw : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Sampling.approximation (PeriodMatrix.geometricNamed raw).name)
      raw.toApproximation := by
    simpa only [PeriodMatrix.geometricNamed,
      Coherent.CoherentNamed.ofApproximation] using
      Equivalent.toNamed_sampling raw.toApproximation
  change Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent prepared.toApproximation
    raw.toApproximation
  exact Equivalent.trans preparedToSampler
    (Equivalent.trans preparedToWrappedRaw
      wrappedRawToRaw)

/-! ## Operational equivalence with persistent normalization -/

/-- Every sample of the geometric realization of an exact Gaussian value is that value. -/
@[simp] theorem geometricOfExact_sample (value :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Gaussian) (index : Nat) :
    (GeometricApproximation.ofNamed
      (Coherence.exact value).name).sample index =
      value := by
  rfl

/-- Canonical sampler of the prepared denominator used by stateful division. -/
@[expose] def preparedDenominatorSource {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) :
    GeometricApproximation :=
  GeometricApproximation.ofNamed
    inverseLower.toScaledInverseCertificate.scalar.name

/-- Whole-ball apartness of the prepared scalar supplies the weaker sample lower bound needed by its equal-index
quotient. -/
@[expose] def preparedDenominatorLower {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.SampleLower
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedDenominatorSource inverseLower)
      where
  lowerSq := inverseLower.toScaledInverseCertificate.scalarApart.certificate.lowerSq
  positive :=
    inverseLower.toScaledInverseCertificate.scalarApart.certificate.positive
  sample_lower := by
    intro index
    exact Apart.Sampling.sampled_lower
      inverseLower.toScaledInverseCertificate.scalar
      inverseLower.toScaledInverseCertificate.scalarApart index

/-- Equal-index reciprocal using the canonical sampler of the prepared stateful denominator. -/
@[expose] def preparedReciprocalApproximation {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) :
    GeometricApproximation :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation
    (GeometricApproximation.ofNamed
      (Coherence.exact 1).name)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedDenominatorSource inverseLower)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedDenominatorLower inverseLower)

/-- Equal-index reciprocal using the unprepared raw scalar stream. -/
@[expose] def rawReciprocalApproximation {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) :
    GeometricApproximation :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation
    (GeometricApproximation.exact 1)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominatorLower inverseLower)

/-- Prepared scalar samples are operationally the raw fraction-free scalar samples from which apartification was
constructed. -/
@[expose] def preparedDenominator_equivalent_raw {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedDenominatorSource
      inverseLower).toApproximation
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator
        data).toApproximation := by
  let inverse := inverseLower.toScaledInverseCertificate
  let raw := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data
  let prepared := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedDenominatorSource
    inverseLower
  have preparedToSampler : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
    prepared.toApproximation
      (Sampling.approximation inverse.scalar.name) :=
    Equivalence.approximationEquivalentOfSamplesEq _ _
      (by intro index; rfl)
  have preparedToWrappedRaw : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Sampling.approximation inverse.scalar.name)
      (Sampling.approximation
        (PeriodMatrix.geometricNamed raw).name) := by
    change Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent inverse.scalar.name
      (PeriodMatrix.geometricNamed raw).name
    simpa only [inverse, raw,
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator,
      PeriodMatrix.canonicalInverseScalar] using
      NamedEquivalent.symm
        inverse.canonicalScalarEquivalent
  have wrappedRawToRaw : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Sampling.approximation (PeriodMatrix.geometricNamed raw).name)
      raw.toApproximation := by
    simpa only [PeriodMatrix.geometricNamed,
      Coherent.CoherentNamed.ofApproximation] using
      Equivalent.toNamed_sampling
        raw.toApproximation
  change Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent prepared.toApproximation
    raw.toApproximation
  exact Equivalent.trans preparedToSampler
    (Equivalent.trans preparedToWrappedRaw
      wrappedRawToRaw)

/-- The exact-one sampler and the constant geometric one stream have the same displayed rational sample at every index.
-/
@[expose] def preparedOne_equivalent_rawOne :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
    (GeometricApproximation.ofNamed
      (Coherence.exact 1).name).toApproximation
    (GeometricApproximation.exact
      1).toApproximation :=
  Equivalence.approximationEquivalentOfSamplesEq _ _
    (by intro index; exact geometricOfExact_sample 1 index)

/-- Replacing the apartified denominator sampler by its raw synchronized source preserves the reciprocal's finite
operational value. -/
@[expose] def preparedReciprocal_equivalent_raw {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedReciprocalApproximation
      inverseLower).toApproximation
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.rawReciprocalApproximation
        inverseLower).toApproximation := by
  exact Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation_respects _ _ _ _
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedDenominatorLower inverseLower)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominatorLower inverseLower)
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedOne_equivalent_rawOne
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedDenominator_equivalent_raw
      inverseLower)

/-- The stateful reciprocal used by persistent normalization is operationally the equal-index reciprocal of the raw
fraction-free scalar stream. -/
@[expose] def inverseScalar_equivalent_rawReciprocal {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (PeriodMatrix.inverseScalar inverseLower.toScaledInverseCertificate).name
      (PeriodMatrix.geometricNamed
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.rawReciprocalApproximation
        inverseLower)).name := by
  let inverse := inverseLower.toScaledInverseCertificate
  let one := Coherence.exact 1
  let sampled :=
    Sample.sampledQuotientApproximation one
      inverse.scalar inverse.scalarApart
  let prepared := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedReciprocalApproximation
    inverseLower
  let raw := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.rawReciprocalApproximation
    inverseLower
  have actualToSampled : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (CoherentNamed.div one inverse.scalar
        inverse.scalarApart).name sampled.toNamed := by
    exact Equivalence.coherentDiv_toSampled
      one inverse.scalar inverse.scalarApart
  have sampledToPreparedApprox : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent sampled
    prepared.toApproximation :=
    Equivalence.approximationEquivalentOfSamplesEq _ _
      (by intro index; rfl)
  have sampledToPrepared : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
    sampled.toNamed
      (PeriodMatrix.geometricNamed prepared).name := by
    simpa only [PeriodMatrix.geometricNamed,
      Coherent.CoherentNamed.ofApproximation] using
      Equivalence.approximationEquivalent_toNamed
        sampledToPreparedApprox
  have preparedToRaw : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
    (PeriodMatrix.geometricNamed prepared).name
      (PeriodMatrix.geometricNamed raw).name := by
    simpa only [PeriodMatrix.geometricNamed,
      Coherent.CoherentNamed.ofApproximation] using
      Equivalence.approximationEquivalent_toNamed
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedReciprocal_equivalent_raw
          inverseLower)
  change Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
    (CoherentNamed.div one inverse.scalar
      inverse.scalarApart).name (PeriodMatrix.geometricNamed raw).name
  exact NamedEquivalent.trans actualToSampled
    (NamedEquivalent.trans sampledToPrepared
      preparedToRaw)

/-- Replacing the apartified denominator sampler by its anchor-dropped raw source preserves the reciprocal's finite
operational value. -/
@[expose] def preparedScalarReciprocal_equivalent_droppedRaw {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedScalarReciprocal
        certificate.toScaledInverseCertificate).toApproximation
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedRawReciprocal
        certificate).toApproximation :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.quotientApproximation_respects _ _ _ _
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedScalarLower
      certificate.toScaledInverseCertificate)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailDenominatorLower certificate)
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedOne_equivalent_rawOne
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedScalar_equivalent_droppedRaw
      certificate)

/-- The stateful reciprocal of a certified tail is operationally the equal-index reciprocal of the anchor-dropped raw
scalar stream. -/
@[expose] def tailInverseScalar_equivalent_droppedRawReciprocal {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (PeriodMatrix.inverseScalar certificate.toScaledInverseCertificate).name
      (PeriodMatrix.geometricNamed
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedRawReciprocal certificate)).name :=
        by
  let inverse := certificate.toScaledInverseCertificate
  let one := Coherence.exact 1
  let sampled :=
    Sample.sampledQuotientApproximation one
      inverse.scalar inverse.scalarApart
  let prepared := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.preparedScalarReciprocal inverse
  let raw := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedRawReciprocal certificate
  have actualToSampled : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (CoherentNamed.div one inverse.scalar
        inverse.scalarApart).name sampled.toNamed :=
    Equivalence.coherentDiv_toSampled
      one inverse.scalar inverse.scalarApart
  have sampledToPreparedApprox : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent sampled
    prepared.toApproximation :=
    Equivalence.approximationEquivalentOfSamplesEq _ _ (by intro index; rfl)
  have sampledToPrepared : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
    sampled.toNamed
      (PeriodMatrix.geometricNamed prepared).name := by
    simpa only [PeriodMatrix.geometricNamed,
      Coherent.CoherentNamed.ofApproximation] using
      Equivalence.approximationEquivalent_toNamed
        sampledToPreparedApprox
  have preparedToRaw : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
    (PeriodMatrix.geometricNamed prepared).name
      (PeriodMatrix.geometricNamed raw).name := by
    simpa only [PeriodMatrix.geometricNamed,
      Coherent.CoherentNamed.ofApproximation] using
      Equivalence.approximationEquivalent_toNamed

          (preparedScalarReciprocal_equivalent_droppedRaw
          certificate)
  change Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
    (CoherentNamed.div one inverse.scalar
      inverse.scalarApart).name (PeriodMatrix.geometricNamed raw).name
  exact NamedEquivalent.trans actualToSampled
    (NamedEquivalent.trans sampledToPrepared
      preparedToRaw)

/-- A tail-normalized period entry is operationally equivalent to the dropped geometric approximation whose samples are
the raw synchronized matrix at the shifted retained index. -/
@[expose] def tailNormalizedEntry_equivalent_dropped {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (row column : Fin genus) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      ((NormalizedPeriodData.ofScaledInverse data
        certificate.toScaledInverseCertificate).omega row column).name
      (PeriodMatrix.geometricNamed
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedSynchronizedEntryApproximation data
          certificate
          row column)).name := by
  let inverse := certificate.toScaledInverseCertificate
  let numerator := PeriodMatrix.matrixMul inverse.adjugate data.bMatrix row column
  let reciprocal := PeriodMatrix.inverseScalar inverse
  let numeratorSource :=
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row column).drop
      certificate.anchor
  let reciprocalSource := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedRawReciprocal
    certificate
  let productSource :=
    GeometricApproximation.mul
      numeratorSource reciprocalSource
  let synchronizedSource :=
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedSynchronizedEntryApproximation data
      certificate row column
  have numeratorEquivalent : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
    numerator.name
      (PeriodMatrix.geometricNamed numeratorSource).name := by
    simpa only [numerator, numeratorSource, inverse] using
      NamedEquivalent.trans
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator_equivalent_scaled
          inverse row column)
        (PeriodMatrix.geometricNamed_drop_equivalent
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row column)
            certificate.anchor)
  have reciprocalEquivalent : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
    reciprocal.name
      (PeriodMatrix.geometricNamed reciprocalSource).name := by
    simpa only [reciprocal, reciprocalSource, inverse] using

        tailInverseScalar_equivalent_droppedRawReciprocal
        certificate
  have productEquivalent : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (CoherentNamed.mul numerator reciprocal).name
      (PeriodMatrix.geometricNamed productSource).name :=
    ScaledInverseCertificate.coherentMul_equivalent_geometricMul numerator reciprocal
      numeratorSource reciprocalSource numeratorEquivalent reciprocalEquivalent
  have productSamples : forall index, productSource.sample index =
      synchronizedSource.sample index := by
    intro index
    change
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
        column).sample
          (certificate.anchor + index) *
          ((1 : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Gaussian) /
            (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).sample
              (certificate.anchor + index)) =
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
          column).sample
            (certificate.anchor + index) /
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).sample
            (certificate.anchor + index)
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
      Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  have productToSynchronized : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (PeriodMatrix.geometricNamed productSource).name
      (PeriodMatrix.geometricNamed synchronizedSource).name :=
    ScaledInverseCertificate.geometricNamed_equivalent_of_samples productSource synchronizedSource
      productSamples
  have result := NamedEquivalent.trans
    productEquivalent productToSynchronized
  simpa only [reciprocalSource, numeratorSource, synchronizedSource,
    NormalizedPeriodData.ofScaledInverse,
    NormalizedPeriodData.omega, PeriodMatrix.normalize_apply, numerator, reciprocal,
    inverse] using result

/-- Persistent fraction-free matrix multiplication realizes the same equal-index `adj(A)B` numerator used by
synchronized normalization. -/
@[expose] def normalizationNumerator_equivalent {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (PeriodMatrix.matrixMul inverseLower.toScaledInverseCertificate.adjugate
        data.bMatrix row column).name
      (PeriodMatrix.geometricNamed
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
        column)).name := by
  let inverse := inverseLower.toScaledInverseCertificate
  let computed := PeriodMatrix.canonicalScaledInverse data.aMatrix
  let bSource := PeriodMatrix.geometricMatrixOfNamed data.bMatrix
  have equivalent := ScaledInverseCertificate.matrixMul_equivalent_geometricProduct
    inverse.adjugate data.bMatrix computed.inverse bSource
    (fun leftRow leftColumn => by
      simpa only [inverse, ScaledInverseCertificate.adjugate,
        PeriodMatrix.canonicalAdjugate_apply, computed] using
        NamedEquivalent.refl
          (PeriodMatrix.geometricNamed (computed.inverse leftRow leftColumn)).name)
    (fun rightRow rightColumn => by
      simpa only [bSource, PeriodMatrix.geometricMatrixOfNamed_apply] using
        ScaledInverseCertificate.named_equivalent_geometricOfNamed
          (data.bMatrix rightRow rightColumn))
    row column
  simpa only [inverse, computed, bSource,
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator] using
    equivalent

/-- Every persistent normalized period entry is operationally equivalent to the geometric approximation whose index-`n`
sample is literally the raw synchronized normalized matrix at index `n`. -/
@[expose] def normalizedEntry_equivalent_synchronized {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      ((Certificate.normalizedData data inverseLower).omega
        row column).name
      (PeriodMatrix.geometricNamed
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntryApproximation data
          inverseLower row column)).name := by
  let inverse := inverseLower.toScaledInverseCertificate
  let numerator := PeriodMatrix.matrixMul inverse.adjugate data.bMatrix row column
  let reciprocal := PeriodMatrix.inverseScalar inverse
  let numeratorSource := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator
    data row column
  let reciprocalSource :=
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.rawReciprocalApproximation inverseLower
  let productSource :=
    GeometricApproximation.mul
      numeratorSource reciprocalSource
  let synchronizedSource :=
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntryApproximation data
      inverseLower row column
  have productEquivalent : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (CoherentNamed.mul numerator reciprocal).name
      (PeriodMatrix.geometricNamed productSource).name := by
    exact ScaledInverseCertificate.coherentMul_equivalent_geometricMul numerator reciprocal
      numeratorSource reciprocalSource
      (by
        simpa only [numerator, inverse] using
          Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator_equivalent
            inverseLower row column)
      (by
        simpa only [reciprocal, reciprocalSource, inverse] using
          Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.inverseScalar_equivalent_rawReciprocal
            inverseLower)
  have productSamples : forall index, productSource.sample index =
      synchronizedSource.sample index := by
    intro index
    change
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
        column).sample index *
          ((1 : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Gaussian) /
            (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).sample
              index) =
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationNumerator data row
          column).sample index /
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizationDenominator data).sample
            index
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
      Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  have productToSynchronized : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.NamedEquivalent
      (PeriodMatrix.geometricNamed productSource).name
      (PeriodMatrix.geometricNamed synchronizedSource).name :=
    ScaledInverseCertificate.geometricNamed_equivalent_of_samples productSource synchronizedSource
      productSamples
  have result := NamedEquivalent.trans
    productEquivalent productToSynchronized
  simpa only [Certificate.normalizedData,
    NormalizedPeriodData.omega, PeriodMatrix.normalize_apply, numerator, reciprocal,
    inverse, synchronizedSource] using result

/-- Approximation-level form, exposing the raw synchronized sample index on the right rather than resampling its
productive wrapper. -/
@[expose] def normalizedEntry_equivalent_synchronizedApproximation {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Sampling.approximation
        ((Certificate.normalizedData data inverseLower).omega
          row column).name)
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntryApproximation data
        inverseLower row column).toApproximation :=
  Equivalent.trans
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.normalizedEntry_equivalent_synchronized data
      inverseLower row column)
    (by
      simpa only [PeriodMatrix.geometricNamed,
        Coherent.CoherentNamed.ofApproximation] using
        Equivalent.toNamed_sampling
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntryApproximation data
            inverseLower row column).toApproximation)

/-! ## One shared finite comparison index -/

/-- A deliberately conservative squared comparison allowance. -/
@[expose] def comparisonTarget (radius :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) : Coordinate :=
  radius ^ 2 / 64

/-- A positive radius gives a positive squared comparison allowance. -/
theorem comparisonTarget_positive {radius :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate}
    (positive : 0 < radius) : 0 <
      Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius := by
  unfold Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
    (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by omega))

/-- Thirty-eight comparison allowances fit strictly below the original radius squared. -/
theorem thirtyEight_comparisonTarget_lt_sq {radius :
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate}
    (positive : 0 < radius) : 38 *
      Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius < radius ^ 2
      := by
  have squarePositive : 0 < radius ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct positive 2
  have sixtyFourPositive : (0 : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) < 64 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 64) (by omega)
  have fractionSmall : (38 : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) / 64 < 1
    := by
    apply (Fraction.Order.Field.div_lt_iff_pos sixtyFourPositive).2
    calc
      (38 : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) < (64 :
        Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) :=
        Fraction.Cast.Order.natCast_lt_direct
          (m := 38) (n := 64) (by omega)
      _ = 1 * 64 := by ring1
  calc
    38 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius = radius ^ 2 *
      ((38 : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) / 64) := by
      unfold Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
      rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
        Algebra.Field.ExplicitField.div_eq_mul_inv]
      ring1
    _ < radius ^ 2 * 1 :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        squarePositive fractionSmall
    _ = radius ^ 2 := Fraction.Field.mul_one_direct _

/-- Constructive maximum of a visibly finite family of natural indices.

The head coordinate contributes its exact value and the successor tail retains the original function on successor
indices. The empty family contributes zero. -/
@[expose] def finMax : {count : Nat} -> (Fin count -> Nat) -> Nat
  | 0, _ => 0
  | count + 1, values =>
      max (values 0) (finMax fun index : Fin count => values index.succ)

/-- Each retained finite coordinate is bounded by the recursively computed maximum.

The supplied original finite index selects the head or a successor coordinate. The successor bound is compared with the
same recursively retained maximum. -/
theorem le_finMax {count : Nat} (values : Fin count -> Nat)
    (index : Fin count) : values index <= finMax values := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      refine Purelib.Data.Fin.cases_induction ?_ (fun tail => ?_) index
      · change values ⟨0, Nat.zero_lt_succ count⟩ ≤
          max (values ⟨0, Nat.zero_lt_succ count⟩) (finMax (fun entry : Fin count => values entry.succ))
        exact Purelib.Data.Nat.Order.le_max_left _ _
      · exact (inductionHypothesis
          (fun entry : Fin count => values entry.succ) tail).trans
            (Purelib.Data.Nat.Order.le_max_right _ _)

/-- Constructive maximum over the finite square matrix of entry indices. -/
@[expose] def matrixMax {size : Nat} (values : Fin size -> Fin size -> Nat) : Nat :=
  finMax fun row => finMax (values row)

/-- Every entry in the finite index matrix is bounded by its nested maximum. -/
theorem le_matrixMax {size : Nat} (values : Fin size -> Fin size -> Nat)
    (row column : Fin size) : values row column <=
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.matrixMax values :=
  (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.le_finMax (values row) column).trans
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.le_finMax (fun entry => finMax (values entry))
      row)

/-- First canonical sampler index at which one normalized entry has small enough semantic allowance for the matrix
comparison. -/
@[expose] def entryComparisonStart {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (row column : Fin genus)
      : Nat :=
  let entry :=
    (Certificate.normalizedData data inverseLower).omega row column
  Search.firstQuarterBelow 1 0
    (entry.coherent.accuracyRequest
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius))

/-- One entry's fully computed operational comparison with the raw synchronized normalization stream. -/
@[expose] def entryComparison {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    Gaussian.Equivalence.Comparison
      (Sampling.approximation
        ((Certificate.normalizedData data inverseLower).omega
          row column).name)
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntryApproximation data
        inverseLower row column).toApproximation
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparisonStart data inverseLower
        radius row column) 0
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius) :=

    (normalizedEntry_equivalent_synchronizedApproximation
    data inverseLower
    row column).compare
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparisonStart data inverseLower
        radius row column) 0
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius)
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget_positive positive)

/-- One later persistent sampler index shared by every matrix entry. -/
@[expose] def persistentSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius) :
      Nat :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.matrixMax fun row column =>
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparison data inverseLower radius
      positive row column).leftIndex

/-- One raw synchronized sample index shared by every matrix entry. -/
@[expose] def synchronizedSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius) :
      Nat :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.matrixMax fun row column =>
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparison data inverseLower radius
      positive row column).rightIndex

/-- Each entry comparison left index is bounded by the common persistent sample index. -/
theorem entryComparison_left_le_persistentSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparison data inverseLower radius
      positive row column).leftIndex <=
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.persistentSampleIndex data inverseLower
        radius positive :=
  by
    simpa only [Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.persistentSampleIndex] using
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.le_matrixMax (fun leftRow leftColumn =>
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparison data inverseLower radius
          positive
          leftRow leftColumn).leftIndex) row column)

/-- Each entry comparison right index is bounded by the common synchronized sample index. -/
theorem entryComparison_right_le_synchronizedSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparison data inverseLower radius
      positive row column).rightIndex <=
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedSampleIndex data inverseLower
        radius positive :=
  by
    simpa only [Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedSampleIndex] using
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.le_matrixMax (fun leftRow leftColumn =>
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparison data inverseLower radius
          positive
          leftRow leftColumn).rightIndex) row column)

/-- Every entry coherence start is bounded by the common persistent sample index. -/
theorem entryComparisonStart_le_persistentSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparisonStart data inverseLower radius
      row column <=
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.persistentSampleIndex data inverseLower
        radius positive :=
  (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparison data inverseLower radius
    positive row column).left_ge.trans
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparison_left_le_persistentSampleIndex
      data inverseLower radius
      positive row column)

/-- The shared persistent sampler index has the small semantic allowance requested before the entrywise operational
comparisons. -/
theorem persistentSampleAllowance_lt {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    let entry :=
      (Certificate.normalizedData data inverseLower).omega
        row column
    entry.coherent.allowance
        (Gaussian.Process.Sampling.stateAt entry.name.process entry.name.state
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.persistentSampleIndex data inverseLower
            radius positive)) <
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius := by
  let entry :=
    (Certificate.normalizedData data inverseLower).omega row column
  let start := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparisonStart data
    inverseLower radius row column
  let persistent := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.persistentSampleIndex data
    inverseLower radius positive
  have requestPositive :
      0 < entry.coherent.accuracyRequest
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius) :=
    entry.coherent.accuracyRequest_pos
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget_positive positive)
  have startAccurate :
      Gaussian.Process.Sampling.refinementTarget start <
        entry.coherent.accuracyRequest
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius) := by
    exact Search.firstQuarterBelow_accurate 1 (by decide) 0
      (entry.coherent.accuracyRequest
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius))
      requestPositive
  have startOrder : start <= persistent := by
    exact
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparisonStart_le_persistentSampleIndex
      data inverseLower
      radius positive row column
  have persistentRequestSmall :
      Gaussian.Process.Sampling.refinementTarget persistent <
        entry.coherent.accuracyRequest
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius) :=
    (quarterRadius_antitone (by decide) startOrder).trans_lt
      startAccurate
  exact Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt entry.coherent
    entry.name.state persistent (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
      radius)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget_positive positive)
      persistentRequestSmall

/-- All entries can be evaluated at the one maximum raw index while retaining the strict operational comparison bound.
-/
theorem persistentSample_close_synchronized {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq
        ((Sampling.approximation
            ((Certificate.normalizedData data inverseLower).omega
              row column).name).sample
            (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.persistentSampleIndex data
              inverseLower radius positive) -
          Certificate.synchronizedNormalizedMatrix data
            (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedSampleIndex data
              inverseLower radius positive)
            row column) <
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius := by
  have close :=
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.entryComparison data inverseLower radius
      positive row column).close

        (entryComparison_left_le_persistentSampleIndex
        data inverseLower radius
        positive row column)

        (entryComparison_right_le_synchronizedSampleIndex
        data inverseLower
        radius positive row column)
  simpa only [
    Gaussian.Geometric.GeometricApproximation.toApproximation_sample,
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedEntryApproximation_sample] using
      close

/-- A sufficiently fine shared persistent request is automatically close to the one computed raw synchronized matrix.

The proof compares only finite process witnesses, finite coherence allowances, and rational squared-error budgets. -/
theorem centerMatrix_close_synchronized {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (comparisonRadius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate)
      (comparisonPositive : 0 < comparisonRadius)
    (centerTarget : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (centerPositive : 0
      < centerTarget)
    (centerSmall : centerTarget < Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
      comparisonRadius)
    (row column : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq
        (Positivity.centerMatrix
            (Certificate.normalizedData data inverseLower)
            centerTarget centerPositive row column -
          Certificate.synchronizedNormalizedMatrix data
            (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedSampleIndex data
              inverseLower comparisonRadius
              comparisonPositive) row column) <
      comparisonRadius ^ 2 := by
  let normalized := Certificate.normalizedData data inverseLower
  let entry := normalized.omega row column
  let prepared := normalized.prepareOmegaEntry centerTarget centerPositive row column
  let refined := prepared.name
  let center := prepared.center
  let witness := (refined.process.witness refined.state).val
  let persistent :=
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.persistentSampleIndex data inverseLower
      comparisonRadius comparisonPositive
  let persistentValue :=
    (Sampling.approximation entry.name).sample persistent
  let rawIndex :=
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedSampleIndex data inverseLower
      comparisonRadius
      comparisonPositive
  let rawValue :=
    Certificate.synchronizedNormalizedMatrix data rawIndex
      row column
  have ballRadiusLt :
      (refined.process.ball refined.state).radiusSq < centerTarget := by
    change (prepared.name.process.ball prepared.name.state).radiusSq < centerTarget
    rewrite [← prepared.ball_eq]
    exact prepared.accurate
  have centerAllowanceLt :
      entry.coherent.allowance refined.state < centerTarget := by
    have contract := normalized.omegaEntry_sharedRequest row column
      centerTarget centerPositive 0
    simpa only [entry, refined, prepared, NormalizedPeriodData.prepareOmegaEntry,
      Gaussian.Table.Request.prepareEntry, NormalizedPeriodData.refinedOmegaEntry] using
      contract.2.1
  have persistentAllowanceLt :
      entry.coherent.allowance
          (Gaussian.Process.Sampling.stateAt entry.name.process entry.name.state
            persistent) < Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
              comparisonRadius := by
    simpa only [entry, persistent, normalized] using
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.persistentSampleAllowance_lt data
        inverseLower comparisonRadius
        comparisonPositive row column
  have refinedPossible : entry.name.process.Possible refined.state witness := by
    exact (refined.process.witness refined.state).property
  have persistentPossible : entry.name.process.Possible
      (Gaussian.Process.Sampling.stateAt entry.name.process entry.name.state
        persistent) persistentValue := by
    exact Gaussian.Process.Sampling.witnessAt_possible entry.name.process
      entry.name.state persistent
  have witnessInside := entry.name.process.possible_inside refinedPossible
  have centerWitness : Data.Gaussian.Norm.Basic.normSq (center - witness) <=
      (refined.process.ball refined.state).radiusSq := by
    have identity : center - witness = -(witness - center) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im] <;> ring1
    rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
    exact witnessInside
  have semanticClose : Data.Gaussian.Norm.Basic.normSq (witness - persistentValue) <=
      4 * (entry.coherent.allowance refined.state +
        entry.coherent.allowance
          (Gaussian.Process.Sampling.stateAt entry.name.process entry.name.state
            persistent)) :=
    entry.coherent.possible_close refinedPossible persistentPossible
  have semanticSmall : Data.Gaussian.Norm.Basic.normSq (witness - persistentValue) <
      4 * (centerTarget + Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius) :=
    semanticClose.trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_direct centerAllowanceLt
          persistentAllowanceLt))
  have operationalSmall : Data.Gaussian.Norm.Basic.normSq (persistentValue - rawValue) <
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius := by
    simpa only [persistentValue, rawValue, persistent, rawIndex, entry,
      normalized] using
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.persistentSample_close_synchronized data
        inverseLower comparisonRadius
        comparisonPositive row column
  have witnessRawSmall : Data.Gaussian.Norm.Basic.normSq (witness - rawValue) <
      2 * (4 * (centerTarget + Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius) +
        Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius) := by
    calc
      Data.Gaussian.Norm.Basic.normSq (witness - rawValue) <=
          2 * (Data.Gaussian.Norm.Basic.normSq (witness - persistentValue) +
            Data.Gaussian.Norm.Basic.normSq (persistentValue - rawValue)) :=
        Data.Gaussian.Norm.Bounds.normSq_sub_le_via witness persistentValue rawValue
      _ < 2 * (4 * (centerTarget + Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius) +
          Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Fraction.Order.Arithmetic.add_lt_add_direct semanticSmall
            operationalSmall)
  have centerRawSmall : Data.Gaussian.Norm.Basic.normSq (center - rawValue) <
      18 * centerTarget + 20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius := by
    calc
      Data.Gaussian.Norm.Basic.normSq (center - rawValue) <=
          2 * (Data.Gaussian.Norm.Basic.normSq (center - witness) + Data.Gaussian.Norm.Basic.normSq
            (witness - rawValue)) :=
        Data.Gaussian.Norm.Bounds.normSq_sub_le_via center witness rawValue
      _ < 2 * (centerTarget +
          2 * (4 * (centerTarget + Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
            comparisonRadius) +
            Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius)) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Fraction.Order.Arithmetic.add_lt_add_direct
            (centerWitness.trans_lt ballRadiusLt) witnessRawSmall)
      _ = 18 * centerTarget +
          20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius :=
            by ring1
  have belowThirtyEight :
      18 * centerTarget + 20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius <
        38 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius :=
          by
    have scaledCenter : 18 * centerTarget <
        18 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        centerSmall
    calc
      18 * centerTarget + 20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius <
          18 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius +
            20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius
              :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct scaledCenter _
      _ = 38 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius :=
        by
        ring1
  have finalSmall := centerRawSmall.trans
    (belowThirtyEight.trans
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.thirtyEight_comparisonTarget_lt_sq
        comparisonPositive))
  have centerReadback : center = normalized.omegaCenter centerTarget centerPositive row column :=
    normalized.prepareOmegaEntry_center centerTarget centerPositive row column
  rw [centerReadback] at finalSmall
  simpa only [rawValue, rawIndex, normalized, Positivity.centerMatrix_apply] using finalSmall

/-- Reindex the automatic comparison by a displayed equality, allowing dependent certificate packages to keep the
computed natural index opaque. -/
theorem centerMatrix_close_synchronized_of_index_eq {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (comparisonRadius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate)
      (comparisonPositive : 0 < comparisonRadius)
    (rawIndex : Nat)
    (rawIndex_eq : rawIndex =
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.synchronizedSampleIndex data inverseLower
        comparisonRadius
        comparisonPositive)
    (centerTarget : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (centerPositive : 0
      < centerTarget)
    (centerSmall : centerTarget < Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
      comparisonRadius)
    (row column : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq
        (Positivity.centerMatrix
            (Certificate.normalizedData data inverseLower)
            centerTarget centerPositive row column -
          Certificate.synchronizedNormalizedMatrix data
            rawIndex row column) <
      comparisonRadius ^ 2 := by
  subst rawIndex
  exact Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.centerMatrix_close_synchronized data
    inverseLower comparisonRadius
    comparisonPositive centerTarget centerPositive centerSmall row column

/-! ## Tail comparison indices and centre comparison -/

/-- First tail sampler index at which one normalized entry has small enough semantic allowance for the matrix
comparison. -/
@[expose] def tailEntryComparisonStart {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (row column : Fin genus)
      : Nat :=
  let entry :=
    (NormalizedPeriodData.ofScaledInverse data
      certificate.toScaledInverseCertificate).omega row column
  Search.firstQuarterBelow 1 0
    (entry.coherent.accuracyRequest
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius))

/-- Approximation-level tail equivalence, exposing the dropped geometric source directly. -/
@[expose] def tailNormalizedEntry_equivalent_droppedApproximation {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (row column : Fin genus) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Equivalent
      (Sampling.approximation
        ((NormalizedPeriodData.ofScaledInverse data
          certificate.toScaledInverseCertificate).omega row column).name)
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedSynchronizedEntryApproximation data
        certificate
        row column).toApproximation :=
  Equivalent.trans
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailNormalizedEntry_equivalent_dropped data
      certificate row column)
    (by
      simpa only [PeriodMatrix.geometricNamed,
        Coherent.CoherentNamed.ofApproximation] using
        Equivalent.toNamed_sampling
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedSynchronizedEntryApproximation
            data certificate
            row column).toApproximation)

/-- One tail entry's fully computed operational comparison with the dropped raw synchronized normalization stream. -/
@[expose] def tailEntryComparison {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
      (row column : Fin genus) :
    Gaussian.Equivalence.Comparison
      (Sampling.approximation
        ((NormalizedPeriodData.ofScaledInverse data
          certificate.toScaledInverseCertificate).omega row column).name)
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedSynchronizedEntryApproximation data
        certificate
        row column).toApproximation
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparisonStart data certificate
        radius row column) 0
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius) :=

    (tailNormalizedEntry_equivalent_droppedApproximation
    data certificate
    row column).compare
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparisonStart data certificate
      radius row column) 0
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius)
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget_positive positive)

/-- One later tail persistent sampler index shared by every matrix entry. -/
@[expose] def tailPersistentSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius) :
      Nat :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.matrixMax fun row column =>
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparison data certificate radius
      positive row column).leftIndex

/-- One shifted raw synchronized sample index shared by every matrix entry. -/
@[expose] def tailSynchronizedSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius) :
      Nat :=
  Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.matrixMax fun row column =>
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparison data certificate radius
      positive row column).rightIndex

/-- Each dropped-tail entry comparison left index is bounded by the common persistent sample index. -/
theorem tailEntryComparison_left_le_persistentSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparison data certificate radius
      positive row column).leftIndex <=
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailPersistentSampleIndex data certificate
        radius positive := by
  simpa only [Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailPersistentSampleIndex] using
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.le_matrixMax (fun leftRow leftColumn =>
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparison data certificate radius
        positive
        leftRow leftColumn).leftIndex) row column)

/-- Each dropped-tail entry comparison right index is bounded by the common synchronized sample index. -/
theorem tailEntryComparison_right_le_synchronizedSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparison data certificate radius
      positive row column).rightIndex <=
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex data certificate
        radius positive := by
  simpa only [Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex] using
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.le_matrixMax (fun leftRow leftColumn =>
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparison data certificate radius
        positive
        leftRow leftColumn).rightIndex) row column)

/-- Every dropped-tail entry coherence start is bounded by the common persistent sample index. -/
theorem tailEntryComparisonStart_le_persistentSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparisonStart data certificate
      radius row column <=
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailPersistentSampleIndex data certificate
        radius positive :=
  (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparison data certificate radius
    positive row column).left_ge.trans

      (tailEntryComparison_left_le_persistentSampleIndex
      data certificate radius
      positive row column)

/-- The shared tail persistent sampler index has the small semantic allowance requested before the entrywise operational
comparisons. -/
theorem tailPersistentSampleAllowance_lt {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    let entry :=
      (NormalizedPeriodData.ofScaledInverse data
        certificate.toScaledInverseCertificate).omega row column
    entry.coherent.allowance
        (Gaussian.Process.Sampling.stateAt entry.name.process entry.name.state
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailPersistentSampleIndex data
            certificate radius positive)) <
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius := by
  let entry :=
    (NormalizedPeriodData.ofScaledInverse data
      certificate.toScaledInverseCertificate).omega row column
  let start := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparisonStart data
    certificate radius row column
  let persistent := Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailPersistentSampleIndex data
    certificate radius positive
  have requestPositive :
      0 < entry.coherent.accuracyRequest
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius) :=
    entry.coherent.accuracyRequest_pos
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget_positive positive)
  have startAccurate :
      Gaussian.Process.Sampling.refinementTarget start <
        entry.coherent.accuracyRequest
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius) :=
    Search.firstQuarterBelow_accurate 1 (by decide) 0
      (entry.coherent.accuracyRequest
        (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius)) requestPositive
  have startOrder : start <= persistent :=

      tailEntryComparisonStart_le_persistentSampleIndex
      data certificate radius
      positive row column
  have persistentRequestSmall :
      Gaussian.Process.Sampling.refinementTarget persistent <
        entry.coherent.accuracyRequest
          (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius) :=
    (quarterRadius_antitone (by decide) startOrder).trans_lt
      startAccurate
  exact Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt entry.coherent
    entry.name.state persistent (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
      radius)
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget_positive positive)
      persistentRequestSmall

/-- All tail entries can be evaluated at the one maximum retained index while retaining the strict operational
comparison bound, with the raw matrix read at the shifted index. -/
theorem tailPersistentSample_close_synchronized {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (radius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq
        ((Sampling.approximation
            ((NormalizedPeriodData.ofScaledInverse data
              certificate.toScaledInverseCertificate).omega row column).name).sample
            (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailPersistentSampleIndex data
              certificate radius positive) -
          Certificate.synchronizedNormalizedMatrix data
            (certificate.anchor +
              Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex data
                certificate radius positive)
            row column) <
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget radius := by
  have close :=
    (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailEntryComparison data certificate radius
      positive row column).close

        (tailEntryComparison_left_le_persistentSampleIndex
        data certificate radius
        positive row column)

        (tailEntryComparison_right_le_synchronizedSampleIndex
        data certificate
        radius positive row column)
  simpa only [
    Gaussian.Geometric.GeometricApproximation.toApproximation_sample,
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.droppedSynchronizedEntryApproximation_sample]
      using close

/-- A sufficiently fine shared persistent tail request is automatically close to the one computed raw synchronized
matrix at the shifted retained index. -/
theorem tailCenterMatrix_close_synchronized {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (comparisonRadius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate)
      (comparisonPositive : 0 < comparisonRadius)
    (centerTarget : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (centerPositive : 0
      < centerTarget)
    (centerSmall : centerTarget < Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
      comparisonRadius)
    (row column : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq
        (Positivity.centerMatrix
            (NormalizedPeriodData.ofScaledInverse data
              certificate.toScaledInverseCertificate)
            centerTarget centerPositive row column -
          Certificate.synchronizedNormalizedMatrix data
            (certificate.anchor +
              Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex data
                certificate comparisonRadius
                comparisonPositive) row column) <
      comparisonRadius ^ 2 := by
  let normalized :=
    NormalizedPeriodData.ofScaledInverse data
      certificate.toScaledInverseCertificate
  let entry := normalized.omega row column
  let prepared := normalized.prepareOmegaEntry centerTarget centerPositive row column
  let refined := prepared.name
  let center := prepared.center
  let witness := (refined.process.witness refined.state).val
  let persistent :=
    Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailPersistentSampleIndex data certificate
      comparisonRadius
      comparisonPositive
  let persistentValue :=
    (Sampling.approximation entry.name).sample persistent
  let rawIndex :=
    certificate.anchor +
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex data certificate
        comparisonRadius
        comparisonPositive
  let rawValue :=
    Certificate.synchronizedNormalizedMatrix data rawIndex
      row column
  have ballRadiusLt :
      (refined.process.ball refined.state).radiusSq < centerTarget := by
    change (prepared.name.process.ball prepared.name.state).radiusSq < centerTarget
    rewrite [← prepared.ball_eq]
    exact prepared.accurate
  have centerAllowanceLt :
      entry.coherent.allowance refined.state < centerTarget := by
    have contract := normalized.omegaEntry_sharedRequest row column
      centerTarget centerPositive 0
    simpa only [entry, refined, prepared, NormalizedPeriodData.prepareOmegaEntry,
      Gaussian.Table.Request.prepareEntry, NormalizedPeriodData.refinedOmegaEntry] using
      contract.2.1
  have persistentAllowanceLt :
      entry.coherent.allowance
          (Gaussian.Process.Sampling.stateAt entry.name.process entry.name.state
            persistent) < Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
              comparisonRadius := by
    simpa only [entry, persistent, normalized] using
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailPersistentSampleAllowance_lt data
        certificate comparisonRadius
        comparisonPositive row column
  have refinedPossible : entry.name.process.Possible refined.state witness :=
    (refined.process.witness refined.state).property
  have persistentPossible : entry.name.process.Possible
      (Gaussian.Process.Sampling.stateAt entry.name.process entry.name.state
        persistent) persistentValue :=
    Gaussian.Process.Sampling.witnessAt_possible entry.name.process
      entry.name.state persistent
  have witnessInside := entry.name.process.possible_inside refinedPossible
  have centerWitness : Data.Gaussian.Norm.Basic.normSq (center - witness) <=
      (refined.process.ball refined.state).radiusSq := by
    have identity : center - witness = -(witness - center) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im] <;> ring1
    rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
    exact witnessInside
  have semanticClose : Data.Gaussian.Norm.Basic.normSq (witness - persistentValue) <=
      4 * (entry.coherent.allowance refined.state +
        entry.coherent.allowance
          (Gaussian.Process.Sampling.stateAt entry.name.process entry.name.state
            persistent)) :=
    entry.coherent.possible_close refinedPossible persistentPossible
  have semanticSmall : Data.Gaussian.Norm.Basic.normSq (witness - persistentValue) <
      4 * (centerTarget + Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius) :=
    semanticClose.trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_direct centerAllowanceLt
          persistentAllowanceLt))
  have operationalSmall : Data.Gaussian.Norm.Basic.normSq (persistentValue - rawValue) <
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius := by
    simpa only [persistentValue, rawValue, persistent, rawIndex, entry,
      normalized] using
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailPersistentSample_close_synchronized data
        certificate comparisonRadius
        comparisonPositive row column
  have witnessRawSmall : Data.Gaussian.Norm.Basic.normSq (witness - rawValue) <
      2 * (4 * (centerTarget + Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius) +
        Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius) := by
    calc
      Data.Gaussian.Norm.Basic.normSq (witness - rawValue) <=
          2 * (Data.Gaussian.Norm.Basic.normSq (witness - persistentValue) +
            Data.Gaussian.Norm.Basic.normSq (persistentValue - rawValue)) :=
        Data.Gaussian.Norm.Bounds.normSq_sub_le_via witness persistentValue rawValue
      _ < 2 * (4 * (centerTarget + Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius) +
          Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Fraction.Order.Arithmetic.add_lt_add_direct semanticSmall
            operationalSmall)
  have centerRawSmall : Data.Gaussian.Norm.Basic.normSq (center - rawValue) <
      18 * centerTarget + 20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius := by
    calc
      Data.Gaussian.Norm.Basic.normSq (center - rawValue) <=
          2 * (Data.Gaussian.Norm.Basic.normSq (center - witness) + Data.Gaussian.Norm.Basic.normSq
            (witness - rawValue)) :=
        Data.Gaussian.Norm.Bounds.normSq_sub_le_via center witness rawValue
      _ < 2 * (centerTarget +
          2 * (4 * (centerTarget + Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
            comparisonRadius) +
            Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius)) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Fraction.Order.Arithmetic.add_lt_add_direct
            (centerWitness.trans_lt ballRadiusLt) witnessRawSmall)
      _ = 18 * centerTarget +
          20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius :=
            by ring1
  have belowThirtyEight :
      18 * centerTarget + 20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius <
        38 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius :=
          by
    have scaledCenter : 18 * centerTarget <
        18 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        centerSmall
    calc
      18 * centerTarget + 20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius <
          18 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius +
            20 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius
              :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct scaledCenter _
      _ = 38 * Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius :=
        by
        ring1
  have finalSmall := centerRawSmall.trans
    (belowThirtyEight.trans
      (Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.thirtyEight_comparisonTarget_lt_sq
        comparisonPositive))
  have centerReadback : center = normalized.omegaCenter centerTarget centerPositive row column :=
    normalized.prepareOmegaEntry_center centerTarget centerPositive row column
  rw [centerReadback] at finalSmall
  simpa only [rawValue, rawIndex, normalized, Positivity.centerMatrix_apply] using finalSmall

/-- Reindex the tail comparison by a displayed equality for a caller-supplied raw index. -/
theorem tailCenterMatrix_close_synchronized_of_index_eq {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (certificate : PeriodMatrix.ScalarTailSeparationCertificate data.aMatrix)
    (comparisonRadius : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate)
      (comparisonPositive : 0 < comparisonRadius)
    (rawIndex : Nat)
    (rawIndex_eq : rawIndex = certificate.anchor +
      Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex data certificate
        comparisonRadius
        comparisonPositive)
    (centerTarget : Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.Coordinate) (centerPositive : 0
      < centerTarget)
    (centerSmall : centerTarget < Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
      comparisonRadius)
    (row column : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq
        (Positivity.centerMatrix
            (NormalizedPeriodData.ofScaledInverse data
              certificate.toScaledInverseCertificate)
            centerTarget centerPositive row column -
          Certificate.synchronizedNormalizedMatrix data
            rawIndex row column) <
      comparisonRadius ^ 2 := by
  subst rawIndex
  exact Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailCenterMatrix_close_synchronized data
    certificate comparisonRadius
    comparisonPositive centerTarget centerPositive centerSmall row column

end Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization

end
