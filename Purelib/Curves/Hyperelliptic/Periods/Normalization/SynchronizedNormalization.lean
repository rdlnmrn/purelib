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

open Purelib.Algebra.Field

open Purelib.Approximation.Gaussian

open Purelib.Data.Rat.Fraction.Order

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
abbrev Approximation := ApproximationData
/-- Operational equivalence of the two retained Gaussian approximation sequences. -/
abbrev Equivalent := Equivalence.Equivalent
/-- Operational equivalence of the retained named Gaussian quantities. -/
abbrev NamedEquivalent := Equivalence.NamedEquivalent
/-- A Gaussian name retaining its coherent sample realization. -/
abbrev CoherentNamed := Coherent.CoherentNamed
/-- A Gaussian sample sequence with retained geometric convergence bounds. -/
abbrev GeometricApproximation :=
  Geometric.GeometricApproximation

open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- A positive rational lower bound for every displayed sample of one geometric approximation.

It is weaker than whole-ball apartness and is exactly what equal-index finite division requires. -/
structure SampleLower (source :
  GeometricApproximation) where
  /-- The retained uniform squared-norm lower bound for the original denominator samples. -/ lowerSq :
    Coordinate
  /-- The retained denominator lower bound is strictly positive. -/ positive : 0 < lowerSq
  /-- Every original denominator sample satisfies the retained uniform squared-norm lower bound. -/ sample_lower :
    forall index, lowerSq <= Basic.normSq (source.sample index)

constructive_injectivity SampleLower

namespace SampleLower

/-- The positive uniform squared-norm lower bound makes every original denominator sample nonzero. -/
theorem sample_nonzero {source :
  GeometricApproximation}
    (lower : SampleLower source) (index : Nat) :
      source.sample index ≠ 0 := by
  intro zero
  have positive := lower.positive.trans_le (lower.sample_lower index)
  rw [zero, Basic.normSq_zero] at positive
  exact (lt_irrefl _ positive).elim

end SampleLower

/-- Geometric error scale for an equal-index quotient of arbitrary geometric sources. -/
@[expose] def quotientErrorScale (numerator denominator :
  GeometricApproximation)
    (lower : SampleLower denominator) : Coordinate
      :=
  (2 * (numerator.errorScale * denominator.centerBound +
    numerator.centerBound * denominator.errorScale)) /
      (lower.lowerSq * lower.lowerSq)

/-- The retained quotient error scale is nonnegative. -/
theorem quotientErrorScale_nonnegative
    (numerator denominator :
      GeometricApproximation)
    (lower : SampleLower denominator) :
    0 <= quotientErrorScale numerator
      denominator lower := by
  unfold quotientErrorScale
  exact Field.div_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Arithmetic.mul_nonneg_direct
          numerator.errorScale_nonneg denominator.centerBound_nonneg)
        (Arithmetic.mul_nonneg_direct
          numerator.centerBound_nonneg denominator.errorScale_nonneg)))
    (Arithmetic.mul_nonneg_direct lower.positive.le
      lower.positive.le)

/-- Equal-index finite quotients of geometric Gaussian-rational samples. -/
@[expose] def quotientApproximation (numerator denominator :
  GeometricApproximation)
    (lower : SampleLower denominator) :
      GeometricApproximation where
  sample index := numerator.sample index / denominator.sample index
  errorScale := quotientErrorScale numerator
    denominator lower
  errorScale_nonneg :=
    quotientErrorScale_nonnegative numerator
    denominator lower
  later_close := by
    intro earlier later order
    have numeratorMovement := numerator.later_close order
    have denominatorMovementForward := denominator.later_close order
    have denominatorMovement :
        Basic.normSq (denominator.sample earlier - denominator.sample later) <=
          quarterRadius denominator.errorScale earlier := by
      have identity : denominator.sample earlier - denominator.sample later =
          -(denominator.sample later - denominator.sample earlier) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
            Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
      rw [identity, Basic.normSq_neg]
      exact denominatorMovementForward
    have quotientBound :=
      Quotient.IntegrationQuotientVariation.normSq_div_sub_div_le
        lower.positive
        (leftNumerator := numerator.sample later)
        (rightNumerator := numerator.sample earlier)
        (leftDenominator := denominator.sample later)
        (rightDenominator := denominator.sample earlier)
        (numeratorSlope := (1 : Coordinate))
        (numeratorBound := numerator.centerBound)
        (denominatorBound := denominator.centerBound)
        (pointMovement :=
          quarterRadius numerator.errorScale earlier)
        (rootMovement :=
          quarterRadius denominator.errorScale earlier)
        (by
            simpa only [Fraction.Field.one_mul]
              using numeratorMovement)
        (numerator.sample_bounded earlier)
        (denominator.sample_bounded earlier)
        denominatorMovement
        (lower.sample_lower later) (lower.sample_lower earlier)
    calc
      Basic.normSq (numerator.sample later / denominator.sample later -
          numerator.sample earlier / denominator.sample earlier) <=
        Quotient.quotientBound
          1 numerator.centerBound denominator.centerBound lower.lowerSq
          (quarterRadius numerator.errorScale earlier)
          (quarterRadius denominator.errorScale earlier) :=
        quotientBound
      _ = quarterRadius
          (quotientErrorScale numerator denominator
            lower) earlier := by
        rw [quarterRadius_eq_mul_pow,
          quarterRadius_eq_mul_pow,
          quarterRadius_eq_mul_pow]
        unfold Quotient.quotientBound
          quotientErrorScale
        let geometric : Coordinate := (1 / 4 :
          Coordinate) ^ earlier
        change
          (2 * (1 * (numerator.errorScale * geometric) *
              denominator.centerBound +
            numerator.centerBound * (denominator.errorScale * geometric))) /
              (lower.lowerSq * lower.lowerSq) =
            ((2 * (numerator.errorScale * denominator.centerBound +
                numerator.centerBound * denominator.errorScale)) /
              (lower.lowerSq * lower.lowerSq)) * geometric
        rw [ExplicitField.div_eq_mul_inv,
          ExplicitField.div_eq_mul_inv]
        ring1
  centerBound := numerator.centerBound / lower.lowerSq
  centerBound_nonneg := Field.div_nonneg_direct
    numerator.centerBound_nonneg lower.positive.le
  sample_bounded := by
    intro index
    rw [Data.Gaussian.Field.normSq_div _ _ (lower.sample_nonzero index)]
    calc
      Basic.normSq (numerator.sample index) / Basic.normSq
        (denominator.sample index) <=
          Basic.normSq (numerator.sample index) / lower.lowerSq :=
        Field.div_le_div_of_nonneg_left_direct
          (Basic.normSq_nonneg _) lower.positive (lower.sample_lower index)
      _ <= numerator.centerBound / lower.lowerSq := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        exact Arithmetic.mul_le_mul_of_nonneg_right_direct
          (numerator.sample_bounded index)
          (Field.inv_pos_direct lower.positive).le

/-- Each quotient sample uses the original numerator and denominator at the same index. -/
@[simp] theorem quotientApproximation_sample
    (numerator denominator :
      GeometricApproximation)
    (lower : SampleLower denominator) (index : Nat)
      :
    (quotientApproximation numerator denominator
      lower).sample index =
      numerator.sample index / denominator.sample index :=
  rfl

/-- One positive lower bound shared by two equal-index denominator streams. -/
@[expose] def commonLower {first second :
  GeometricApproximation}
    (firstLower : SampleLower first) (secondLower :
      SampleLower second) :
    Coordinate :=
  min firstLower.lowerSq secondLower.lowerSq

/-- The minimum of the two retained positive denominator bounds is positive. -/
theorem commonLower_positive {first second :
  GeometricApproximation}
    (firstLower : SampleLower first) (secondLower :
      SampleLower second) :
    0 < commonLower firstLower secondLower :=
  Basic.lt_min firstLower.positive secondLower.positive

/-- Sensitivity coefficient for replacing both operands of a finite equal-index quotient. -/
@[expose] def quotientComparisonCoefficient
    (secondNumerator secondDenominator :
      GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator) :
      Coordinate :=
  Quotient.comparisonCoefficient
    secondNumerator.centerBound secondDenominator.centerBound
    (commonLower firstLower secondLower)

/-- The quotient comparison coefficient is nonnegative. -/
theorem quotientComparisonCoefficient_nonnegative
    (secondNumerator secondDenominator :
      GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator) :
    0 <= quotientComparisonCoefficient
      secondNumerator secondDenominator
      firstLower secondLower :=
  Quotient.comparisonCoefficient_nonnegative
    secondNumerator.centerBound_nonneg secondDenominator.centerBound_nonneg
    (commonLower_positive firstLower secondLower).le

/-- Divide the positive target by one plus the quotient comparison coefficient. -/
@[expose] def quotientComparisonTarget
    (secondNumerator secondDenominator :
      GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator)
    (target : Coordinate) : Coordinate :=
  Quotient.comparisonTarget
    secondNumerator.centerBound secondDenominator.centerBound
    (commonLower firstLower secondLower) target

/-- The adjusted quotient comparison target is positive. -/
theorem quotientComparisonTarget_positive
    (secondNumerator secondDenominator :
      GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator)
    {target : Coordinate} (positive : 0 < target) :
    0 < quotientComparisonTarget secondNumerator
      secondDenominator
      firstLower secondLower target :=
  Quotient.comparisonTarget_positive
    secondNumerator.centerBound_nonneg secondDenominator.centerBound_nonneg
    (commonLower_positive firstLower secondLower).le positive

/-- The adjusted target times the comparison coefficient is strictly below the original target. -/
theorem quotientComparisonTarget_budget_lt
    (secondNumerator secondDenominator :
      GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator)
    {target : Coordinate} (positive : 0 < target) :
    quotientComparisonTarget secondNumerator
      secondDenominator
        firstLower secondLower target *
      quotientComparisonCoefficient secondNumerator
        secondDenominator
        firstLower secondLower < target :=
  Quotient.comparisonTarget_budget_lt
    secondNumerator.centerBound_nonneg secondDenominator.centerBound_nonneg
    (commonLower_positive firstLower secondLower).le positive

/-- Equal-index geometric quotients respect operational equality of both sources, using only a displayed positive sample
lower bound on each denominator. -/
@[expose] def quotientApproximation_respects
    (firstNumerator secondNumerator firstDenominator secondDenominator :
      GeometricApproximation)
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator)
    (numeratorEquivalent : Equivalent
      firstNumerator.toApproximation
      secondNumerator.toApproximation)
    (denominatorEquivalent : Equivalent
      firstDenominator.toApproximation
      secondDenominator.toApproximation) :
    Equivalent
      (quotientApproximation firstNumerator
        firstDenominator firstLower).toApproximation
      (quotientApproximation secondNumerator
        secondDenominator secondLower).toApproximation where
  compare := by
    intro firstStart secondStart target positive
    let inputTarget := quotientComparisonTarget
      secondNumerator
      secondDenominator firstLower secondLower target
    have inputPositive : 0 < inputTarget :=
      quotientComparisonTarget_positive
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
        left_ge := numeratorComparison.left_ge.trans (Data.Nat.Order.le_max_left _ _)
        right_ge := numeratorComparison.right_ge.trans (Data.Nat.Order.le_max_left _ _)
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have numeratorClose := numeratorComparison.close
            ((Data.Nat.Order.le_max_left numeratorComparison.leftIndex
              denominatorComparison.leftIndex).trans firstOrder)
            ((Data.Nat.Order.le_max_left numeratorComparison.rightIndex
              denominatorComparison.rightIndex).trans secondOrder)
          have numeratorClose' :
              Basic.normSq (firstNumerator.sample firstLater -
                secondNumerator.sample secondLater) < inputTarget := by
            simpa only [
              GeometricApproximation.toApproximation_sample]
              using numeratorClose
          have denominatorCloseForward := denominatorComparison.close
            ((Data.Nat.Order.le_max_right numeratorComparison.leftIndex
              denominatorComparison.leftIndex).trans firstOrder)
            ((Data.Nat.Order.le_max_right numeratorComparison.rightIndex
              denominatorComparison.rightIndex).trans secondOrder)
          have denominatorCloseForward' :
              Basic.normSq (firstDenominator.sample firstLater -
                secondDenominator.sample secondLater) < inputTarget := by
            simpa only [
              GeometricApproximation.toApproximation_sample]
              using denominatorCloseForward
          have denominatorClose :
              Basic.normSq (secondDenominator.sample secondLater -
                  firstDenominator.sample firstLater) <= inputTarget := by
            have identity :
                secondDenominator.sample secondLater -
                    firstDenominator.sample firstLater =
                  -(firstDenominator.sample firstLater -
                    secondDenominator.sample secondLater) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                  Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
            rw [identity, Basic.normSq_neg]
            exact denominatorCloseForward'.le
          have commonFirst : commonLower firstLower
            secondLower <=
              Basic.normSq (firstDenominator.sample firstLater) :=
            (Basic.min_le_left _ _).trans (firstLower.sample_lower firstLater)
          have commonSecond : commonLower
            firstLower secondLower <=
              Basic.normSq (secondDenominator.sample secondLater) :=
            (Basic.min_le_right _ _).trans (secondLower.sample_lower secondLater)
          have quotientBound :=
            Quotient.IntegrationQuotientVariation.normSq_div_sub_div_le
              (commonLower_positive firstLower
                secondLower)
              (leftNumerator := firstNumerator.sample firstLater)
              (rightNumerator := secondNumerator.sample secondLater)
              (leftDenominator := firstDenominator.sample firstLater)
              (rightDenominator := secondDenominator.sample secondLater)
              (numeratorSlope := (1 : Coordinate))
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
          change Basic.normSq
              (firstNumerator.sample firstLater /
                  firstDenominator.sample firstLater -
                secondNumerator.sample secondLater /
                  secondDenominator.sample secondLater) < target
          calc
            Basic.normSq
                (firstNumerator.sample firstLater /
                    firstDenominator.sample firstLater -
                  secondNumerator.sample secondLater /
                    secondDenominator.sample secondLater) <=
              Quotient.quotientBound
                1 secondNumerator.centerBound secondDenominator.centerBound
                (commonLower firstLower
                  secondLower) inputTarget inputTarget :=
              quotientBound
            _ < target :=
              Quotient.comparison_budget_lt secondNumerator.centerBound_nonneg
                secondDenominator.centerBound_nonneg
                (commonLower_positive firstLower secondLower).le positive }

/-! ## Synchronized normalization sources -/

/-- Equal-index numerator `adj(A)B` underlying one normalized period entry. -/
@[expose] def normalizationNumerator {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    GeometricApproximation :=
  geometricProductEntry (canonicalScaledInverse data.aMatrix).inverse
    (geometricMatrixOfNamed data.bMatrix) row column

/-- Equal-index fraction-free inverse scalar underlying normalization. -/
@[expose] def normalizationDenominator {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) : GeometricApproximation :=
  (canonicalScaledInverse data.aMatrix).scalar

/-- The finite inverse-separation certificate is precisely a sample lower bound for the synchronized denominator stream.
-/
@[expose] def normalizationDenominatorLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    SampleLower
      (normalizationDenominator data) where
  lowerSq := inverseLower.lowerSq
  positive := inverseLower.positive
  sample_lower := inverseLower.sample_lower

/-- One raw equal-index normalized period entry, now carrying its own geometric refinement and boundedness data. -/
@[expose] def synchronizedEntryApproximation {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) : GeometricApproximation :=
  quotientApproximation
    (normalizationNumerator data row column)
    (normalizationDenominator data)
    (normalizationDenominatorLower inverseLower)

/-- The raw equal-index quotient of the canonical numerator and denominator is literally the synchronized normalized
matrix entry. -/
theorem synchronizedEntry_core {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column : Fin genus) (index : Nat) :
    (normalizationNumerator data row
      column).sample index /
      (normalizationDenominator data).sample index
        =
      Certificate.synchronizedNormalizedMatrix data index
        row column := by
  let aSource := geometricMatrixOfNamed data.aMatrix
  let bSource := geometricMatrixOfNamed data.bMatrix
  let computed := canonicalScaledInverse data.aMatrix
  let sampledA := sampledMatrix data.aMatrix index
  let inverse :=
    PivotedScaledInverse.completeScaledInverse sampledA
  have inverseSamples :=
    PivotedScaledInverse.completeApproximation_sample aSource index
  have aSourceSample :
      Matrix.sampleMatrix aSource index =
        sampledA := by
    exact sample_geometricMatrixOfNamed data.aMatrix index
  rw [aSourceSample] at inverseSamples
  have computedScalarSample : computed.scalar.sample index = inverse.scalar := by
    simpa only [computed, canonicalScaledInverse, aSource] using inverseSamples.1
  have computedInverseSample :
      Matrix.sampleMatrix computed.inverse
          index = inverse.inverse := by
    simpa only [computed, canonicalScaledInverse, aSource] using inverseSamples.2
  have bSourceSample :
      Matrix.sampleMatrix bSource index =
        sampledMatrix data.bMatrix index := by
    exact sample_geometricMatrixOfNamed data.bMatrix index
  rw [show (normalizationNumerator data row
    column).sample index =
      Multiplication.mul inverse.inverse
        (sampledMatrix data.bMatrix index) row column by
    unfold normalizationNumerator
    rw [geometricProductEntry_sample]
    change Multiplication.mul
        (Matrix.sampleMatrix computed.inverse
          index)
        (Matrix.sampleMatrix bSource index)
          row column = _
    rw [bSourceSample, computedInverseSample]]
  rw [show (normalizationDenominator data).sample
    index = inverse.scalar by
    exact computedScalarSample]
  unfold Certificate.synchronizedNormalizedMatrix
    Certificate.synchronizedScaledInverse
  rw [Energy.divideGaussianMatrix_apply]

/-- The geometric normalization source displays literally the raw matrix entry used by the finite energy transport
argument at every index. -/
theorem synchronizedEntryApproximation_sample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) (index : Nat) :
    (synchronizedEntryApproximation data
      inverseLower row column).sample index =
      Certificate.synchronizedNormalizedMatrix data index
        row column := by
  rw [show (synchronizedEntryApproximation data
    inverseLower row column).sample
      index =
        (normalizationNumerator data row
          column).sample index /
          (normalizationDenominator data).sample
            index by rfl]
  exact synchronizedEntry_core data row column
    index

/-! ## Dropped sources for a certified tail anchor -/

/-- One anchor value and the approximation's later-movement bound control the squared norm of every retained sample. -/
private theorem drop_sample_normSq_lower (source :
  GeometricApproximation)
    (anchor index : Nat) :
    Basic.normSq (source.sample anchor) / 2 -
        quarterRadius source.errorScale anchor <=
      Basic.normSq
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
      Basic.normSq
          (source.sample anchor - source.sample (anchor + index)) <=
        quarterRadius source.errorScale anchor := by
    rw [reverseDifference, Basic.normSq_neg]
    exact movementForward
  have triangle :=
    Bounds.half_normSq_sub_le_normSq_sub
      (source.sample anchor) (source.sample (anchor + index))
  apply (Arithmetic.sub_le_iff_le_add_direct).2
  calc
    Basic.normSq (source.sample anchor) / 2 <=
        Basic.normSq
            (source.sample anchor - source.sample (anchor + index)) +
          Basic.normSq
            (source.sample (anchor + index)) :=
      (Arithmetic.sub_le_iff_le_add_direct).1 triangle
    _ <= quarterRadius source.errorScale anchor +
        Basic.normSq
          (source.sample (anchor + index)) :=
      Arithmetic.add_le_add_right_direct movement _
    _ = Basic.normSq
          (source.sample (anchor + index)) +
        quarterRadius source.errorScale anchor :=
      Fraction.Field.add_comm _ _

/-- The certified tail anchor is a uniform sample lower bound for the dropped canonical denominator stream. -/
@[expose] def tailDenominatorLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : ScalarTailSeparationCertificate data.aMatrix) :
    SampleLower
      ((normalizationDenominator data).drop
      certificate.anchor) where
  lowerSq := certificate.lowerSq
  positive := certificate.lowerSq_positive
  sample_lower := by
    intro index
    exact drop_sample_normSq_lower
      (normalizationDenominator data)
      certificate.anchor index

/-- One dropped equal-index normalized entry.

Its samples are the raw synchronized matrix at the shifted retained index. -/
@[expose] def droppedSynchronizedEntryApproximation {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (row column : Fin genus) : GeometricApproximation :=
  quotientApproximation
    ((normalizationNumerator data row column).drop
      certificate.anchor)
    ((normalizationDenominator data).drop
      certificate.anchor)
    (tailDenominatorLower certificate)

/-- The dropped normalization source displays the raw matrix entry at the shifted retained index. -/
theorem droppedSynchronizedEntryApproximation_sample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (row column : Fin genus) (index : Nat) :
    (droppedSynchronizedEntryApproximation data
      certificate row column).sample
        index =
      Certificate.synchronizedNormalizedMatrix data
        (certificate.anchor + index) row column := by
  change (normalizationNumerator data row
    column).sample
        (certificate.anchor + index) /
      (normalizationDenominator data).sample
        (certificate.anchor + index) = _
  exact synchronizedEntry_core data row column
    (certificate.anchor + index)

/-- Persistent fraction-free matrix multiplication realizes the canonical equal-index `adj(A)B` numerator for any scaled
inverse presentation, since the adjugate is presentation-independent. -/
@[expose] def normalizationNumerator_equivalent_scaled {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverse : ScaledInverseCertificate data.aMatrix) (row column : Fin genus) :
    NamedEquivalent
      (matrixMul inverse.adjugate data.bMatrix row column).name
      (geometricNamed
        (normalizationNumerator data row
        column)).name := by
  let computed := canonicalScaledInverse data.aMatrix
  let bSource := geometricMatrixOfNamed data.bMatrix
  have equivalent := matrixMul_equivalent_geometricProduct
    inverse.adjugate data.bMatrix computed.inverse bSource
    (fun leftRow leftColumn => by
      simpa only [adjugate,
        canonicalAdjugate_apply, computed] using
        NamedEquivalent.refl
          (geometricNamed (computed.inverse leftRow leftColumn)).name)
    (fun rightRow rightColumn => by
      simpa only [bSource, geometricMatrixOfNamed_apply] using
        named_equivalent_geometricOfNamed
          (data.bMatrix rightRow rightColumn))
    row column
  simpa only [computed, bSource,
    normalizationNumerator] using equivalent

/-- Canonical sampler of one prepared scalar name. -/
@[expose] def preparedScalarSource {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) : GeometricApproximation :=
  GeometricApproximation.ofNamed
    inverse.scalar.name

/-- Whole-ball apartness of the prepared scalar supplies the weaker sample lower bound needed by its equal-index
quotient. -/
@[expose] def preparedScalarLower {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) :
    SampleLower
      (preparedScalarSource inverse) where
  lowerSq := inverse.scalarApart.certificate.lowerSq
  positive := inverse.scalarApart.certificate.positive
  sample_lower := by
    intro index
    exact Apart.Sampling.sampled_lower inverse.scalar
      inverse.scalarApart index

/-- Equal-index reciprocal using the canonical sampler of the prepared stateful denominator. -/
@[expose] def preparedScalarReciprocal {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) : GeometricApproximation :=
  quotientApproximation
    (GeometricApproximation.ofNamed
      (Coherence.exact 1).name)
    (preparedScalarSource inverse)
    (preparedScalarLower inverse)

/-- Equal-index reciprocal of the anchor-dropped raw scalar stream. -/
@[expose] def droppedRawReciprocal {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : ScalarTailSeparationCertificate data.aMatrix) :
    GeometricApproximation :=
  quotientApproximation
    (GeometricApproximation.exact 1)
    ((normalizationDenominator data).drop
      certificate.anchor)
    (tailDenominatorLower certificate)

/-- Prepared scalar samples are operationally the anchor-dropped raw scalar samples. -/
@[expose] def preparedScalar_equivalent_droppedRaw {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : ScalarTailSeparationCertificate data.aMatrix) :
    Equivalent
      (preparedScalarSource
        certificate.toScaledInverseCertificate).toApproximation
      ((normalizationDenominator data).drop
        certificate.anchor).toApproximation := by
  let inverse := certificate.toScaledInverseCertificate
  let raw := (normalizationDenominator data).drop
    certificate.anchor
  let prepared := preparedScalarSource inverse
  have preparedToSampler : Equivalent
    prepared.toApproximation
      (Sampling.approximation inverse.scalar.name) :=
    Equivalence.approximationEquivalentOfSamplesEq _ _ (by intro index; rfl)
  have preparedToWrappedRaw : Equivalent
      (Sampling.approximation inverse.scalar.name)
      (Sampling.approximation (geometricNamed raw).name) := by
    change NamedEquivalent inverse.scalar.name
      (geometricNamed raw).name
    exact NamedEquivalent.trans
      (NamedEquivalent.symm inverse.canonicalScalarEquivalent)
      (by
        simpa only [inverse, raw,
          normalizationDenominator,
          ScalarTailSeparationCertificate.scalarSource] using
          certificate.sourceEquivalent)
  have wrappedRawToRaw : Equivalent
      (Sampling.approximation (geometricNamed raw).name)
      raw.toApproximation := by
    simpa only [geometricNamed,
      ofApproximation] using
      Equivalent.toNamed_sampling raw.toApproximation
  change Equivalent prepared.toApproximation
    raw.toApproximation
  exact Equivalent.trans preparedToSampler
    (Equivalent.trans preparedToWrappedRaw
      wrappedRawToRaw)

/-! ## Operational equivalence with persistent normalization -/

/-- Every sample of the geometric realization of an exact Gaussian value is that value. -/
@[simp] theorem geometricOfExact_sample (value :
  Gaussian) (index : Nat) :
    (GeometricApproximation.ofNamed
      (Coherence.exact value).name).sample index =
      value := by
  rfl

/-- Canonical sampler of the prepared denominator used by stateful division. -/
@[expose] def preparedDenominatorSource {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    GeometricApproximation :=
  GeometricApproximation.ofNamed
    inverseLower.toScaledInverseCertificate.scalar.name

/-- Whole-ball apartness of the prepared scalar supplies the weaker sample lower bound needed by its equal-index
quotient. -/
@[expose] def preparedDenominatorLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    SampleLower
      (preparedDenominatorSource inverseLower)
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
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    GeometricApproximation :=
  quotientApproximation
    (GeometricApproximation.ofNamed
      (Coherence.exact 1).name)
    (preparedDenominatorSource inverseLower)
    (preparedDenominatorLower inverseLower)

/-- Equal-index reciprocal using the unprepared raw scalar stream. -/
@[expose] def rawReciprocalApproximation {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    GeometricApproximation :=
  quotientApproximation
    (GeometricApproximation.exact 1)
    (normalizationDenominator data)
    (normalizationDenominatorLower inverseLower)

/-- Prepared scalar samples are operationally the raw fraction-free scalar samples from which apartification was
constructed. -/
@[expose] def preparedDenominator_equivalent_raw {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    Equivalent
      (preparedDenominatorSource
      inverseLower).toApproximation
      (normalizationDenominator
        data).toApproximation := by
  let inverse := inverseLower.toScaledInverseCertificate
  let raw := normalizationDenominator data
  let prepared := preparedDenominatorSource
    inverseLower
  have preparedToSampler : Equivalent
    prepared.toApproximation
      (Sampling.approximation inverse.scalar.name) :=
    Equivalence.approximationEquivalentOfSamplesEq _ _
      (by intro index; rfl)
  have preparedToWrappedRaw : Equivalent
      (Sampling.approximation inverse.scalar.name)
      (Sampling.approximation
        (geometricNamed raw).name) := by
    change NamedEquivalent inverse.scalar.name
      (geometricNamed raw).name
    simpa only [inverse, raw,
      normalizationDenominator,
      canonicalInverseScalar] using
      NamedEquivalent.symm
        inverse.canonicalScalarEquivalent
  have wrappedRawToRaw : Equivalent
      (Sampling.approximation (geometricNamed raw).name)
      raw.toApproximation := by
    simpa only [geometricNamed,
      ofApproximation] using
      Equivalent.toNamed_sampling
        raw.toApproximation
  change Equivalent prepared.toApproximation
    raw.toApproximation
  exact Equivalent.trans preparedToSampler
    (Equivalent.trans preparedToWrappedRaw
      wrappedRawToRaw)

/-- The exact-one sampler and the constant geometric one stream have the same displayed rational sample at every index.
-/
@[expose] def preparedOne_equivalent_rawOne :
  Equivalent
    (GeometricApproximation.ofNamed
      (Coherence.exact 1).name).toApproximation
    (GeometricApproximation.exact
      1).toApproximation :=
  Equivalence.approximationEquivalentOfSamplesEq _ _
    (by intro index; exact geometricOfExact_sample 1 index)

/-- Replacing the apartified denominator sampler by its raw synchronized source preserves the reciprocal's finite
operational value. -/
@[expose] def preparedReciprocal_equivalent_raw {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    Equivalent
      (preparedReciprocalApproximation
      inverseLower).toApproximation
      (rawReciprocalApproximation
        inverseLower).toApproximation := by
  exact quotientApproximation_respects _ _ _ _
    (preparedDenominatorLower inverseLower)
    (normalizationDenominatorLower inverseLower)
    preparedOne_equivalent_rawOne
    (preparedDenominator_equivalent_raw
      inverseLower)

/-- The stateful reciprocal used by persistent normalization is operationally the equal-index reciprocal of the raw
fraction-free scalar stream. -/
@[expose] def inverseScalar_equivalent_rawReciprocal {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    NamedEquivalent
      (inverseScalar inverseLower.toScaledInverseCertificate).name
      (geometricNamed
        (rawReciprocalApproximation
        inverseLower)).name := by
  let inverse := inverseLower.toScaledInverseCertificate
  let one := Coherence.exact 1
  let sampled :=
    Sample.sampledQuotientApproximation one
      inverse.scalar inverse.scalarApart
  let prepared := preparedReciprocalApproximation
    inverseLower
  let raw := rawReciprocalApproximation
    inverseLower
  have actualToSampled : NamedEquivalent
      (div one inverse.scalar
        inverse.scalarApart).name sampled.toNamed := by
    exact Equivalence.coherentDiv_toSampled
      one inverse.scalar inverse.scalarApart
  have sampledToPreparedApprox : Equivalent sampled
    prepared.toApproximation :=
    Equivalence.approximationEquivalentOfSamplesEq _ _
      (by intro index; rfl)
  have sampledToPrepared : NamedEquivalent
    sampled.toNamed
      (geometricNamed prepared).name := by
    simpa only [geometricNamed,
      ofApproximation] using
      Equivalence.approximationEquivalent_toNamed
        sampledToPreparedApprox
  have preparedToRaw : NamedEquivalent
    (geometricNamed prepared).name
      (geometricNamed raw).name := by
    simpa only [geometricNamed,
      ofApproximation] using
      Equivalence.approximationEquivalent_toNamed
        (preparedReciprocal_equivalent_raw
          inverseLower)
  change NamedEquivalent
    (div one inverse.scalar
      inverse.scalarApart).name (geometricNamed raw).name
  exact NamedEquivalent.trans actualToSampled
    (NamedEquivalent.trans sampledToPrepared
      preparedToRaw)

/-- Replacing the apartified denominator sampler by its anchor-dropped raw source preserves the reciprocal's finite
operational value. -/
@[expose] def preparedScalarReciprocal_equivalent_droppedRaw {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : ScalarTailSeparationCertificate data.aMatrix) :
    Equivalent
      (preparedScalarReciprocal
        certificate.toScaledInverseCertificate).toApproximation
      (droppedRawReciprocal
        certificate).toApproximation :=
  quotientApproximation_respects _ _ _ _
    (preparedScalarLower
      certificate.toScaledInverseCertificate)
    (tailDenominatorLower certificate)
    preparedOne_equivalent_rawOne
    (preparedScalar_equivalent_droppedRaw
      certificate)

/-- The stateful reciprocal of a certified tail is operationally the equal-index reciprocal of the anchor-dropped raw
scalar stream. -/
@[expose] def tailInverseScalar_equivalent_droppedRawReciprocal {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : ScalarTailSeparationCertificate data.aMatrix) :
    NamedEquivalent
      (inverseScalar certificate.toScaledInverseCertificate).name
      (geometricNamed
        (droppedRawReciprocal certificate)).name :=
        by
  let inverse := certificate.toScaledInverseCertificate
  let one := Coherence.exact 1
  let sampled :=
    Sample.sampledQuotientApproximation one
      inverse.scalar inverse.scalarApart
  let prepared := preparedScalarReciprocal inverse
  let raw := droppedRawReciprocal certificate
  have actualToSampled : NamedEquivalent
      (div one inverse.scalar
        inverse.scalarApart).name sampled.toNamed :=
    Equivalence.coherentDiv_toSampled
      one inverse.scalar inverse.scalarApart
  have sampledToPreparedApprox : Equivalent sampled
    prepared.toApproximation :=
    Equivalence.approximationEquivalentOfSamplesEq _ _ (by intro index; rfl)
  have sampledToPrepared : NamedEquivalent
    sampled.toNamed
      (geometricNamed prepared).name := by
    simpa only [geometricNamed,
      ofApproximation] using
      Equivalence.approximationEquivalent_toNamed
        sampledToPreparedApprox
  have preparedToRaw : NamedEquivalent
    (geometricNamed prepared).name
      (geometricNamed raw).name := by
    simpa only [geometricNamed,
      ofApproximation] using
      Equivalence.approximationEquivalent_toNamed

          (preparedScalarReciprocal_equivalent_droppedRaw
          certificate)
  change NamedEquivalent
    (div one inverse.scalar
      inverse.scalarApart).name (geometricNamed raw).name
  exact NamedEquivalent.trans actualToSampled
    (NamedEquivalent.trans sampledToPrepared
      preparedToRaw)

/-- A tail-normalized period entry is operationally equivalent to the dropped geometric approximation whose samples are
the raw synchronized matrix at the shifted retained index. -/
@[expose] def tailNormalizedEntry_equivalent_dropped {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (row column : Fin genus) :
    NamedEquivalent
      ((NormalizedPeriodData.ofScaledInverse data
        certificate.toScaledInverseCertificate).omega row column).name
      (geometricNamed
        (droppedSynchronizedEntryApproximation data
          certificate
          row column)).name := by
  let inverse := certificate.toScaledInverseCertificate
  let numerator := matrixMul inverse.adjugate data.bMatrix row column
  let reciprocal := inverseScalar inverse
  let numeratorSource :=
    (normalizationNumerator data row column).drop
      certificate.anchor
  let reciprocalSource := droppedRawReciprocal
    certificate
  let productSource :=
    GeometricApproximation.mul
      numeratorSource reciprocalSource
  let synchronizedSource :=
    droppedSynchronizedEntryApproximation data
      certificate row column
  have numeratorEquivalent : NamedEquivalent
    numerator.name
      (geometricNamed numeratorSource).name := by
    simpa only [numerator, numeratorSource, inverse] using
      NamedEquivalent.trans
        (normalizationNumerator_equivalent_scaled
          inverse row column)
        (geometricNamed_drop_equivalent
          (normalizationNumerator data row column)
            certificate.anchor)
  have reciprocalEquivalent : NamedEquivalent
    reciprocal.name
      (geometricNamed reciprocalSource).name := by
    simpa only [reciprocal, reciprocalSource, inverse] using

        tailInverseScalar_equivalent_droppedRawReciprocal
        certificate
  have productEquivalent : NamedEquivalent
      (mul numerator reciprocal).name
      (geometricNamed productSource).name :=
    coherentMul_equivalent_geometricMul numerator reciprocal
      numeratorSource reciprocalSource numeratorEquivalent reciprocalEquivalent
  have productSamples : forall index, productSource.sample index =
      synchronizedSource.sample index := by
    intro index
    change
      (normalizationNumerator data row
        column).sample
          (certificate.anchor + index) *
          ((1 : Gaussian) /
            (normalizationDenominator data).sample
              (certificate.anchor + index)) =
        (normalizationNumerator data row
          column).sample
            (certificate.anchor + index) /
          (normalizationDenominator data).sample
            (certificate.anchor + index)
    rw [ExplicitField.div_eq_mul_inv,
      ExplicitField.div_eq_mul_inv]
    ring1
  have productToSynchronized : NamedEquivalent
      (geometricNamed productSource).name
      (geometricNamed synchronizedSource).name :=
    geometricNamed_equivalent_of_samples productSource synchronizedSource
      productSamples
  have result := NamedEquivalent.trans
    productEquivalent productToSynchronized
  simpa only [reciprocalSource, numeratorSource, synchronizedSource,
    NormalizedPeriodData.ofScaledInverse,
    NormalizedPeriodData.omega, normalize_apply, numerator, reciprocal,
    inverse] using result

/-- Persistent fraction-free matrix multiplication realizes the same equal-index `adj(A)B` numerator used by
synchronized normalization. -/
@[expose] def normalizationNumerator_equivalent {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) :
    NamedEquivalent
      (matrixMul inverseLower.toScaledInverseCertificate.adjugate
        data.bMatrix row column).name
      (geometricNamed
        (normalizationNumerator data row
        column)).name := by
  let inverse := inverseLower.toScaledInverseCertificate
  let computed := canonicalScaledInverse data.aMatrix
  let bSource := geometricMatrixOfNamed data.bMatrix
  have equivalent := matrixMul_equivalent_geometricProduct
    inverse.adjugate data.bMatrix computed.inverse bSource
    (fun leftRow leftColumn => by
      simpa only [inverse, adjugate,
        canonicalAdjugate_apply, computed] using
        NamedEquivalent.refl
          (geometricNamed (computed.inverse leftRow leftColumn)).name)
    (fun rightRow rightColumn => by
      simpa only [bSource, geometricMatrixOfNamed_apply] using
        named_equivalent_geometricOfNamed
          (data.bMatrix rightRow rightColumn))
    row column
  simpa only [inverse, computed, bSource,
    normalizationNumerator] using
    equivalent

/-- Every persistent normalized period entry is operationally equivalent to the geometric approximation whose index-`n`
sample is literally the raw synchronized normalized matrix at index `n`. -/
@[expose] def normalizedEntry_equivalent_synchronized {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) :
    NamedEquivalent
      ((Certificate.normalizedData data inverseLower).omega
        row column).name
      (geometricNamed
        (synchronizedEntryApproximation data
          inverseLower row column)).name := by
  let inverse := inverseLower.toScaledInverseCertificate
  let numerator := matrixMul inverse.adjugate data.bMatrix row column
  let reciprocal := inverseScalar inverse
  let numeratorSource := normalizationNumerator
    data row column
  let reciprocalSource :=
    rawReciprocalApproximation inverseLower
  let productSource :=
    GeometricApproximation.mul
      numeratorSource reciprocalSource
  let synchronizedSource :=
    synchronizedEntryApproximation data
      inverseLower row column
  have productEquivalent : NamedEquivalent
      (mul numerator reciprocal).name
      (geometricNamed productSource).name := by
    exact coherentMul_equivalent_geometricMul numerator reciprocal
      numeratorSource reciprocalSource
      (by
        simpa only [numerator, inverse] using
          normalizationNumerator_equivalent
            inverseLower row column)
      (by
        simpa only [reciprocal, reciprocalSource, inverse] using
          inverseScalar_equivalent_rawReciprocal
            inverseLower)
  have productSamples : forall index, productSource.sample index =
      synchronizedSource.sample index := by
    intro index
    change
      (normalizationNumerator data row
        column).sample index *
          ((1 : Gaussian) /
            (normalizationDenominator data).sample
              index) =
        (normalizationNumerator data row
          column).sample index /
          (normalizationDenominator data).sample
            index
    rw [ExplicitField.div_eq_mul_inv,
      ExplicitField.div_eq_mul_inv]
    ring1
  have productToSynchronized : NamedEquivalent
      (geometricNamed productSource).name
      (geometricNamed synchronizedSource).name :=
    geometricNamed_equivalent_of_samples productSource synchronizedSource
      productSamples
  have result := NamedEquivalent.trans
    productEquivalent productToSynchronized
  simpa only [Certificate.normalizedData,
    NormalizedPeriodData.omega, normalize_apply, numerator, reciprocal,
    inverse, synchronizedSource] using result

/-- Approximation-level form, exposing the raw synchronized sample index on the right rather than resampling its
productive wrapper. -/
@[expose] def normalizedEntry_equivalent_synchronizedApproximation {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) :
    Equivalent
      (Sampling.approximation
        ((Certificate.normalizedData data inverseLower).omega
          row column).name)
      (synchronizedEntryApproximation data
        inverseLower row column).toApproximation :=
  Equivalent.trans
    (normalizedEntry_equivalent_synchronized data
      inverseLower row column)
    (by
      simpa only [geometricNamed,
        ofApproximation] using
        Equivalent.toNamed_sampling
          (synchronizedEntryApproximation data
            inverseLower row column).toApproximation)

/-! ## One shared finite comparison index -/

/-- A deliberately conservative squared comparison allowance. -/
@[expose] def comparisonTarget (radius :
  Coordinate) : Coordinate :=
  radius ^ 2 / 64

/-- A positive radius gives a positive squared comparison allowance. -/
theorem comparisonTarget_positive {radius :
  Coordinate}
    (positive : 0 < radius) : 0 <
      comparisonTarget radius := by
  unfold comparisonTarget
  exact Field.div_pos_direct
    (Arithmetic.pow_pos_direct positive 2)
    (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by omega))

/-- Thirty-eight comparison allowances fit strictly below the original radius squared. -/
theorem thirtyEight_comparisonTarget_lt_sq {radius :
  Coordinate}
    (positive : 0 < radius) : 38 *
      comparisonTarget radius < radius ^ 2
      := by
  have squarePositive : 0 < radius ^ 2 :=
    Arithmetic.pow_pos_direct positive 2
  have sixtyFourPositive : (0 : Coordinate) < 64 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 64) (by omega)
  have fractionSmall : (38 : Coordinate) / 64 < 1
    := by
    apply (Field.div_lt_iff_pos sixtyFourPositive).2
    calc
      (38 : Coordinate) < (64 :
        Coordinate) :=
        Fraction.Cast.Order.natCast_lt_direct
          (m := 38) (n := 64) (by omega)
      _ = 1 * 64 := by ring1
  calc
    38 * comparisonTarget radius = radius ^ 2 *
      ((38 : Coordinate) / 64) := by
      unfold comparisonTarget
      rw [ExplicitField.div_eq_mul_inv,
        ExplicitField.div_eq_mul_inv]
      ring1
    _ < radius ^ 2 * 1 :=
      Arithmetic.mul_lt_mul_of_pos_left_direct
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
      refine Data.Fin.cases_induction ?_ (fun tail => ?_) index
      · change values ⟨0, Nat.zero_lt_succ count⟩ ≤
          max (values ⟨0, Nat.zero_lt_succ count⟩) (finMax (fun entry : Fin count => values entry.succ))
        exact Data.Nat.Order.le_max_left _ _
      · exact (inductionHypothesis
          (fun entry : Fin count => values entry.succ) tail).trans
            (Data.Nat.Order.le_max_right _ _)

/-- Constructive maximum over the finite square matrix of entry indices. -/
@[expose] def matrixMax {size : Nat} (values : Fin size -> Fin size -> Nat) : Nat :=
  finMax fun row => finMax (values row)

/-- Every entry in the finite index matrix is bounded by its nested maximum. -/
theorem le_matrixMax {size : Nat} (values : Fin size -> Fin size -> Nat)
    (row column : Fin size) : values row column <=
      matrixMax values :=
  (le_finMax (values row) column).trans
    (le_finMax (fun entry => finMax (values entry))
      row)

/-- First canonical sampler index at which one normalized entry has small enough semantic allowance for the matrix
comparison. -/
@[expose] def entryComparisonStart {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (row column : Fin genus)
      : Nat :=
  let entry :=
    (Certificate.normalizedData data inverseLower).omega row column
  Search.firstQuarterBelow 1 0
    (entry.coherent.accuracyRequest
      (comparisonTarget radius))

/-- One entry's fully computed operational comparison with the raw synchronized normalization stream. -/
@[expose] def entryComparison {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    Comparison
      (Sampling.approximation
        ((Certificate.normalizedData data inverseLower).omega
          row column).name)
      (synchronizedEntryApproximation data
        inverseLower row column).toApproximation
      (entryComparisonStart data inverseLower
        radius row column) 0
      (comparisonTarget radius) :=

    (normalizedEntry_equivalent_synchronizedApproximation
    data inverseLower
    row column).compare
      (entryComparisonStart data inverseLower
        radius row column) 0
      (comparisonTarget radius)
        (comparisonTarget_positive positive)

/-- One later persistent sampler index shared by every matrix entry. -/
@[expose] def persistentSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius) :
      Nat :=
  matrixMax fun row column =>
    (entryComparison data inverseLower radius
      positive row column).leftIndex

/-- One raw synchronized sample index shared by every matrix entry. -/
@[expose] def synchronizedSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius) :
      Nat :=
  matrixMax fun row column =>
    (entryComparison data inverseLower radius
      positive row column).rightIndex

/-- Each entry comparison left index is bounded by the common persistent sample index. -/
theorem entryComparison_left_le_persistentSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (entryComparison data inverseLower radius
      positive row column).leftIndex <=
      persistentSampleIndex data inverseLower
        radius positive :=
  by
    simpa only [persistentSampleIndex] using
      (le_matrixMax (fun leftRow leftColumn =>
        (entryComparison data inverseLower radius
          positive
          leftRow leftColumn).leftIndex) row column)

/-- Each entry comparison right index is bounded by the common synchronized sample index. -/
theorem entryComparison_right_le_synchronizedSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (entryComparison data inverseLower radius
      positive row column).rightIndex <=
      synchronizedSampleIndex data inverseLower
        radius positive :=
  by
    simpa only [synchronizedSampleIndex] using
      (le_matrixMax (fun leftRow leftColumn =>
        (entryComparison data inverseLower radius
          positive
          leftRow leftColumn).rightIndex) row column)

/-- Every entry coherence start is bounded by the common persistent sample index. -/
theorem entryComparisonStart_le_persistentSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    entryComparisonStart data inverseLower radius
      row column <=
      persistentSampleIndex data inverseLower
        radius positive :=
  (entryComparison data inverseLower radius
    positive row column).left_ge.trans
    (entryComparison_left_le_persistentSampleIndex
      data inverseLower radius
      positive row column)

/-- The shared persistent sampler index has the small semantic allowance requested before the entrywise operational
comparisons. -/
theorem persistentSampleAllowance_lt {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    let entry :=
      (Certificate.normalizedData data inverseLower).omega
        row column
    entry.coherent.allowance
        (Process.Sampling.stateAt entry.name.process entry.name.state
          (persistentSampleIndex data inverseLower
            radius positive)) <
      comparisonTarget radius := by
  let entry :=
    (Certificate.normalizedData data inverseLower).omega row column
  let start := entryComparisonStart data
    inverseLower radius row column
  let persistent := persistentSampleIndex data
    inverseLower radius positive
  have requestPositive :
      0 < entry.coherent.accuracyRequest
        (comparisonTarget radius) :=
    entry.coherent.accuracyRequest_pos
      (comparisonTarget_positive positive)
  have startAccurate :
      Process.Sampling.refinementTarget start <
        entry.coherent.accuracyRequest
          (comparisonTarget radius) := by
    exact Search.firstQuarterBelow_accurate 1 (by decide) 0
      (entry.coherent.accuracyRequest
        (comparisonTarget radius))
      requestPositive
  have startOrder : start <= persistent := by
    exact
      entryComparisonStart_le_persistentSampleIndex
      data inverseLower
      radius positive row column
  have persistentRequestSmall :
      Process.Sampling.refinementTarget persistent <
        entry.coherent.accuracyRequest
          (comparisonTarget radius) :=
    (quarterRadius_antitone (by decide) startOrder).trans_lt
      startAccurate
  exact Process.Coherence.Basic.Coherent.stateAt_allowance_lt entry.coherent
    entry.name.state persistent (comparisonTarget
      radius)
    (comparisonTarget_positive positive)
      persistentRequestSmall

/-- All entries can be evaluated at the one maximum raw index while retaining the strict operational comparison bound.
-/
theorem persistentSample_close_synchronized {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    Basic.normSq
        ((Sampling.approximation
            ((Certificate.normalizedData data inverseLower).omega
              row column).name).sample
            (persistentSampleIndex data
              inverseLower radius positive) -
          Certificate.synchronizedNormalizedMatrix data
            (synchronizedSampleIndex data
              inverseLower radius positive)
            row column) <
      comparisonTarget radius := by
  have close :=
    (entryComparison data inverseLower radius
      positive row column).close

        (entryComparison_left_le_persistentSampleIndex
        data inverseLower radius
        positive row column)

        (entryComparison_right_le_synchronizedSampleIndex
        data inverseLower
        radius positive row column)
  simpa only [
    GeometricApproximation.toApproximation_sample,
    synchronizedEntryApproximation_sample] using
      close

/-- A sufficiently fine shared persistent request is automatically close to the one computed raw synchronized matrix.

The proof compares only finite process witnesses, finite coherence allowances, and rational squared-error budgets. -/
theorem centerMatrix_close_synchronized {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (comparisonRadius : Coordinate)
      (comparisonPositive : 0 < comparisonRadius)
    (centerTarget : Coordinate) (centerPositive : 0
      < centerTarget)
    (centerSmall : centerTarget < comparisonTarget
      comparisonRadius)
    (row column : Fin genus) :
    Basic.normSq
        (Positivity.centerMatrix
            (Certificate.normalizedData data inverseLower)
            centerTarget centerPositive row column -
          Certificate.synchronizedNormalizedMatrix data
            (synchronizedSampleIndex data
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
    persistentSampleIndex data inverseLower
      comparisonRadius comparisonPositive
  let persistentValue :=
    (Sampling.approximation entry.name).sample persistent
  let rawIndex :=
    synchronizedSampleIndex data inverseLower
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
      Table.Request.prepareEntry, NormalizedPeriodData.refinedOmegaEntry] using
      contract.2.1
  have persistentAllowanceLt :
      entry.coherent.allowance
          (Process.Sampling.stateAt entry.name.process entry.name.state
            persistent) < comparisonTarget
              comparisonRadius := by
    simpa only [entry, persistent, normalized] using
      persistentSampleAllowance_lt data
        inverseLower comparisonRadius
        comparisonPositive row column
  have refinedPossible : entry.name.process.Possible refined.state witness := by
    exact (refined.process.witness refined.state).property
  have persistentPossible : entry.name.process.Possible
      (Process.Sampling.stateAt entry.name.process entry.name.state
        persistent) persistentValue := by
    exact Process.Sampling.witnessAt_possible entry.name.process
      entry.name.state persistent
  have witnessInside := entry.name.process.possible_inside refinedPossible
  have centerWitness : Basic.normSq (center - witness) <=
      (refined.process.ball refined.state).radiusSq := by
    have identity : center - witness = -(witness - center) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im] <;> ring1
    rw [identity, Basic.normSq_neg]
    exact witnessInside
  have semanticClose : Basic.normSq (witness - persistentValue) <=
      4 * (entry.coherent.allowance refined.state +
        entry.coherent.allowance
          (Process.Sampling.stateAt entry.name.process entry.name.state
            persistent)) :=
    entry.coherent.possible_close refinedPossible persistentPossible
  have semanticSmall : Basic.normSq (witness - persistentValue) <
      4 * (centerTarget + comparisonTarget
        comparisonRadius) :=
    semanticClose.trans_lt
      (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (Arithmetic.add_lt_add_direct centerAllowanceLt
          persistentAllowanceLt))
  have operationalSmall : Basic.normSq (persistentValue - rawValue) <
      comparisonTarget comparisonRadius := by
    simpa only [persistentValue, rawValue, persistent, rawIndex, entry,
      normalized] using
      persistentSample_close_synchronized data
        inverseLower comparisonRadius
        comparisonPositive row column
  have witnessRawSmall : Basic.normSq (witness - rawValue) <
      2 * (4 * (centerTarget + comparisonTarget
        comparisonRadius) +
        comparisonTarget comparisonRadius) := by
    calc
      Basic.normSq (witness - rawValue) <=
          2 * (Basic.normSq (witness - persistentValue) +
            Basic.normSq (persistentValue - rawValue)) :=
        Bounds.normSq_sub_le_via witness persistentValue rawValue
      _ < 2 * (4 * (centerTarget + comparisonTarget
        comparisonRadius) +
          comparisonTarget comparisonRadius) :=
        Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Arithmetic.add_lt_add_direct semanticSmall
            operationalSmall)
  have centerRawSmall : Basic.normSq (center - rawValue) <
      18 * centerTarget + 20 * comparisonTarget
        comparisonRadius := by
    calc
      Basic.normSq (center - rawValue) <=
          2 * (Basic.normSq (center - witness) + Basic.normSq
            (witness - rawValue)) :=
        Bounds.normSq_sub_le_via center witness rawValue
      _ < 2 * (centerTarget +
          2 * (4 * (centerTarget + comparisonTarget
            comparisonRadius) +
            comparisonTarget comparisonRadius)) :=
        Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Arithmetic.add_lt_add_direct
            (centerWitness.trans_lt ballRadiusLt) witnessRawSmall)
      _ = 18 * centerTarget +
          20 * comparisonTarget comparisonRadius :=
            by ring1
  have belowThirtyEight :
      18 * centerTarget + 20 * comparisonTarget
        comparisonRadius <
        38 * comparisonTarget comparisonRadius :=
          by
    have scaledCenter : 18 * centerTarget <
        18 * comparisonTarget comparisonRadius :=
      Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        centerSmall
    calc
      18 * centerTarget + 20 * comparisonTarget
        comparisonRadius <
          18 * comparisonTarget comparisonRadius +
            20 * comparisonTarget comparisonRadius
              :=
        Arithmetic.add_lt_add_right_direct scaledCenter _
      _ = 38 * comparisonTarget comparisonRadius :=
        by
        ring1
  have finalSmall := centerRawSmall.trans
    (belowThirtyEight.trans
      (thirtyEight_comparisonTarget_lt_sq
        comparisonPositive))
  have centerReadback : center = normalized.omegaCenter centerTarget centerPositive row column :=
    normalized.prepareOmegaEntry_center centerTarget centerPositive row column
  rw [centerReadback] at finalSmall
  simpa only [rawValue, rawIndex, normalized, Positivity.centerMatrix_apply] using finalSmall

/-- Reindex the automatic comparison by a displayed equality, allowing dependent certificate packages to keep the
computed natural index opaque. -/
theorem centerMatrix_close_synchronized_of_index_eq {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (comparisonRadius : Coordinate)
      (comparisonPositive : 0 < comparisonRadius)
    (rawIndex : Nat)
    (rawIndex_eq : rawIndex =
      synchronizedSampleIndex data inverseLower
        comparisonRadius
        comparisonPositive)
    (centerTarget : Coordinate) (centerPositive : 0
      < centerTarget)
    (centerSmall : centerTarget < comparisonTarget
      comparisonRadius)
    (row column : Fin genus) :
    Basic.normSq
        (Positivity.centerMatrix
            (Certificate.normalizedData data inverseLower)
            centerTarget centerPositive row column -
          Certificate.synchronizedNormalizedMatrix data
            rawIndex row column) <
      comparisonRadius ^ 2 := by
  subst rawIndex
  exact centerMatrix_close_synchronized data
    inverseLower comparisonRadius
    comparisonPositive centerTarget centerPositive centerSmall row column

/-! ## Tail comparison indices and centre comparison -/

/-- First tail sampler index at which one normalized entry has small enough semantic allowance for the matrix
comparison. -/
@[expose] def tailEntryComparisonStart {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (radius : Coordinate) (row column : Fin genus)
      : Nat :=
  let entry :=
    (NormalizedPeriodData.ofScaledInverse data
      certificate.toScaledInverseCertificate).omega row column
  Search.firstQuarterBelow 1 0
    (entry.coherent.accuracyRequest
      (comparisonTarget radius))

/-- Approximation-level tail equivalence, exposing the dropped geometric source directly. -/
@[expose] def tailNormalizedEntry_equivalent_droppedApproximation {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (row column : Fin genus) :
    Equivalent
      (Sampling.approximation
        ((NormalizedPeriodData.ofScaledInverse data
          certificate.toScaledInverseCertificate).omega row column).name)
      (droppedSynchronizedEntryApproximation data
        certificate
        row column).toApproximation :=
  Equivalent.trans
    (tailNormalizedEntry_equivalent_dropped data
      certificate row column)
    (by
      simpa only [geometricNamed,
        ofApproximation] using
        Equivalent.toNamed_sampling
          (droppedSynchronizedEntryApproximation
            data certificate
            row column).toApproximation)

/-- One tail entry's fully computed operational comparison with the dropped raw synchronized normalization stream. -/
@[expose] def tailEntryComparison {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
      (row column : Fin genus) :
    Comparison
      (Sampling.approximation
        ((NormalizedPeriodData.ofScaledInverse data
          certificate.toScaledInverseCertificate).omega row column).name)
      (droppedSynchronizedEntryApproximation data
        certificate
        row column).toApproximation
      (tailEntryComparisonStart data certificate
        radius row column) 0
      (comparisonTarget radius) :=

    (tailNormalizedEntry_equivalent_droppedApproximation
    data certificate
    row column).compare
    (tailEntryComparisonStart data certificate
      radius row column) 0
    (comparisonTarget radius)
      (comparisonTarget_positive positive)

/-- One later tail persistent sampler index shared by every matrix entry. -/
@[expose] def tailPersistentSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius) :
      Nat :=
  matrixMax fun row column =>
    (tailEntryComparison data certificate radius
      positive row column).leftIndex

/-- One shifted raw synchronized sample index shared by every matrix entry. -/
@[expose] def tailSynchronizedSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius) :
      Nat :=
  matrixMax fun row column =>
    (tailEntryComparison data certificate radius
      positive row column).rightIndex

/-- Each dropped-tail entry comparison left index is bounded by the common persistent sample index. -/
theorem tailEntryComparison_left_le_persistentSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (tailEntryComparison data certificate radius
      positive row column).leftIndex <=
      tailPersistentSampleIndex data certificate
        radius positive := by
  simpa only [tailPersistentSampleIndex] using
    (le_matrixMax (fun leftRow leftColumn =>
      (tailEntryComparison data certificate radius
        positive
        leftRow leftColumn).leftIndex) row column)

/-- Each dropped-tail entry comparison right index is bounded by the common synchronized sample index. -/
theorem tailEntryComparison_right_le_synchronizedSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (tailEntryComparison data certificate radius
      positive row column).rightIndex <=
      tailSynchronizedSampleIndex data certificate
        radius positive := by
  simpa only [tailSynchronizedSampleIndex] using
    (le_matrixMax (fun leftRow leftColumn =>
      (tailEntryComparison data certificate radius
        positive
        leftRow leftColumn).rightIndex) row column)

/-- Every dropped-tail entry coherence start is bounded by the common persistent sample index. -/
theorem tailEntryComparisonStart_le_persistentSampleIndex {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    tailEntryComparisonStart data certificate
      radius row column <=
      tailPersistentSampleIndex data certificate
        radius positive :=
  (tailEntryComparison data certificate radius
    positive row column).left_ge.trans

      (tailEntryComparison_left_le_persistentSampleIndex
      data certificate radius
      positive row column)

/-- The shared tail persistent sampler index has the small semantic allowance requested before the entrywise operational
comparisons. -/
theorem tailPersistentSampleAllowance_lt {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    let entry :=
      (NormalizedPeriodData.ofScaledInverse data
        certificate.toScaledInverseCertificate).omega row column
    entry.coherent.allowance
        (Process.Sampling.stateAt entry.name.process entry.name.state
          (tailPersistentSampleIndex data
            certificate radius positive)) <
      comparisonTarget radius := by
  let entry :=
    (NormalizedPeriodData.ofScaledInverse data
      certificate.toScaledInverseCertificate).omega row column
  let start := tailEntryComparisonStart data
    certificate radius row column
  let persistent := tailPersistentSampleIndex data
    certificate radius positive
  have requestPositive :
      0 < entry.coherent.accuracyRequest
        (comparisonTarget radius) :=
    entry.coherent.accuracyRequest_pos
      (comparisonTarget_positive positive)
  have startAccurate :
      Process.Sampling.refinementTarget start <
        entry.coherent.accuracyRequest
          (comparisonTarget radius) :=
    Search.firstQuarterBelow_accurate 1 (by decide) 0
      (entry.coherent.accuracyRequest
        (comparisonTarget radius)) requestPositive
  have startOrder : start <= persistent :=

      tailEntryComparisonStart_le_persistentSampleIndex
      data certificate radius
      positive row column
  have persistentRequestSmall :
      Process.Sampling.refinementTarget persistent <
        entry.coherent.accuracyRequest
          (comparisonTarget radius) :=
    (quarterRadius_antitone (by decide) startOrder).trans_lt
      startAccurate
  exact Process.Coherence.Basic.Coherent.stateAt_allowance_lt entry.coherent
    entry.name.state persistent (comparisonTarget
      radius)
    (comparisonTarget_positive positive)
      persistentRequestSmall

/-- All tail entries can be evaluated at the one maximum retained index while retaining the strict operational
comparison bound, with the raw matrix read at the shifted index. -/
theorem tailPersistentSample_close_synchronized {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    Basic.normSq
        ((Sampling.approximation
            ((NormalizedPeriodData.ofScaledInverse data
              certificate.toScaledInverseCertificate).omega row column).name).sample
            (tailPersistentSampleIndex data
              certificate radius positive) -
          Certificate.synchronizedNormalizedMatrix data
            (certificate.anchor +
              tailSynchronizedSampleIndex data
                certificate radius positive)
            row column) <
      comparisonTarget radius := by
  have close :=
    (tailEntryComparison data certificate radius
      positive row column).close

        (tailEntryComparison_left_le_persistentSampleIndex
        data certificate radius
        positive row column)

        (tailEntryComparison_right_le_synchronizedSampleIndex
        data certificate
        radius positive row column)
  simpa only [
    GeometricApproximation.toApproximation_sample,
    droppedSynchronizedEntryApproximation_sample]
      using close

/-- A sufficiently fine shared persistent tail request is automatically close to the one computed raw synchronized
matrix at the shifted retained index. -/
theorem tailCenterMatrix_close_synchronized {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (comparisonRadius : Coordinate)
      (comparisonPositive : 0 < comparisonRadius)
    (centerTarget : Coordinate) (centerPositive : 0
      < centerTarget)
    (centerSmall : centerTarget < comparisonTarget
      comparisonRadius)
    (row column : Fin genus) :
    Basic.normSq
        (Positivity.centerMatrix
            (NormalizedPeriodData.ofScaledInverse data
              certificate.toScaledInverseCertificate)
            centerTarget centerPositive row column -
          Certificate.synchronizedNormalizedMatrix data
            (certificate.anchor +
              tailSynchronizedSampleIndex data
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
    tailPersistentSampleIndex data certificate
      comparisonRadius
      comparisonPositive
  let persistentValue :=
    (Sampling.approximation entry.name).sample persistent
  let rawIndex :=
    certificate.anchor +
      tailSynchronizedSampleIndex data certificate
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
      Table.Request.prepareEntry, NormalizedPeriodData.refinedOmegaEntry] using
      contract.2.1
  have persistentAllowanceLt :
      entry.coherent.allowance
          (Process.Sampling.stateAt entry.name.process entry.name.state
            persistent) < comparisonTarget
              comparisonRadius := by
    simpa only [entry, persistent, normalized] using
      tailPersistentSampleAllowance_lt data
        certificate comparisonRadius
        comparisonPositive row column
  have refinedPossible : entry.name.process.Possible refined.state witness :=
    (refined.process.witness refined.state).property
  have persistentPossible : entry.name.process.Possible
      (Process.Sampling.stateAt entry.name.process entry.name.state
        persistent) persistentValue :=
    Process.Sampling.witnessAt_possible entry.name.process
      entry.name.state persistent
  have witnessInside := entry.name.process.possible_inside refinedPossible
  have centerWitness : Basic.normSq (center - witness) <=
      (refined.process.ball refined.state).radiusSq := by
    have identity : center - witness = -(witness - center) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im] <;> ring1
    rw [identity, Basic.normSq_neg]
    exact witnessInside
  have semanticClose : Basic.normSq (witness - persistentValue) <=
      4 * (entry.coherent.allowance refined.state +
        entry.coherent.allowance
          (Process.Sampling.stateAt entry.name.process entry.name.state
            persistent)) :=
    entry.coherent.possible_close refinedPossible persistentPossible
  have semanticSmall : Basic.normSq (witness - persistentValue) <
      4 * (centerTarget + comparisonTarget
        comparisonRadius) :=
    semanticClose.trans_lt
      (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (Arithmetic.add_lt_add_direct centerAllowanceLt
          persistentAllowanceLt))
  have operationalSmall : Basic.normSq (persistentValue - rawValue) <
      comparisonTarget comparisonRadius := by
    simpa only [persistentValue, rawValue, persistent, rawIndex, entry,
      normalized] using
      tailPersistentSample_close_synchronized data
        certificate comparisonRadius
        comparisonPositive row column
  have witnessRawSmall : Basic.normSq (witness - rawValue) <
      2 * (4 * (centerTarget + comparisonTarget
        comparisonRadius) +
        comparisonTarget comparisonRadius) := by
    calc
      Basic.normSq (witness - rawValue) <=
          2 * (Basic.normSq (witness - persistentValue) +
            Basic.normSq (persistentValue - rawValue)) :=
        Bounds.normSq_sub_le_via witness persistentValue rawValue
      _ < 2 * (4 * (centerTarget + comparisonTarget
        comparisonRadius) +
          comparisonTarget comparisonRadius) :=
        Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Arithmetic.add_lt_add_direct semanticSmall
            operationalSmall)
  have centerRawSmall : Basic.normSq (center - rawValue) <
      18 * centerTarget + 20 * comparisonTarget
        comparisonRadius := by
    calc
      Basic.normSq (center - rawValue) <=
          2 * (Basic.normSq (center - witness) + Basic.normSq
            (witness - rawValue)) :=
        Bounds.normSq_sub_le_via center witness rawValue
      _ < 2 * (centerTarget +
          2 * (4 * (centerTarget + comparisonTarget
            comparisonRadius) +
            comparisonTarget comparisonRadius)) :=
        Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Arithmetic.add_lt_add_direct
            (centerWitness.trans_lt ballRadiusLt) witnessRawSmall)
      _ = 18 * centerTarget +
          20 * comparisonTarget comparisonRadius :=
            by ring1
  have belowThirtyEight :
      18 * centerTarget + 20 * comparisonTarget
        comparisonRadius <
        38 * comparisonTarget comparisonRadius :=
          by
    have scaledCenter : 18 * centerTarget <
        18 * comparisonTarget comparisonRadius :=
      Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        centerSmall
    calc
      18 * centerTarget + 20 * comparisonTarget
        comparisonRadius <
          18 * comparisonTarget comparisonRadius +
            20 * comparisonTarget comparisonRadius
              :=
        Arithmetic.add_lt_add_right_direct scaledCenter _
      _ = 38 * comparisonTarget comparisonRadius :=
        by
        ring1
  have finalSmall := centerRawSmall.trans
    (belowThirtyEight.trans
      (thirtyEight_comparisonTarget_lt_sq
        comparisonPositive))
  have centerReadback : center = normalized.omegaCenter centerTarget centerPositive row column :=
    normalized.prepareOmegaEntry_center centerTarget centerPositive row column
  rw [centerReadback] at finalSmall
  simpa only [rawValue, rawIndex, normalized, Positivity.centerMatrix_apply] using finalSmall

/-- Reindex the tail comparison by a displayed equality for a caller-supplied raw index. -/
theorem tailCenterMatrix_close_synchronized_of_index_eq {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (certificate : ScalarTailSeparationCertificate data.aMatrix)
    (comparisonRadius : Coordinate)
      (comparisonPositive : 0 < comparisonRadius)
    (rawIndex : Nat)
    (rawIndex_eq : rawIndex = certificate.anchor +
      tailSynchronizedSampleIndex data certificate
        comparisonRadius
        comparisonPositive)
    (centerTarget : Coordinate) (centerPositive : 0
      < centerTarget)
    (centerSmall : centerTarget < comparisonTarget
      comparisonRadius)
    (row column : Fin genus) :
    Basic.normSq
        (Positivity.centerMatrix
            (NormalizedPeriodData.ofScaledInverse data
              certificate.toScaledInverseCertificate)
            centerTarget centerPositive row column -
          Certificate.synchronizedNormalizedMatrix data
            rawIndex row column) <
      comparisonRadius ^ 2 := by
  subst rawIndex
  exact tailCenterMatrix_close_synchronized data
    certificate comparisonRadius
    comparisonPositive centerTarget centerPositive centerSmall row column

end Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization

end
