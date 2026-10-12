module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Gaussian.Name.Apart
public import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Budget.Quotient
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Quotient
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Core operational congruence for finite sampled quotients

Division is only continuous after a positive denominator lower bound has been
displayed.  This core file packages that constructive fact for the canonical
finite samplers of coherent CCL names.  It does not select completed values:
every quotient below is a quotient of two Gaussian rationals computed at one
finite index.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample

/-- Geometric error scale for equal-index quotients. The factor eight is the finite Gaussian triangle cost combined with
the canonical quarter-radius movement of each operand sampler. -/
def sampledQuotientErrorScale (numerator denominator
  : Coherent.CoherentNamed)
    (apart : Named.Apart denominator.name) : Fraction.Rational :=
  (8 *
      ((Sampling.approximation denominator.name).centerBound +
        (Sampling.approximation numerator.name).centerBound)) /
    (apart.certificate.lowerSq * apart.certificate.lowerSq)

/-- The equal-index quotient error scale is nonnegative under the retained denominator apartness certificate. -/
theorem sampledQuotientErrorScale_nonnegative
    (numerator denominator : Coherent.CoherentNamed)
    (apart : Named.Apart denominator.name) :
    0 <= sampledQuotientErrorScale numerator denominator
      apart := by
  unfold sampledQuotientErrorScale
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Sampling.approximation
          denominator.name).centerBound_nonneg
        (Sampling.approximation
          numerator.name).centerBound_nonneg))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      apart.certificate.positive.le apart.certificate.positive.le)

/-- Equal-index finite Gaussian quotients of two canonical CCL samplers. -/
def sampledQuotientApproximation (numerator
  denominator : Coherent.CoherentNamed)
    (apart : Named.Apart denominator.name) : Gaussian.Sequence.ApproximationData where
  sample index :=
    (Sampling.approximation numerator.name).sample index /
      (Sampling.approximation denominator.name).sample index
  radiusSq := Geometric.Basic.quarterRadius
    (sampledQuotientErrorScale numerator denominator apart)
  radiusSq_nonneg := Geometric.Basic.quarterRadius_nonneg
    (sampledQuotientErrorScale_nonnegative numerator denominator
      apart)
  later_close := by
    intro earlier later order
    let numeratorSource :=
      Sampling.approximation numerator.name
    let denominatorSource :=
      Sampling.approximation denominator.name
    have numeratorMovement :
        Data.Gaussian.Norm.Basic.normSq (numeratorSource.sample later -
            numeratorSource.sample earlier) <=
          Geometric.Basic.quarterRadius 4 earlier := by
      simpa only [numeratorSource, Sampling.approximation]
        using numeratorSource.later_close order
    have denominatorMovementForward :
        Data.Gaussian.Norm.Basic.normSq (denominatorSource.sample later -
            denominatorSource.sample earlier) <=
          Geometric.Basic.quarterRadius 4 earlier := by
      simpa only [denominatorSource, Sampling.approximation]
        using denominatorSource.later_close order
    have denominatorMovement :
        Data.Gaussian.Norm.Basic.normSq (denominatorSource.sample earlier -
            denominatorSource.sample later) <=
          Geometric.Basic.quarterRadius 4 earlier := by
      have identity : denominatorSource.sample earlier -
          denominatorSource.sample later =
            -(denominatorSource.sample later -
              denominatorSource.sample earlier) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
            Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
      rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
      exact denominatorMovementForward
    have quotientBound :=
      Quotient.ApproximationQuotientVariation.normSq_div_sub_div_le
        apart.certificate.positive
        (leftNumerator := numeratorSource.sample later)
        (rightNumerator := numeratorSource.sample earlier)
        (leftDenominator := denominatorSource.sample later)
        (rightDenominator := denominatorSource.sample earlier)
        (numeratorSlope := (1 : Fraction.Rational))
        (numeratorBound := numeratorSource.centerBound)
        (denominatorBound := denominatorSource.centerBound)
        (pointMovement := Geometric.Basic.quarterRadius 4 earlier)
        (rootMovement := Geometric.Basic.quarterRadius 4 earlier)
        (by
          simpa only [Fraction.Field.one_mul]
            using numeratorMovement)
        (numeratorSource.sample_bounded earlier)
        (denominatorSource.sample_bounded earlier)
        denominatorMovement
        (Apart.Sampling.sampled_lower denominator apart later)
        (Apart.Sampling.sampled_lower denominator apart earlier)
    change Data.Gaussian.Norm.Basic.normSq
        (numeratorSource.sample later / denominatorSource.sample later -
          numeratorSource.sample earlier / denominatorSource.sample earlier) <=
      Geometric.Basic.quarterRadius
        (sampledQuotientErrorScale numerator denominator apart)
          earlier
    calc
      Data.Gaussian.Norm.Basic.normSq
          (numeratorSource.sample later / denominatorSource.sample later -
            numeratorSource.sample earlier /
              denominatorSource.sample earlier) <=
        Purelib.Approximation.Rational.Budget.Quotient.quotientBound
          1 numeratorSource.centerBound denominatorSource.centerBound
          apart.certificate.lowerSq
          (Geometric.Basic.quarterRadius 4 earlier)
          (Geometric.Basic.quarterRadius 4 earlier) := quotientBound
      _ = Geometric.Basic.quarterRadius
          (sampledQuotientErrorScale numerator denominator apart)
            earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        dsimp only [numeratorSource, denominatorSource]
        unfold Purelib.Approximation.Rational.Budget.Quotient.quotientBound
          sampledQuotientErrorScale
        let geometric : Fraction.Rational := (1 / 4 : Fraction.Rational) ^ earlier
        change
          (2 *
              (1 * (4 * geometric) *
                  (Sampling.approximation
                    denominator.name).centerBound +
                (Sampling.approximation
                    numerator.name).centerBound * (4 * geometric))) /
              (apart.certificate.lowerSq * apart.certificate.lowerSq) =
            ((8 *
                ((Sampling.approximation
                    denominator.name).centerBound +
                  (Sampling.approximation
                    numerator.name).centerBound)) /
                (apart.certificate.lowerSq * apart.certificate.lowerSq)) *
              geometric
        rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
          Algebra.Field.ExplicitField.div_eq_mul_inv]
        ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow
      (sampledQuotientErrorScale numerator denominator apart)
        current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      (sampledQuotientErrorScale numerator denominator apart)
        current target
  refineIndex_accurate := Search.firstQuarterBelow_accurate
    (sampledQuotientErrorScale numerator denominator apart)
    (sampledQuotientErrorScale_nonnegative numerator denominator
      apart)
  centerBound :=
    (Sampling.approximation numerator.name).centerBound /
      apart.certificate.lowerSq
  centerBound_nonneg := Fraction.Order.Field.div_nonneg_direct
    (Sampling.approximation numerator.name).centerBound_nonneg
    apart.certificate.positive.le
  sample_bounded := by
    intro index
    let numeratorSource :=
      Sampling.approximation numerator.name
    let denominatorSource :=
      Sampling.approximation denominator.name
    have denominatorLower := Apart.Sampling.sampled_lower denominator apart index
    have denominatorPositive : 0 < Data.Gaussian.Norm.Basic.normSq (denominatorSource.sample index) :=
      apart.certificate.positive.trans_le denominatorLower
    have denominatorNonzero : denominatorSource.sample index ≠ 0 := by
      intro zero
      rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at denominatorPositive
      exact (lt_irrefl _ denominatorPositive).elim
    rw [Data.Gaussian.Field.normSq_div _ _ denominatorNonzero]
    calc
      Data.Gaussian.Norm.Basic.normSq (numeratorSource.sample index) /
          Data.Gaussian.Norm.Basic.normSq (denominatorSource.sample index) <=
        Data.Gaussian.Norm.Basic.normSq (numeratorSource.sample index) /
          apart.certificate.lowerSq :=
        Fraction.Order.Field.div_le_div_of_nonneg_left_direct
          (Data.Gaussian.Norm.Basic.normSq_nonneg _) apart.certificate.positive denominatorLower
      _ <= numeratorSource.centerBound / apart.certificate.lowerSq := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (numeratorSource.sample_bounded index)
          (Fraction.Order.Field.inv_pos_direct
            apart.certificate.positive).le

/-- The quotient approximation divides the original canonical numerator and denominator samples at the same index. -/
@[simp] theorem sampledQuotientApproximation_sample
    (numerator denominator : Coherent.CoherentNamed)
    (apart : Named.Apart denominator.name) (index : Nat) :
    (sampledQuotientApproximation numerator denominator
      apart).sample index =
      (Sampling.approximation numerator.name).sample index /
        (Sampling.approximation denominator.name).sample index :=
  rfl
end Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample

end
