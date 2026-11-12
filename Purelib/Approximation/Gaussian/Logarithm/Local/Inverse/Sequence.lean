module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial
public import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error
import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Majorant
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Geometric.Quarter
import Purelib.Polynomial.Ascending.Rational.Evaluation
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.GaussianMajorant
import Purelib.Polynomial.Ascending.Rational.Nonnegative
import Purelib.Polynomial.Ascending.Rational.Nonnegative.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

section
public section

/-! Approximation Gaussian Logarithm Local Inverse Sequence and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Sequence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat
open Purelib.Data.Rat.Geometric
open Purelib.Polynomial.Ascending.Rational
open Purelib.Polynomial.Ascending.Rational.Nonnegative

/-- Four times the retained finite exponential–logarithm chart error coefficient. -/
@[expose] public def localExpLogApproximationScale : Fraction.Rational := 4 * Error.expLogErrorScale

/-- The local exponential–logarithm approximation scale is nonnegative. -/
theorem localExpLogApproximationScale_nonnegative :
    0 ≤ localExpLogApproximationScale :=
  Arithmetic.mul_nonneg_direct (by decide)
    Error.expLogErrorScale_nonnegative

/-- On the one-ninth quadrance disk, every synchronized exponential–logarithm sample has squared norm at most fifty. -/
theorem localExpLogSample_bounded {z : Data.Gaussian.Basic.Canonical}
    (zBound : Basic.normSq z ≤ 1 / 9) (depth : Nat) :
    Basic.normSq (Error.localExpLogSample z depth) ≤ 5 * 10 := by
  rw [Error.localExpLogSample_eq_eval]
  let polynomial := Polynomial.exponentialLocalLog (2 * depth + 2) depth
  have polynomialNonnegative : CoefficientsNonnegative polynomial :=
    Polynomial.coefficientsNonnegative_exponentialLocalLog _ _
  have magnitudeNonnegative : 0 ≤ Evaluation.scalarEval (1 / 2) polynomial :=
    Evaluation.scalarEvalCoefficients_nonnegative (by decide) polynomial.coefficients
      polynomialNonnegative
  have magnitudeBound : Evaluation.scalarEval (1 / 2) polynomial ≤ 5 :=
    Majorant.scalarEval_exponentialLocalLog_half_le_five _ _
  have magnitudeSquare := Arithmetic.pow_le_pow_direct
    magnitudeNonnegative magnitudeBound 2
  calc
    Basic.normSq (GaussianEvaluation.eval polynomial z) ≤
        2 * Evaluation.scalarEval (1 / 2) polynomial ^ 2 :=
      GaussianMajorant.eval_normSq_le_scalarHalf polynomialNonnegative zBound
    _ ≤ 2 * (5 : Fraction.Rational) ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        magnitudeSquare (by decide)
    _ = 5 * 10 := by decide

/-- Package the finite exponential–logarithm samples with geometric error and an executable refinement search.

The original Gaussian input is retained together with its one-ninth quadrance bound; every sample has the displayed
uniform norm bound. -/
@[expose] public def localExpLogApproximation (z : Data.Gaussian.Basic.Canonical)
    (zBound : Basic.normSq z ≤ 1 / 9) : ApproximationData where
  sample := Error.localExpLogSample z
  radiusSq := fun depth =>
    Basic.quarterRadius
      localExpLogApproximationScale depth
  radiusSq_nonneg := fun depth =>
    Basic.quarterRadius_nonneg
      localExpLogApproximationScale_nonnegative depth
  later_close := by
    intro earlier later order
    let chart := (1 + z) / (1 - z)
    have laterError := Error.localExpLogSample_chart_error zBound later
    have earlierError := Error.localExpLogSample_chart_error zBound earlier
    have earlierError' :
        Basic.normSq (chart - Error.localExpLogSample z earlier) ≤
          Error.expLogErrorScale * (1 / 4 : Fraction.Rational) ^ earlier := by
      have identity : chart - Error.localExpLogSample z earlier =
          -(Error.localExpLogSample z earlier - chart) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
            Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
      rw [identity, Basic.normSq_neg]
      exact earlierError
    have laterScaled :
        Error.expLogErrorScale * (1 / 4 : Fraction.Rational) ^ later ≤
          Error.expLogErrorScale * (1 / 4 : Fraction.Rational) ^ earlier :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Quarter.quarterPower_antitone order) Error.expLogErrorScale_nonnegative
    calc
      Basic.normSq (Error.localExpLogSample z later - Error.localExpLogSample z earlier) ≤
          2 * (Basic.normSq (Error.localExpLogSample z later - chart) +
            Basic.normSq (chart - Error.localExpLogSample z earlier)) :=
        Bounds.normSq_sub_le_via _ chart _
      _ ≤ 2 *
          (Error.expLogErrorScale * (1 / 4 : Fraction.Rational) ^ earlier +
            Error.expLogErrorScale * (1 / 4 : Fraction.Rational) ^ earlier) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (laterError.trans laterScaled) earlierError') (by decide)
      _ = Basic.quarterRadius
          localExpLogApproximationScale earlier := by
        rw [Basic.quarterRadius_eq_mul_pow]
        dsimp only [localExpLogApproximationScale]
        ring1
  refineIndex := fun current target positive =>
    Search.firstQuarterBelow
      localExpLogApproximationScale current target
  refineIndex_ge := by
    intro current target positive
    exact Search.firstQuarterBelow_ge
      localExpLogApproximationScale current target
  refineIndex_accurate := by
    intro current target positive
    exact Search.firstQuarterBelow_accurate
      localExpLogApproximationScale
        localExpLogApproximationScale_nonnegative
        current target positive
  centerBound := 5 * 10
  centerBound_nonneg :=
    Arithmetic.mul_nonneg_direct (by decide) (by decide)
  sample_bounded := localExpLogSample_bounded zBound

/-- The constant finite approximation at the Gaussian Cayley-chart value of the displayed input. -/
@[expose] public def localChartApproximation (z : Data.Gaussian.Basic.Canonical) : ApproximationData
  :=
  Constant.constantApproximation
    ((1 + z) / (1 - z))

/-- Finite operational form of `exp(2(z + z^3/3 + ...)) = (1+z)/(1-z)` on the displayed local disk. -/
@[expose] public def local_exp_log_equivalent (z : Data.Gaussian.Basic.Canonical) (zBound :
  Basic.normSq z ≤ 1 / 9) :
    Equivalence.Equivalent (localExpLogApproximation z
      zBound)
      (localChartApproximation z) where
  compare := by
    intro leftStart rightStart target positive
    let leftIndex := Search.firstQuarterBelow
      Error.expLogErrorScale leftStart target
    have leftSmall :
        Error.expLogErrorScale * (1 / 4 : Fraction.Rational) ^ leftIndex < target := by
      simpa only [Basic.quarterRadius_eq_mul_pow]
        using Search.firstQuarterBelow_accurate
          Error.expLogErrorScale Error.expLogErrorScale_nonnegative leftStart target positive
    exact
      { leftIndex := leftIndex
        rightIndex := rightStart
        left_ge := Search.firstQuarterBelow_ge
          Error.expLogErrorScale leftStart target
        right_ge := Nat.le_refl _
        close := by
          intro leftLater rightLater leftOrder rightOrder
          change Basic.normSq
            (Error.localExpLogSample z leftLater - (1 + z) / (1 - z)) < target
          exact (Error.localExpLogSample_chart_error zBound leftLater).trans_lt
            ((Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Quarter.quarterPower_antitone leftOrder)
              Error.expLogErrorScale_nonnegative).trans_lt leftSmall) }

end Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Sequence

end
