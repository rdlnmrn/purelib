module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Box.Interior
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Hermitian
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RationalFunctions.Curve.Projective.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RationalFunctions.Curve.Basic
import Purelib.Tactic.Ring
import Purelib.Geometry.Projective.Line.Matrix

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal.Box

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Chart

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Hermitian

open Purelib.RationalFunctions.Curve

section
@[expose] public section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace Purelib.Geometry.Projective.RationalCharts.Box.Exclusion

/-- A homogeneous denominator residual below the chart-weight-scaled infinity gap excludes the corresponding explicit
non-pole affine point from the finite box. -/
theorem denominator_residual_excludes_box
    {form : Hermitian.HermitianForm}
    (chart : Chart.BoundedChart form)
    (box : Rational.Box) (parameter : Fraction.Rational)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (small :
      (Coordinates.denominatorNormSq
          chart.parameterization.curve).eval parameter ^ 2 <
        (chart.parameterization.weightLower * Interior.infinityBoxGap box) ^ 2) :
    ¬box.Contains
      (chart.parameterization.curve.point parameter) := by
  let denominatorNorm := Data.Gaussian.Norm.Basic.normSq
    (chart.parameterization.curve.denominatorAt parameter)
  let weight := Proj.weight
    (chart.projective parameter)
  let gap := Interior.infinityBoxGap box
  let cap := chart.parameterization.weightLower * gap
  have gapPositive : 0 < gap := by
    simpa only [gap] using Interior.infinityBoxGap_pos box
  have lowerPositive : 0 < chart.parameterization.weightLower :=
    chart.parameterization.weightLowerPositive
  have capPositive : 0 < cap :=
    Fraction.Order.Arithmetic.mul_pos_direct lowerPositive gapPositive
  have denominatorSquareSmall : denominatorNorm ^ 2 < cap ^ 2 := by
    simpa only [denominatorNorm, cap,
      Coordinates.eval_denominatorNormSq] using small
  have denominatorLtCap : denominatorNorm < cap :=
    Bounds.Square.lt_of_sq_lt_sq_of_nonneg capPositive.le
      denominatorSquareSmall
  have denominatorNonnegative : 0 ≤ denominatorNorm := Data.Gaussian.Norm.Basic.normSq_nonneg _
  have weightPositive : 0 < weight := by
    simpa only [weight] using chart.projective_weight_pos parameter
  have lowerLeWeight : chart.parameterization.weightLower ≤ weight := by
    simpa only [weight] using chart.weightLower_le_projective parameter
  have quotientLe : denominatorNorm / weight ≤
      denominatorNorm / chart.parameterization.weightLower :=
    Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      denominatorNonnegative lowerPositive lowerLeWeight
  have quotientLtGap :
      denominatorNorm / chart.parameterization.weightLower < gap := by
    apply (Fraction.Order.Field.div_lt_iff_pos lowerPositive).2
    simpa only [cap, Fraction.Field.mul_comm] using denominatorLtCap
  have projectiveClose :
      Chordal.Basic.chordalSq
          (chart.projective parameter) Proj.omega < gap := by
    have identity :
        Chordal.Basic.chordalSq
            (chart.projective parameter) Proj.omega =
          denominatorNorm / weight := by
      simp only [BoundedChart.projective,
        Projective.projective,
        Chordal.Basic.chordalSq, Proj.omega,
        Proj.weight, denominatorNorm, weight,
        Data.Gaussian.Basic.mul_zero,
        Data.Gaussian.Basic.one_mul,
        Data.Gaussian.Basic.zero_sub,
        Data.Gaussian.Norm.Basic.normSq_neg,
        Data.Gaussian.Norm.Basic.normSq_one,
        Data.Gaussian.Norm.Basic.normSq_zero]
      congr 1
      ring1
    rw [identity]
    exact quotientLe.trans_lt quotientLtGap
  intro inside
  have gapLower := Interior.infinityBoxGap_le_affine inside
  have projectiveEq :=
    Projective.chordalSq_projective_eq_affine
      chart.parameterization.curve parameter denominatorNonzero Proj.omega
  rw [← projectiveEq] at gapLower
  exact (not_lt_of_ge gapLower) projectiveClose
end Purelib.Geometry.Projective.RationalCharts.Box.Exclusion

end
