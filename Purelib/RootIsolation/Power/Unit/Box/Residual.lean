module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
public import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Newton
import Purelib.RootIsolation.Power.Unit.Radius
import Purelib.RootIsolation.Power.Unit.Source
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Power.Gaussian.DerivativeSeparation
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Box.Residual

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Every displayed point of a robust owner has uniformly small residual.
The estimate is obtained from the source-anchor residual, the explicit
Newton displacement, and the finite Horner Lipschitz majorant. -/
theorem unitRobustBox_residual_le
    {parameter point : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (inside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains point) :
    normSq ((Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree).eval point) ≤
      (1 / 32 : Fraction.Rational) := by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let source := Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let newton := Power.Unit.Newton.unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  let eighth : Fraction.Rational := 1 / 8
  have radiusPositive : 0 < r :=
    Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo
  have radiusLeOne : r ≤ 1 :=
    (Power.Unit.Radius.unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo).trans
      (by decide)
  have radiusSquareLe : r ^ 2 ≤ r := by
    rw [pow_two]
    calc
      r * r ≤ 1 * r :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct radiusLeOne
          radiusPositive.le
      _ = r := by ring1
  have pointCenterDistance : normSq (point - newton.point) ≤ 2 * r ^ 2 := by
    exact Box.Square.Centered.centeredSquare_normSq_sub_center_le newton.point
      radiusPositive.le (by simpa only [Power.Unit.Box.unitRobustBox] using inside)
  have centerAnchorDistance :
      normSq (newton.point - source.box.anchor) ≤ r ^ 2 :=
    Power.Unit.Box.unitRobustNewton_displacement_le_radius_sq parameterNonzero parameterUnit
      degree degreeAtLeastTwo index
  have pointAnchorIdentity :
      point - source.box.anchor =
        (point - newton.point) + (newton.point - source.box.anchor) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1
  have pointAnchorDistance :
      normSq (point - source.box.anchor) ≤ 6 * r ^ 2 := by
    rw [pointAnchorIdentity]
    calc
      normSq ((point - newton.point) +
          (newton.point - source.box.anchor)) ≤
        2 * (normSq (point - newton.point) +
          normSq (newton.point - source.box.anchor)) :=
        Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * (2 * r ^ 2 + r ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add pointCenterDistance centerAnchorDistance) (by decide)
      _ = 6 * r ^ 2 := by ring1
  have pointAmbient : ambient.Contains point :=
    (Power.Unit.Box.unitRobustBox_refinesAmbient parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).contains inside
  have anchorAmbient : ambient.Contains source.box.anchor :=
    source.refinesAmbient.contains source.box.contains_anchor
  have variation :
      normSq (p.eval point - p.eval source.box.anchor) ≤
        6 * eighth ^ 3 := by
    have raw :=
      Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound p
        pointAmbient anchorAmbient
    have lipschitzRadiusSquare : lipschitz * r ^ 2 ≤ eighth ^ 3 := by
      calc
        lipschitz * r ^ 2 ≤ lipschitz * r :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            radiusSquareLe
            (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient).le
        _ = r * lipschitz := by ring1
        _ ≤ eighth ^ 3 := by
          simpa only [eighth] using
            Power.Unit.Radius.unitRobustRadius_mul_lipschitz_le parameterUnit degree
              degreeAtLeastTwo
    calc
      normSq (p.eval point - p.eval source.box.anchor) ≤
          lipschitz * normSq (point - source.box.anchor) := raw
      _ ≤ lipschitz * (6 * r ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          pointAnchorDistance
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient).le
      _ = 6 * (lipschitz * r ^ 2) := by ring1
      _ ≤ 6 * eighth ^ 3 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          lipschitzRadiusSquare (by decide)
  have quarterRadiusLeEighth : r / 4 ≤ eighth := by
    have inverseFourLeOne : (4 : Fraction.Rational)⁻¹ ≤ 1 := by
      have quarterLeOne : (1 / 4 : Fraction.Rational) ≤ 1 := by decide
      rw [Fraction.Field.div_eq_mul_inv_direct] at quarterLeOne
      calc
        (4 : Fraction.Rational)⁻¹ = 1 * (4 : Fraction.Rational)⁻¹ := by ring1
        _ ≤ 1 := quarterLeOne
    calc
      r / 4 ≤ r := by
        rw [Fraction.Field.div_eq_mul_inv_direct]
        calc
          r * (4 : Fraction.Rational)⁻¹ ≤ r * 1 :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              inverseFourLeOne radiusPositive.le
          _ = r := by ring1
      _ ≤ eighth := by
        simpa only [eighth] using
          Power.Unit.Radius.unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo
  have anchorResidual : normSq (p.eval source.box.anchor) ≤ eighth ^ 3 := by
    have sourceBound :=
      Power.Unit.Source.unitRobustSourceState_anchorResidual_le_displacementBudget
      parameterNonzero parameterUnit degree degreeAtLeastTwo index
    have actual := newton.residual
    have squareBound := Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Field.div_nonneg_direct radiusPositive.le (by decide))
      quarterRadiusLeEighth 2
    calc
      normSq (p.eval source.box.anchor) ≤
          Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient source.box :=
        actual
      _ ≤ (1 / 8 : Fraction.Rational) * (r / 4) ^ 2 := sourceBound
      _ ≤ eighth * eighth ^ 2 := by
        simpa only [eighth] using
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareBound
          (by decide)
      _ = eighth ^ 3 := by ring1
  have valueIdentity : p.eval point =
      (p.eval point - p.eval source.box.anchor) + p.eval source.box.anchor := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1
  rw [valueIdentity]
  have coefficientBound : 14 * eighth ≤ (2 : Fraction.Rational) := by
    simp only [eighth]
    decide
  have eighthSquareNonnegative : 0 ≤ eighth ^ 2 :=
    Fraction.Order.Arithmetic.pow_nonneg_direct
      (by simpa only [eighth] using
        (show (0 : Fraction.Rational) ≤ 1 / 8 by decide)) 2
  have residualBudget : 14 * eighth ^ 3 ≤ 1 / 32 := by
    have squareNonnegative : 0 ≤ eighth ^ 2 :=
      eighthSquareNonnegative
    calc
      14 * eighth ^ 3 = (14 * eighth) * eighth ^ 2 := by ring1
      _ ≤ 2 * eighth ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          coefficientBound squareNonnegative
      _ = 1 / 32 := by simp only [eighth]; decide
  calc
    normSq ((p.eval point - p.eval source.box.anchor) +
        p.eval source.box.anchor) ≤
      2 * (normSq (p.eval point - p.eval source.box.anchor) +
        normSq (p.eval source.box.anchor)) := Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (6 * eighth ^ 3 + eighth ^ 3) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add variation anchorResidual) (by decide)
    _ = 14 * eighth ^ 3 := by ring1
    _ ≤ 1 / 32 := residualBudget
end Purelib.RootIsolation.Power.Unit.Box.Residual

end
