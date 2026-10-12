module

import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Digits
public import Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Table
public import Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Return
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Floor
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Region.Gaussian.UnitSquare

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic

/-!
# Three-step coordinate-floor contraction

The original coordinate-floor return program and Gaussian digits retain
their exact unit-square remainders. Integer translation bounds and the
original finite exceptional table prove the stated three-step quadrance bound.
-/

namespace Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Basic

open Purelib.Algebra
open Purelib.Data
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Region

/-- The exceptional successive digits one minus i and one minus two i cannot occur in three retained unit-square
remainders.

Both preceding remainders are nonzero and satisfy the exact gamma-inverse branch identities. Their coordinate equations
force the first imaginary coordinate above one, contradicting the half-open square bound. -/
public theorem cross_pair_impossible (u v w : Basic.Canonical)
    (uNonzero : u ≠ 0) (vNonzero : v ≠ 0)
    (uInside : Gaussian.UnitSquare.Sq u)
    (vInside : Gaussian.UnitSquare.Sq v)
    (wInside : Gaussian.UnitSquare.Sq w)
    (uBranch : Basic.Canonical.gamma * u⁻¹ = GaussianInt.toGaussian (Contraction.Digits.tau .d1) + v)
    (vBranch : Basic.Canonical.gamma * v⁻¹ = GaussianInt.toGaussian (Contraction.Digits.tau .d0) + w) : False := by
  rcases uInside with ⟨_, _, _, uImagSmall⟩
  rcases vInside with ⟨vRealNonnegative, _, _, _⟩
  rcases wInside with ⟨_, _, _, wImagSmall⟩
  have vProduct : v * (GaussianInt.toGaussian (Contraction.Digits.tau .d0) + w) = Basic.Canonical.gamma := by
    rw [← vBranch]
    exact Constants.mul_quotient_eq_gamma v vNonzero
  have vRealEquation :=
    congrArg Basic.re vProduct
  have vImagEquation :=
    congrArg Basic.im vProduct
  change v.re * (1 + w.re) - v.im * (-2 + w.im) = 1 at vRealEquation
  change v.re * (-2 + w.im) + v.im * (1 + w.re) = 1 at vImagEquation
  let A : Fraction.Rational := 1 + w.re
  let B : Fraction.Rational := 2 - w.im
  let R : Fraction.Rational := A ^ 2 + B ^ 2
  have realLinear : v.re * A + v.im * B = 1 := by
    calc
      v.re * A + v.im * B =
          v.re * (1 + w.re) - v.im * (-2 + w.im) := by
        dsimp only [A, B]
        ring1
      _ = 1 := vRealEquation
  have imagLinear : -v.re * B + v.im * A = 1 := by
    calc
      -v.re * B + v.im * A =
          v.re * (-2 + w.im) + v.im * (1 + w.re) := by
        dsimp only [A, B]
        ring1
      _ = 1 := vImagEquation
  have bGreaterOne : 1 < B := by
    apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    dsimp only [B]
    have positive := Fraction.Order.Arithmetic.sub_pos_direct wImagSmall
    calc
      (2 - w.im) - 1 = 1 - w.im := by ring1
      _ > 0 := positive
  have bPositive : 0 < B := (by decide : (0 : Fraction.Rational) < 1).trans
    bGreaterOne
  have rPositive : 0 < R := by
    have aSquareNonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct A
    have bSquarePositive : 0 < B ^ 2 := by
      rw [pow_two]
      exact Fraction.Order.Arithmetic.mul_pos_direct bPositive bPositive
    exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct aSquareNonnegative bSquarePositive
  have realTimesR : v.re * R = A - B := by
    calc
      v.re * R = A * (v.re * A + v.im * B) -
          B * (-v.re * B + v.im * A) := by
        dsimp only [R]
        ring1
      _ = A * 1 - B * 1 := by rw [realLinear, imagLinear]
      _ = A - B := by ring1
  have imagTimesR : v.im * R = A + B := by
    calc
      v.im * R = B * (v.re * A + v.im * B) +
          A * (-v.re * B + v.im * A) := by
        dsimp only [R]
        ring1
      _ = B * 1 + A * 1 := by rw [realLinear, imagLinear]
      _ = A + B := by ring1
  have normTimesR : (v.re ^ 2 + v.im ^ 2) * R = 2 := by
    calc
      (v.re ^ 2 + v.im ^ 2) * R =
          v.re * (v.re * R) + v.im * (v.im * R) := by ring1
      _ = v.re * (A - B) + v.im * (A + B) := by
        rw [realTimesR, imagTimesR]
      _ = (v.re * A + v.im * B) + (-v.re * B + v.im * A) := by
        ring1
      _ = 1 + 1 := by rw [realLinear, imagLinear]
      _ = 2 := by ring1
  let numerator : Fraction.Rational :=
    v.im * (1 - v.im) - v.re * (1 + v.re)
  have numeratorTimesR : numerator * R = 2 * (B - 1) := by
    calc
      numerator * R = v.im * R - v.re * R -
          (v.re ^ 2 + v.im ^ 2) * R := by
        dsimp only [numerator]
        ring1
      _ = (A + B) - (A - B) - 2 := by
        rw [imagTimesR, realTimesR, normTimesR]
      _ = 2 * (B - 1) := by ring1
  have numeratorProductPositive : 0 < numerator * R := by
    rw [numeratorTimesR]
    exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.sub_pos_direct bGreaterOne)
  have numeratorPositive : 0 < numerator := by
    have reordered : 0 < R * numerator := by
      rwa [Fraction.Field.mul_comm]
    exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
      reordered rPositive.le
  have uProduct : u * (GaussianInt.toGaussian (Contraction.Digits.tau .d1) + v) = Basic.Canonical.gamma := by
    rw [← uBranch]
    exact Constants.mul_quotient_eq_gamma u uNonzero
  have uRealEquation :=
    congrArg Basic.re uProduct
  have uImagEquation :=
    congrArg Basic.im uProduct
  change u.re * (1 + v.re) - u.im * (-1 + v.im) = 1 at uRealEquation
  change u.re * (-1 + v.im) + u.im * (1 + v.re) = 1 at uImagEquation
  let D : Fraction.Rational := (1 + v.re) ^ 2 + (v.im - 1) ^ 2
  have onePlusRealPositive : 0 < 1 + v.re := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      vRealNonnegative 1
    have oneLe : (1 : Fraction.Rational) ≤ 1 + v.re := by
      calc
        (1 : Fraction.Rational) = 0 + 1 := by ring1
        _ ≤ v.re + 1 := shifted
        _ = 1 + v.re := by ring1
    exact (by decide : (0 : Fraction.Rational) < 1).trans_le oneLe
  have dPositive : 0 < D := by
    have firstPositive : 0 < (1 + v.re) ^ 2 := by
      rw [pow_two]
      exact Fraction.Order.Arithmetic.mul_pos_direct
        onePlusRealPositive onePlusRealPositive
    exact Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstPositive
      (Fraction.Order.Arithmetic.sq_nonneg_direct (v.im - 1))
  have imagTimesD : u.im * D = 2 + v.re - v.im := by
    calc
      u.im * D = -(v.im - 1) *
          (u.re * (1 + v.re) - u.im * (-1 + v.im)) +
          (1 + v.re) *
            (u.re * (-1 + v.im) + u.im * (1 + v.re)) := by
        dsimp only [D]
        ring1
      _ = -(v.im - 1) * 1 + (1 + v.re) * 1 := by
        rw [uRealEquation, uImagEquation]
      _ = 2 + v.re - v.im := by ring1
  have shiftedTimesD : (u.im - 1) * D = numerator := by
    calc
      (u.im - 1) * D = u.im * D - D := by ring1
      _ = (2 + v.re - v.im) - D := by rw [imagTimesD]
      _ = numerator := by
        dsimp only [D, numerator]
        ring1
  have shiftedProductPositive : 0 < (u.im - 1) * D := by
    rw [shiftedTimesD]
    exact numeratorPositive
  have shiftedPositive : 0 < u.im - 1 := by
    have reordered : 0 < D * (u.im - 1) := by
      rwa [Fraction.Field.mul_comm]
    exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
      reordered dPositive.le
  have oneLessImag := Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    shiftedPositive
  exact (lt_asymm oneLessImag uImagSmall).elim

/-- Three successive coordinate-floor remainders have product squared norm strictly below one.

The initial remainder lies in the half-open unit square, and it and its first return are nonzero. The proof combines the
integer digit lower bounds with the finite exceptional-digit inequalities, preserving the original return map. -/
public theorem three_step_contraction (u : Basic.Canonical) (uNonzero : u ≠ 0)
    (uInside : Gaussian.UnitSquare.Sq u)
    (vNonzero : Return.step u ≠ 0) :
    Gaussian.Norm.Basic.normSq (u * Return.step u *
      Return.step
        (Return.step u)) < 1 := by
  let v := Return.step u
  let w := Return.step v
  let t := GaussianInt.Floor.floor (Basic.Canonical.gamma * u⁻¹)
  let t' := GaussianInt.Floor.floor (Basic.Canonical.gamma * v⁻¹)
  have vInside : Gaussian.UnitSquare.Sq v := by
    dsimp only [v]
    exact Return.step_sq u
  have wInside : Gaussian.UnitSquare.Sq w := by
    dsimp only [w]
    exact Return.step_sq v
  have uBranch : Basic.Canonical.gamma * u⁻¹ = GaussianInt.toGaussian t + v := by
    symm
    simpa only [t, v] using
      Return.floor_add_step u
  have vBranch : Basic.Canonical.gamma * v⁻¹ = GaussianInt.toGaussian t' + w := by
    symm
    simpa only [t', w] using
      Return.floor_add_step v
  have tCone : 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re := by
    simpa only [t] using Return.digit_cone
      u uNonzero uInside
  have t'Cone : 1 ≤ t'.re ∧ -t'.re - 1 ≤ t'.im ∧ t'.im ≤ t'.re := by
    simpa only [t'] using Return.digit_cone
      v vNonzero vInside
  have uProduct : u * (GaussianInt.toGaussian t + v) = Basic.Canonical.gamma := by
    rw [← uBranch]
    exact Constants.mul_quotient_eq_gamma u uNonzero
  have vProduct : v * (GaussianInt.toGaussian t' + w) = Basic.Canonical.gamma := by
    rw [← vBranch]
    exact Constants.mul_quotient_eq_gamma v vNonzero
  have uNorm := congrArg Gaussian.Norm.Basic.normSq uProduct
  have vNorm := congrArg Gaussian.Norm.Basic.normSq vProduct
  rw [Norm.Basic.normSq_mul, Constants.normSq_gamma] at uNorm vNorm
  have denominatorInequality :
      4 * Gaussian.Norm.Basic.normSq w <
        Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t + v) * Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian
          t' + w) := by
    by_cases coarse : 8 ≤ Contraction.Digits.lambda t * Contraction.Digits.lambda t'
    · have tLower := Contraction.Table.lambda_le_norm_translate t (by omega) v vInside
      have t'Lower := Contraction.Table.lambda_le_norm_translate t' (by omega) w wInside
      have productLower :
          ((Contraction.Digits.lambda t * Contraction.Digits.lambda t' : Int) : Fraction.Rational) ≤
            Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t + v) * Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian t' + w) := by
        rw [Ring.IntCast.intCast_mul]
        exact Fraction.Order.Arithmetic.mul_le_mul_direct tLower t'Lower
          (Fraction.Cast.Order.cast_int_nonnegative (Contraction.Digits.lambda_nonnegative t'))
          (Norm.Basic.normSq_nonneg (GaussianInt.toGaussian t + v))
      have coarseCast : (8 : Fraction.Rational) ≤
          ((Contraction.Digits.lambda t * Contraction.Digits.lambda t' : Int) : Fraction.Rational) := by
        have cast :=
          (Fraction.Cast.Order.intCast_le_intCast_iff_direct
            8 (Contraction.Digits.lambda t * Contraction.Digits.lambda t')).2 coarse
        simpa only [Int.cast_ofNat] using cast
      have fourTimesNormLess : 4 * Gaussian.Norm.Basic.normSq w < 8 := by
        have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide : (0 : Fraction.Rational) < 4)
          (Gaussian.UnitSquare.normSq_lt_two_of_sq wInside)
        calc
          4 * Gaussian.Norm.Basic.normSq w < 4 * 2 := scaled
          _ = 8 := by ring1
      exact fourTimesNormLess.trans_le (coarseCast.trans productLower)
    · have productSmall : Contraction.Digits.lambda t * Contraction.Digits.lambda t' < 8 :=
        Int.Order.lt_of_not_le coarse
      have tOne := Contraction.Digits.one_le_lambda_of_cone t tCone
      have t'One := Contraction.Digits.one_le_lambda_of_cone t' t'Cone
      have tSmall : Contraction.Digits.lambda t < 8 := by
        have factorOrder : Contraction.Digits.lambda t ≤ Contraction.Digits.lambda t * Contraction.Digits.lambda t' :=
          by
          calc
            Contraction.Digits.lambda t = Contraction.Digits.lambda t * 1 := (Int.Arithmetic.mul_one _).symm
            _ ≤ Contraction.Digits.lambda t * Contraction.Digits.lambda t' :=
              Int.Order.mul_le_mul_of_nonneg_left t'One (Contraction.Digits.lambda_nonnegative t)
        omega0
      have t'Small : Contraction.Digits.lambda t' < 8 := by
        have factorOrder : Contraction.Digits.lambda t' ≤ Contraction.Digits.lambda t * Contraction.Digits.lambda t' :=
          by
          calc
            Contraction.Digits.lambda t' = 1 * Contraction.Digits.lambda t' := (Int.one_mul _).symm
            _ ≤ Contraction.Digits.lambda t * Contraction.Digits.lambda t' :=
              Int.Order.mul_le_mul_of_nonneg_right tOne (Contraction.Digits.lambda_nonnegative t')
        omega0
      obtain ⟨r, tEqual⟩ := Contraction.Digits.exists_small_of_cone t tCone tSmall
      obtain ⟨c, t'Equal⟩ := Contraction.Digits.exists_small_of_cone t' t'Cone t'Small
      have notCrossed : ¬ (r = .d1 ∧ c = .d0) := by
        rintro ⟨rfl, rfl⟩
        apply Contraction.Basic.cross_pair_impossible u v w uNonzero vNonzero
          uInside vInside wInside
        · simpa only [tEqual] using uBranch
        · simpa only [t'Equal] using vBranch
      have tablePositive := Contraction.Table.delta_pos_of_small r c w wInside
        (by simpa only [← tEqual, ← t'Equal] using productSmall)
        notCrossed
      have vProduct' : v * (GaussianInt.toGaussian (Contraction.Digits.tau c) + w) = Basic.Canonical.gamma := by
        simpa only [t'Equal] using vProduct
      have factorIdentity :
          GaussianInt.toGaussian (Contraction.Digits.tau r) * (GaussianInt.toGaussian (Contraction.Digits.tau c) + w) +
            Basic.Canonical.gamma =
            (GaussianInt.toGaussian (Contraction.Digits.tau r) + v) * (GaussianInt.toGaussian (Contraction.Digits.tau c)
              + w) := by
        rw [Basic.right_distrib, vProduct']
      rw [Contraction.Table.delta, factorIdentity, Norm.Basic.normSq_mul] at tablePositive
      have translated := Fraction.Order.Arithmetic.lt_of_sub_pos_direct
        tablePositive
      simpa only [tEqual, t'Equal] using translated
  have productIdentity :
      Gaussian.Norm.Basic.normSq (u * v * w) *
          (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t + v) * Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian t' + w)) =
        4 * Gaussian.Norm.Basic.normSq w := by
    rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    calc
      (Gaussian.Norm.Basic.normSq u * Gaussian.Norm.Basic.normSq v * Gaussian.Norm.Basic.normSq w) *
          (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t + v) * Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian t' + w)) =
          (Gaussian.Norm.Basic.normSq u * Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t + v)) *
            (Gaussian.Norm.Basic.normSq v * Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t' + w)) *
              Gaussian.Norm.Basic.normSq w := by
        ring1
      _ = 2 * 2 * Gaussian.Norm.Basic.normSq w := by rw [uNorm, vNorm]
      _ = 4 * Gaussian.Norm.Basic.normSq w := by ring1
  have denominatorPositive :
      0 < Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t + v) * Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian
        t' + w) := by
    have leftNonnegative : 0 ≤ 4 * Gaussian.Norm.Basic.normSq w :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Norm.Basic.normSq_nonneg w)
    exact leftNonnegative.trans_lt denominatorInequality
  have scaledResult :
      Gaussian.Norm.Basic.normSq (u * v * w) *
          (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t + v) * Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian t' + w)) <
        1 * (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t + v) * Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian t' + w)) := by
    rw [productIdentity]
    simpa only [Fraction.Field.one_mul] using denominatorInequality
  have result := Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    scaledResult denominatorPositive
  simpa only [v, w] using result

end Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Basic
