module
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Monoid.Int
import Purelib.Algebra.NatCast
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Conjugate
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.SignedFraction.Arithmetic
import Purelib.Data.Rat.SignedFraction.Basic
import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.Data.Rat.SignedFraction.Order
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Chambers
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Optimal
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Bounds
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Optimal
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.NumberTheory.Approximation.Best.Consecutive.Index
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

section
public section

open Purelib.Algebra
attribute [local instance 2000] Group.Negation.subNegZeroMonoid

/-!
# Determinant-index-one Dirichlet windows

The generic nearest-coefficient argument uses only one Gaussian-integer
candidate.  At determinant index one every ambient coefficient is available,
so three neighbouring coefficients in the octant containing the normalized
error ratio give a stronger finite gap.  This file first proves the exact
first-octant calculation.  Its hypotheses are only rational coordinate
inequalities and three explicit empty-cylinder alternatives.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Bounds

/-- Compose a strict rational coordinate inequality with a weak upper bound. -/
private theorem lt_of_lt_of_le_coordinate
    {a b c : Fraction.Rational} (first : a < b) (second : b ≤ c) : a < c :=
  ⟨first.1.trans second, fun reverse => first.2 (second.trans reverse)⟩

/-- A weighted dot-product bound gives a determinant gap of at least `1/2`.

The second squared norm is at most one, and four times the dot product is bounded by `(1 + 2 * xNorm) * yNorm`. -/
private theorem half_le_of_fourDot_le
    (xNorm yNorm dot : Fraction.Rational)
    (yNormLeOne : yNorm ≤ 1)
    (fourDotBound : 4 * dot ≤ (1 + 2 * xNorm) * yNorm) :
    (1 / 2 : Fraction.Rational) ≤ 1 + xNorm * yNorm - 2 * dot := by
  have oneLeBaseline : (1 : Fraction.Rational) ≤ 2 - yNorm := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 1 - yNorm :=
        Fraction.Order.Arithmetic.sub_nonneg_direct yNormLeOne
      _ = (2 - yNorm) - 1 := by ring1
  have negated :=
    Fraction.Order.Arithmetic.neg_le_neg_direct fourDotBound
  have oneLeTwiceGap :
      (1 : Fraction.Rational) ≤ 2 * (1 + xNorm * yNorm - 2 * dot) := by
    calc
      (1 : Fraction.Rational) ≤ 2 - yNorm := oneLeBaseline
      _ = 2 + 2 * xNorm * yNorm - (1 + 2 * xNorm) * yNorm := by
        ring1
      _ ≤ 2 + 2 * xNorm * yNorm - 4 * dot := by
        have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
          negated (2 + 2 * xNorm * yNorm)
        calc
          2 + 2 * xNorm * yNorm - (1 + 2 * xNorm) * yNorm =
              -((1 + 2 * xNorm) * yNorm) +
                (2 + 2 * xNorm * yNorm) := by ring1
          _ ≤ -(4 * dot) + (2 + 2 * xNorm * yNorm) := shifted
          _ = 2 + 2 * xNorm * yNorm - 4 * dot := by ring1
      _ = 2 * (1 + xNorm * yNorm - 2 * dot) := by ring1
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      (1 / 2 : Fraction.Rational) * 2 = 1 := by decide
      _ ≤ 2 * (1 + xNorm * yNorm - 2 * dot) := oneLeTwiceGap
      _ = (1 + xNorm * yNorm - 2 * dot) * 2 := by ring1
  · decide

/-- The boundary dot-product inequality gives a gap of at least `1/2`.

Both squared norms are at most one; the assumed bound on four times the dot product includes their product and both
boundary contributions. -/
private theorem half_le_of_fourDot_le_boundary
    (xNorm yNorm dot : Fraction.Rational)
    (xNormLeOne : xNorm ≤ 1)
    (yNormLeOne : yNorm ≤ 1)
    (fourDotBound : 4 * dot ≤ yNorm * (xNorm + 1) + xNorm) :
    (1 / 2 : Fraction.Rational) ≤ 1 + xNorm * yNorm - 2 * dot := by
  have oneMinusXNonnegative : 0 ≤ 1 - xNorm :=
    Fraction.Order.Arithmetic.sub_nonneg_direct xNormLeOne
  have oneMinusYNonnegative : 0 ≤ 1 - yNorm :=
    Fraction.Order.Arithmetic.sub_nonneg_direct yNormLeOne
  have productNonnegative : 0 ≤ (1 - xNorm) * (1 - yNorm) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct oneMinusXNonnegative
      oneMinusYNonnegative
  have oneLeBaseline :
      (1 : Fraction.Rational) ≤ 1 + (1 - xNorm) * (1 - yNorm) :=
    le_add_of_nonneg_right productNonnegative
  have negated :=
    Fraction.Order.Arithmetic.neg_le_neg_direct fourDotBound
  have oneLeTwiceGap :
      (1 : Fraction.Rational) ≤ 2 * (1 + xNorm * yNorm - 2 * dot) := by
    calc
      (1 : Fraction.Rational) ≤ 1 + (1 - xNorm) * (1 - yNorm) := oneLeBaseline
      _ = 2 + 2 * xNorm * yNorm -
          (yNorm * (xNorm + 1) + xNorm) := by ring1
      _ ≤ 2 + 2 * xNorm * yNorm - 4 * dot := by
        have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
          negated (2 + 2 * xNorm * yNorm)
        calc
          2 + 2 * xNorm * yNorm -
                (yNorm * (xNorm + 1) + xNorm) =
              -(yNorm * (xNorm + 1) + xNorm) +
                (2 + 2 * xNorm * yNorm) := by ring1
          _ ≤ -(4 * dot) + (2 + 2 * xNorm * yNorm) := shifted
          _ = 2 + 2 * xNorm * yNorm - 4 * dot := by ring1
      _ = 2 * (1 + xNorm * yNorm - 2 * dot) := by ring1
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      (1 / 2 : Fraction.Rational) * 2 = 1 := by decide
      _ ≤ 2 * (1 + xNorm * yNorm - 2 * dot) := oneLeTwiceGap
      _ = (1 + xNorm * yNorm - 2 * dot) * 2 := by ring1
  · decide

/-- Convert a dot-product upper bound into a determinant-gap lower bound.

The allowance `1/4` above the product of squared norms leaves a gap of at least `3/4`. -/
private theorem three_quarters_le_of_twiceDot_le
    (xNorm yNorm dot : Fraction.Rational)
    (twiceDotBound : 2 * dot ≤ xNorm * yNorm + 1 / 4) :
    (3 / 4 : Fraction.Rational) ≤ 1 + xNorm * yNorm - 2 * dot := by
  have negated := Fraction.Order.Arithmetic.neg_le_neg_direct twiceDotBound
  calc
    (3 / 4 : Fraction.Rational) =
        1 + xNorm * yNorm - (xNorm * yNorm + 1 / 4) := by
      rw [show (3 / 4 : Fraction.Rational) = 1 - 1 / 4 by decide]
      ring1
    _ = -(xNorm * yNorm + 1 / 4) + (1 + xNorm * yNorm) := by
      ring1
    _ ≤ -(2 * dot) + (1 + xNorm * yNorm) :=
      Fraction.Order.Arithmetic.add_le_add_right_direct
        negated (1 + xNorm * yNorm)
    _ = 1 + xNorm * yNorm - 2 * dot := by ring1

/-- Bound a coordinate times a squared norm by the product of norms plus `1/4`.

The first norm is the sum of the two displayed coordinate squares, and the second lies between zero and one. Completing
the coordinate square supplies the bound. -/
private theorem component_mul_norm_le_product_add_quarter
    (component other firstNorm secondNorm : Fraction.Rational)
    (firstNormIdentity : firstNorm = component ^ 2 + other ^ 2)
    (secondNormNonnegative : 0 ≤ secondNorm)
    (secondNormLeOne : secondNorm ≤ 1) :
    component * secondNorm ≤ firstNorm * secondNorm + 1 / 4 := by
  have squareSumNonnegative :
      0 ≤ (component - 1 / 2) ^ 2 + other ^ 2 :=
    add_nonneg
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have weightedSquaresNonnegative :
      0 ≤ secondNorm * ((component - 1 / 2) ^ 2 + other ^ 2) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct secondNormNonnegative
      squareSumNonnegative
  have complementNonnegative : 0 ≤ 1 - secondNorm :=
    Fraction.Order.Arithmetic.sub_nonneg_direct secondNormLeOne
  have weightedComplementNonnegative :
      0 ≤ (1 - secondNorm) * (1 / 4) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct complementNonnegative
      (by decide)
  have shiftedSquareIdentity :
      (component - 1 / 2) ^ 2 =
        component ^ 2 - component + 1 / 4 := by
    calc
      (component - 1 / 2) ^ 2 =
          component ^ 2 - component * (1 / 2 + 1 / 2) +
            (1 / 2) ^ 2 := by ring1
      _ = component ^ 2 - component * 1 + (1 / 2) ^ 2 := by
        rw [show (1 / 2 : Fraction.Rational) + 1 / 2 = 1 by decide]
      _ = component ^ 2 - component + 1 / 4 := by
        rw [show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide]
        ring1
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ secondNorm * ((component - 1 / 2) ^ 2 + other ^ 2) +
        (1 - secondNorm) * (1 / 4) :=
      add_nonneg weightedSquaresNonnegative weightedComplementNonnegative
    _ = (firstNorm * secondNorm + 1 / 4) -
        component * secondNorm := by
      rw [firstNormIdentity, shiftedSquareIdentity]
      ring1

/-- Axis obstructions exclude a positive real and negative imaginary coordinate together.

For a point strictly inside the unit disk, the two coordinate inequalities force one of the stated weak sign conditions.
-/
private theorem real_nonpositive_or_imaginary_nonnegative_of_axisObstructions
    (value : Gaussian.Basic.Canonical)
    (inside : Data.Gaussian.Norm.Basic.normSq value < 1)
    (realObstruction : 2 * value.re ≤ Data.Gaussian.Norm.Basic.normSq value)
    (imaginaryObstruction : -2 * value.im ≤ Data.Gaussian.Norm.Basic.normSq value) :
    value.re ≤ 0 ∨ 0 ≤ value.im := by
  by_cases realNonpositive : value.re ≤ 0
  · exact Or.inl realNonpositive
  · have realPositive : 0 < value.re :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct realNonpositive
    by_cases imaginaryNonnegative : 0 ≤ value.im
    · exact Or.inr imaginaryNonnegative
    · have imaginaryNegative : value.im < 0 :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct imaginaryNonnegative
      have negImaginaryPositive : 0 < -value.im := by
        have positive :=
          Fraction.Order.Arithmetic.sub_pos_direct imaginaryNegative
        calc
          0 < 0 - value.im := positive
          _ = -value.im := by ring1
      have twiceNegImaginaryLeNorm :
          2 * (-value.im) ≤ Data.Gaussian.Norm.Basic.normSq value := by
        calc
          2 * (-value.im) = -2 * value.im := by ring1
          _ ≤ Data.Gaussian.Norm.Basic.normSq value := imaginaryObstruction
      have twiceSumLeNorm :
          2 * (value.re + -value.im) ≤ 2 * Data.Gaussian.Norm.Basic.normSq value := by
        have added := Fraction.Order.Arithmetic.add_le_add_direct
          realObstruction twiceNegImaginaryLeNorm
        calc
          2 * (value.re + -value.im) =
              2 * value.re + 2 * (-value.im) := by ring1
          _ ≤ Data.Gaussian.Norm.Basic.normSq value + Data.Gaussian.Norm.Basic.normSq value := added
          _ = 2 * Data.Gaussian.Norm.Basic.normSq value := by ring1
      have sumLeNorm : value.re + -value.im ≤ Data.Gaussian.Norm.Basic.normSq value := by
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
        · calc
            (value.re + -value.im) * 2 =
                2 * (value.re + -value.im) := by ring1
            _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq value := twiceSumLeNorm
            _ = Data.Gaussian.Norm.Basic.normSq value * 2 := by ring1
        · decide
      have realLtOne : value.re < 1 :=
        Dirichlet.Window.IndexOne.Bounds.lt_of_lt_of_le_coordinate
          (by
            have shifted :=
              Fraction.Order.Arithmetic.add_lt_add_left_direct
                negImaginaryPositive value.re
            calc
              value.re = value.re + 0 := by ring1
              _ < value.re + -value.im := shifted)
          (sumLeNorm.trans
            (Fraction.Order.Arithmetic.le_of_lt_direct inside))
      have negImaginaryLtOne : -value.im < 1 :=
        Dirichlet.Window.IndexOne.Bounds.lt_of_lt_of_le_coordinate
          (by
            have shifted :=
              Fraction.Order.Arithmetic.add_lt_add_right_direct
                realPositive (-value.im)
            calc
              -value.im = 0 + -value.im := by ring1
              _ < value.re + -value.im := shifted)
          (sumLeNorm.trans
            (Fraction.Order.Arithmetic.le_of_lt_direct inside))
      have realSquareLtReal : value.re ^ 2 < value.re := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            realPositive realLtOne
        calc
          value.re ^ 2 = value.re * value.re := by ring1
          _ < value.re * 1 := scaled
          _ = value.re := by ring1
      have negImaginarySquareLtNegImaginary :
          (-value.im) ^ 2 < -value.im := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            negImaginaryPositive negImaginaryLtOne
        calc
          (-value.im) ^ 2 = (-value.im) * (-value.im) := by ring1
          _ < (-value.im) * 1 := scaled
          _ = -value.im := by ring1
      have normLtSum : Data.Gaussian.Norm.Basic.normSq value < value.re + -value.im := by
        have added := Fraction.Order.Arithmetic.add_lt_add_direct
          realSquareLtReal negImaginarySquareLtNegImaginary
        dsimp only [Data.Gaussian.Norm.Basic.normSq]
        calc
          value.re ^ 2 + value.im ^ 2 =
              value.re ^ 2 + (-value.im) ^ 2 := by ring1
          _ < value.re + -value.im := added
      exact (normLtSum.2 sumLeNorm).elim

/-- A diagonal obstruction excludes the open fourth quadrant inside the unit disk.

The bound on the real coordinate minus the imaginary coordinate forces a nonpositive real part or a nonnegative
imaginary part. -/
private theorem real_nonpositive_or_imaginary_nonnegative_of_diagonalObstructions
    (value : Gaussian.Basic.Canonical)
    (inside : Data.Gaussian.Norm.Basic.normSq value < 1)
    (diagonalObstruction : value.re - value.im ≤ Data.Gaussian.Norm.Basic.normSq value) :
    value.re ≤ 0 ∨ 0 ≤ value.im := by
  by_cases realNonpositive : value.re ≤ 0
  · exact Or.inl realNonpositive
  · have realPositive : 0 < value.re :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct realNonpositive
    by_cases imaginaryNonnegative : 0 ≤ value.im
    · exact Or.inr imaginaryNonnegative
    · have imaginaryNegative : value.im < 0 :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct imaginaryNonnegative
      have negImaginaryPositive : 0 < -value.im := by
        have positive :=
          Fraction.Order.Arithmetic.sub_pos_direct imaginaryNegative
        calc
          0 < 0 - value.im := positive
          _ = -value.im := by ring1
      have sumLeNorm : value.re + -value.im ≤ Data.Gaussian.Norm.Basic.normSq value := by
        calc
          value.re + -value.im = value.re - value.im := by ring1
          _ ≤ Data.Gaussian.Norm.Basic.normSq value := diagonalObstruction
      have realLtOne : value.re < 1 :=
        Dirichlet.Window.IndexOne.Bounds.lt_of_lt_of_le_coordinate
          (by
            have shifted :=
              Fraction.Order.Arithmetic.add_lt_add_left_direct
                negImaginaryPositive value.re
            calc
              value.re = value.re + 0 := by ring1
              _ < value.re + -value.im := shifted)
          (sumLeNorm.trans
            (Fraction.Order.Arithmetic.le_of_lt_direct inside))
      have negImaginaryLtOne : -value.im < 1 :=
        Dirichlet.Window.IndexOne.Bounds.lt_of_lt_of_le_coordinate
          (by
            have shifted :=
              Fraction.Order.Arithmetic.add_lt_add_right_direct
                realPositive (-value.im)
            calc
              -value.im = 0 + -value.im := by ring1
              _ < value.re + -value.im := shifted)
          (sumLeNorm.trans
            (Fraction.Order.Arithmetic.le_of_lt_direct inside))
      have realSquareLtReal : value.re ^ 2 < value.re := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            realPositive realLtOne
        calc
          value.re ^ 2 = value.re * value.re := by ring1
          _ < value.re * 1 := scaled
          _ = value.re := by ring1
      have negImaginarySquareLtNegImaginary :
          (-value.im) ^ 2 < -value.im := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            negImaginaryPositive negImaginaryLtOne
        calc
          (-value.im) ^ 2 = (-value.im) * (-value.im) := by ring1
          _ < (-value.im) * 1 := scaled
          _ = -value.im := by ring1
      have normLtSum : Data.Gaussian.Norm.Basic.normSq value < value.re + -value.im := by
        have added := Fraction.Order.Arithmetic.add_lt_add_direct
          realSquareLtReal negImaginarySquareLtNegImaginary
        dsimp only [Data.Gaussian.Norm.Basic.normSq]
        calc
          value.re ^ 2 + value.im ^ 2 =
              value.re ^ 2 + (-value.im) ^ 2 := by ring1
          _ < value.re + -value.im := added
      exact (normLtSum.2 sumLeNorm).elim

/-- The two axis obstructions give a determinant gap of at least `3/4`.

The error coordinates are nonnegative and the denominator ratio lies inside the unit disk. The denominator sign
alternative bounds the real part of their product. -/
private theorem three_quarters_le_of_axisChamber
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (denominatorRealObstruction :
      2 * denominatorRatio.re ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio)
    (denominatorImaginaryObstruction :
      -2 * denominatorRatio.im ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio) :
    (3 / 4 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let xNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  let yNorm := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  let dot := errorRatio.re * denominatorRatio.re -
    errorRatio.im * denominatorRatio.im
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact Gaussian.Norm.Basic.normSq_nonneg denominatorRatio
  have yNormLeOne : yNorm ≤ 1 := denominatorInside.le
  have realComponentBound :
      errorRatio.re * yNorm ≤ xNorm * yNorm + 1 / 4 := by
    apply Dirichlet.Window.IndexOne.Bounds.component_mul_norm_le_product_add_quarter
        errorRatio.re errorRatio.im xNorm yNorm
    · rfl
    · exact yNormNonnegative
    · exact yNormLeOne
  have imaginaryComponentBound :
      errorRatio.im * yNorm ≤ xNorm * yNorm + 1 / 4 := by
    apply Dirichlet.Window.IndexOne.Bounds.component_mul_norm_le_product_add_quarter
        errorRatio.im errorRatio.re xNorm yNorm
    · dsimp only [xNorm, Data.Gaussian.Norm.Basic.normSq]
      ring1
    · exact yNormNonnegative
    · exact yNormLeOne
  have gapExpansion :
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, Data.Gaussian.Norm.Basic.normSq]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im]
    ring1
  have signAlternative :=
    Dirichlet.Window.IndexOne.Bounds.real_nonpositive_or_imaginary_nonnegative_of_axisObstructions
      denominatorRatio denominatorInside denominatorRealObstruction
        denominatorImaginaryObstruction
  rw [gapExpansion]
  apply Dirichlet.Window.IndexOne.Bounds.three_quarters_le_of_twiceDot_le xNorm yNorm dot
  rcases signAlternative with realNonpositive | imaginaryNonnegative
  · have realProductNonpositive :
        errorRatio.re * denominatorRatio.re ≤ 0 := by
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          realNonpositive errorRealNonnegative
      calc
        errorRatio.re * denominatorRatio.re ≤ errorRatio.re * 0 := scaled
        _ = 0 := by ring1
    have dotLeImaginaryProduct :
        dot ≤ errorRatio.im * (-denominatorRatio.im) := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      dsimp only [dot]
      calc
        0 ≤ -(errorRatio.re * denominatorRatio.re) :=
          by
            have shifted := Fraction.Order.Arithmetic.neg_le_neg_direct realProductNonpositive
            simpa only [neg_zero] using shifted
        _ = errorRatio.im * (-denominatorRatio.im) -
            (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by ring1
    have twiceDotLeImaginary :
        2 * dot ≤ errorRatio.im * yNorm := by
      have doubled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          dotLeImaginaryProduct (show (0 : Fraction.Rational) ≤ 2 by decide)
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          denominatorImaginaryObstruction errorImaginaryNonnegative
      calc
        2 * dot ≤ 2 * (errorRatio.im * (-denominatorRatio.im)) := doubled
        _ = errorRatio.im * (-2 * denominatorRatio.im) := by ring1
        _ ≤ errorRatio.im * yNorm := scaled
    exact twiceDotLeImaginary.trans imaginaryComponentBound
  · have imaginaryProductNonnegative :
        0 ≤ errorRatio.im * denominatorRatio.im :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        errorImaginaryNonnegative imaginaryNonnegative
    have dotLeRealProduct :
        dot ≤ errorRatio.re * denominatorRatio.re := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      dsimp only [dot]
      calc
        0 ≤ errorRatio.im * denominatorRatio.im :=
          imaginaryProductNonnegative
        _ = errorRatio.re * denominatorRatio.re -
            (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by ring1
    have twiceDotLeReal : 2 * dot ≤ errorRatio.re * yNorm := by
      have doubled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          dotLeRealProduct (show (0 : Fraction.Rational) ≤ 2 by decide)
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          denominatorRealObstruction errorRealNonnegative
      calc
        2 * dot ≤ 2 * (errorRatio.re * denominatorRatio.re) := doubled
        _ = errorRatio.re * (2 * denominatorRatio.re) := by ring1
        _ ≤ errorRatio.re * yNorm := scaled
    exact twiceDotLeReal.trans realComponentBound

/-- The diagonal denominator chamber gives a determinant gap of at least `3/4`.

Both ratios lie inside the unit disk. The error has nonnegative coordinates, and the imaginary, real and diagonal
obstructions control the product contribution. -/
private theorem three_quarters_le_of_diagonalDenominatorChamber
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (errorImaginaryObstruction :
      2 * errorRatio.im ≤ Data.Gaussian.Norm.Basic.normSq errorRatio)
    (denominatorRealObstruction :
      2 * denominatorRatio.re ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio)
    (denominatorDiagonalObstruction :
      denominatorRatio.re - denominatorRatio.im ≤
        Data.Gaussian.Norm.Basic.normSq denominatorRatio) :
    (3 / 4 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let xNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  let yNorm := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  let dot := errorRatio.re * denominatorRatio.re -
    errorRatio.im * denominatorRatio.im
  have xNormNonnegative : 0 ≤ xNorm := by
    dsimp only [xNorm]
    exact Gaussian.Norm.Basic.normSq_nonneg errorRatio
  have xNormLeOne : xNorm ≤ 1 := errorInside.le
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact Gaussian.Norm.Basic.normSq_nonneg denominatorRatio
  have yNormLeOne : yNorm ≤ 1 := denominatorInside.le
  have realComponentBound :
      errorRatio.re * yNorm ≤ xNorm * yNorm + 1 / 4 := by
    apply Dirichlet.Window.IndexOne.Bounds.component_mul_norm_le_product_add_quarter
        errorRatio.re errorRatio.im xNorm yNorm
    · rfl
    · exact yNormNonnegative
    · exact yNormLeOne
  have negativeImaginaryComponentBound :
      xNorm * (-denominatorRatio.im) ≤
        xNorm * yNorm + 1 / 4 := by
    have swapped := Dirichlet.Window.IndexOne.Bounds.component_mul_norm_le_product_add_quarter
      (-denominatorRatio.im) denominatorRatio.re yNorm xNorm
      (by
        dsimp only [yNorm, Data.Gaussian.Norm.Basic.normSq]
        ring1)
      xNormNonnegative xNormLeOne
    calc
      xNorm * (-denominatorRatio.im) =
          (-denominatorRatio.im) * xNorm := by ring1
      _ ≤ yNorm * xNorm + 1 / 4 := swapped
      _ = xNorm * yNorm + 1 / 4 := by ring1
  have gapExpansion :
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, Data.Gaussian.Norm.Basic.normSq]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im]
    ring1
  have signAlternative :=
    Dirichlet.Window.IndexOne.Bounds.real_nonpositive_or_imaginary_nonnegative_of_diagonalObstructions
      denominatorRatio denominatorInside denominatorDiagonalObstruction
  rw [gapExpansion]
  apply Dirichlet.Window.IndexOne.Bounds.three_quarters_le_of_twiceDot_le xNorm yNorm dot
  by_cases denominatorImaginaryNonnegative : 0 ≤ denominatorRatio.im
  · have imaginaryProductNonnegative :
        0 ≤ errorRatio.im * denominatorRatio.im :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        errorImaginaryNonnegative denominatorImaginaryNonnegative
    have dotLeRealProduct :
        dot ≤ errorRatio.re * denominatorRatio.re := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      dsimp only [dot]
      calc
        0 ≤ errorRatio.im * denominatorRatio.im :=
          imaginaryProductNonnegative
        _ = errorRatio.re * denominatorRatio.re -
            (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by ring1
    have twiceDotLeReal : 2 * dot ≤ errorRatio.re * yNorm := by
      have doubled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          dotLeRealProduct (show (0 : Fraction.Rational) ≤ 2 by decide)
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          denominatorRealObstruction errorRealNonnegative
      calc
        2 * dot ≤ 2 * (errorRatio.re * denominatorRatio.re) := doubled
        _ = errorRatio.re * (2 * denominatorRatio.re) := by ring1
        _ ≤ errorRatio.re * yNorm := scaled
    exact twiceDotLeReal.trans realComponentBound
  · have denominatorImaginaryNegative : denominatorRatio.im < 0 :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct
        denominatorImaginaryNonnegative
    have denominatorRealNonpositive : denominatorRatio.re ≤ 0 := by
      rcases signAlternative with realNonpositive | imaginaryNonnegative
      · exact realNonpositive
      · exact (denominatorImaginaryNonnegative imaginaryNonnegative).elim
    have negativeImaginaryNonnegative : 0 ≤ -denominatorRatio.im := by
      calc
        0 ≤ 0 - denominatorRatio.im :=
          (Fraction.Order.Arithmetic.sub_pos_direct
            denominatorImaginaryNegative).le
        _ = -denominatorRatio.im := by ring1
    have realProductNonpositive :
        errorRatio.re * denominatorRatio.re ≤ 0 := by
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          denominatorRealNonpositive errorRealNonnegative
      calc
        errorRatio.re * denominatorRatio.re ≤ errorRatio.re * 0 := scaled
        _ = 0 := by ring1
    have dotLeImaginaryProduct :
        dot ≤ errorRatio.im * (-denominatorRatio.im) := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      dsimp only [dot]
      calc
        0 ≤ -(errorRatio.re * denominatorRatio.re) :=
          by
            have shifted := Fraction.Order.Arithmetic.neg_le_neg_direct realProductNonpositive
            simpa only [neg_zero] using shifted
        _ = errorRatio.im * (-denominatorRatio.im) -
            (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by ring1
    have twiceDotLeNegativeImaginary :
        2 * dot ≤ xNorm * (-denominatorRatio.im) := by
      have doubled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          dotLeImaginaryProduct (show (0 : Fraction.Rational) ≤ 2 by decide)
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          errorImaginaryObstruction negativeImaginaryNonnegative
      calc
        2 * dot ≤ 2 * (errorRatio.im * (-denominatorRatio.im)) :=
          doubled
        _ = (2 * errorRatio.im) * (-denominatorRatio.im) := by ring1
        _ ≤ xNorm * (-denominatorRatio.im) := scaled
    exact twiceDotLeNegativeImaginary.trans
      negativeImaginaryComponentBound

/-- The signed fraction with numerator `13` and positive denominator `97`. -/
private def diagonalErrorBoundaryFraction :
    Data.Rat.SignedFraction :=
  { num := 13, den := 97, den_pos := by decide }

/-- The rational boundary `13/97` for the diagonal error chamber. -/
private def diagonalErrorBoundary : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryFraction

/-- Multiplying the diagonal error boundary by `97` recovers `13`. -/
private theorem diagonalErrorBoundary_mul_denominator :
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary * 97 = 13 := by
  have numeratorCast :
      (((13 : Nat) : Int) : Fraction.Rational) = (13 : Fraction.Rational) := by
    calc
      (((13 : Nat) : Int) : Fraction.Rational) = ((13 : Nat) : Fraction.Rational) :=
        Int.cast_natCast 13
      _ = (13 : Fraction.Rational) := Nat.cast_ofNat
  calc
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary * 97 =
        Data.Rat.SignedFraction.Normalization.ofFraction Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryFraction
          *
          ((Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryFraction.den : Int) : Fraction.Rational) := by
      unfold Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary
      dsimp only [Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryFraction]
      congr 1
    _ = ((Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryFraction.num : Int) : Fraction.Rational) :=
      Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryFraction
    _ = 13 := by
      dsimp only [Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryFraction]
      exact numeratorCast

/-- The signed fraction with numerator `97` and positive denominator `56`. -/
private def diagonalErrorLinearCoefficientFraction :
    Data.Rat.SignedFraction :=
  { num := 97, den := 56, den_pos := by decide }

/-- The rational linear coefficient `97/56` in the diagonal chamber bound. -/
private def diagonalErrorLinearCoefficient : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficientFraction

/-- Multiplying the diagonal linear coefficient by `56` recovers `97`. -/
private theorem diagonalErrorLinearCoefficient_mul_denominator :
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * 56 = 97 := by
  have numeratorCast :
      (((97 : Nat) : Int) : Fraction.Rational) = (97 : Fraction.Rational) := by
    calc
      (((97 : Nat) : Int) : Fraction.Rational) = ((97 : Nat) : Fraction.Rational) :=
        Int.cast_natCast 97
      _ = (97 : Fraction.Rational) := Nat.cast_ofNat
  calc
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * 56 =
        Data.Rat.SignedFraction.Normalization.ofFraction
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficientFraction *
            ((Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficientFraction.den : Int) :
              Fraction.Rational) := by
      unfold Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient
      dsimp only [Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficientFraction]
      congr 1
    _ = ((Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficientFraction.num : Int) : Fraction.Rational) :=
      Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficientFraction
    _ = 97 := by
      dsimp only [Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficientFraction]
      exact numeratorCast

/-- The diagonal error boundary `13/97` is at most `1/2`. -/
private theorem diagonalErrorBoundary_le_half :
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ≤ (1 / 2 : Fraction.Rational) := by decide

/-- At the diagonal boundary, `x² - 2x + 1/4` is strictly negative. -/
private theorem diagonalErrorBoundary_polynomial_negative :
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 - 2 *
      Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + 1 / 4 < 0 := by
  decide

/-- Twice the diagonal error boundary is at most the linear coefficient `97/56`. -/
private theorem twice_diagonalErrorBoundary_le_linearCoefficient :
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ≤
      Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient := by
  decide

/-- At the diagonal boundary, `x² - (97/56)x + 3/14` is positive. -/
private theorem diagonalErrorBoundary_quadratic_positive :
    0 < Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
      Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient *
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + 3 / 14 := by
  decide

/-- The signed fraction representing the norm-two index-one gap `71/112`. -/
private def normTwoIndexOneGapThresholdFraction :
    Data.Rat.SignedFraction :=
  { num := 71, den := 112, den_pos := by decide }

/-- The displayed index-one determinant-gap threshold `71/112` obtained by
adding the first norm-two leading coefficient test. -/
@[expose] def normTwoIndexOneGapThreshold : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    { num := 71, den := 112, den_pos := by decide }

/-- The signed fraction representing the reciprocal window bound `112/71`. -/
private def normTwoIndexOneWindowBoundFraction :
    Data.Rat.SignedFraction :=
  { num := 112, den := 71, den_pos := by decide }

/-- The corresponding determinant-index-one squared-window bound `112/71`. -/
@[expose] def normTwoIndexOneWindowBound : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    { num := 112, den := 71, den_pos := by decide }

/-- The strengthened root-free index-one gap `205/256`. -/
@[expose] def sharpIndexOneGapBound : Fraction.Rational :=
  Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound

/-- The corresponding strengthened squared-window bound `256/205`. -/
@[expose] def sharpIndexOneWindowBound : Fraction.Rational :=
  Dirichlet.Window.IndexOne.Chambers.firstRegionWindowBound

/-- The dyadic index-one gap `205/256` is strictly positive. -/
theorem sharpIndexOneGapBound_pos :
    (0 : Fraction.Rational) < Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound :=
  Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound_pos

/-- The dyadic window bound and gap multiply to one. -/
theorem sharpIndexOneWindowBound_mul_gapBound :
    Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound * Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound =
      1 :=
  Dirichlet.Window.IndexOne.Chambers.firstRegionWindowBound_mul_gapBound

/-- Multiplying the dyadic gap by `256` gives `205`. -/
theorem sharpIndexOneGapBound_mul_denominator :
    Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound * (2 : Fraction.Rational) ^ 8 = 13 * 16 - 3 := by
  simpa only [Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound] using
    Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound_mul_denominator

/-- Multiplying the dyadic window bound by `205` gives `256`. -/
theorem sharpIndexOneWindowBound_mul_denominator :
    Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound * (13 * 16 - 3 : Fraction.Rational) =
      (2 : Fraction.Rational) ^ 8 := by
  simpa only [Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound] using
    Dirichlet.Window.IndexOne.Chambers.firstRegionWindowBound_mul_denominator

/-- The index-one and centered index-two dyadic window bounds are both `256/205`. -/
theorem sharpIndexOneWindowBound_eq_dyadicCenteredWindowBound :
    Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound =
      IndexTwo.Bounds.dyadicCenteredWindowBound := by
  unfold Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound
    Dirichlet.Window.IndexOne.Chambers.firstRegionWindowBound
    IndexTwo.Bounds.dyadicCenteredWindowBound
  apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
  change
    ((2 ^ 8 : Nat) : Int) * ((13 * 16 - 3 : Nat) : Int) =
      ((2 ^ 8 : Nat) : Int) * ((13 * 16 - 3 : Nat) : Int)
  rfl

/-- Multiplying the norm-two index-one gap by `112` gives `71`. -/
theorem normTwoIndexOneGapThreshold_mul_denominator :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold * 112 = 71 := by
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 71, den := 112, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Multiplying the norm-two index-one window bound by `71` gives `112`. -/
theorem normTwoIndexOneWindowBound_mul_denominator :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound * 71 = 112 := by
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 112, den := 71, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- The norm-two index-one gap `71/112` is strictly positive. -/
theorem normTwoIndexOneGapThreshold_pos :
    (0 : Fraction.Rational) < Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold := by
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold
  change
    Data.Rat.SignedFraction.Order.LessEqFraction
        Data.Rat.SignedFraction.Arithmetic.zeroFraction ⟨71, 112, by decide⟩ ∧
      ¬Data.Rat.SignedFraction.Order.LessEqFraction
        ⟨71, 112, by decide⟩ Data.Rat.SignedFraction.Arithmetic.zeroFraction
  decide

/-- The norm-two index-one window bound and gap multiply to one. -/
theorem normTwoIndexOneWindowBound_mul_gapThreshold :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound *
      Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold = 1 := by
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold
  rw [Data.Rat.SignedFraction.Arithmetic.ofFraction_mulFraction]
  calc
    _ = Data.Rat.SignedFraction.Normalization.ofFraction ⟨1, 1, by decide⟩ := by
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change (112 * 71 : Int) * 1 = 1 * (71 * 112)
      ring1
    _ = 1 := (Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 1).symm

/-- The norm-two index-one and centered index-two window bounds are both `112/71`. -/
theorem normTwoIndexOneWindowBound_eq_centeredIndexTwoWindowBound :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound = IndexTwo.Bounds.centeredWindowBound
      := by
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound
  unfold IndexTwo.Bounds.centeredWindowBound
  apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
  change (112 * 71 : Int) = 112 * 71
  rfl

/-- The norm-two index-one gap is at most one. -/
private theorem normTwoIndexOneGapThreshold_le_one :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤ 1 := by
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold
  rw [show (1 : Fraction.Rational) =
      Data.Rat.SignedFraction.Normalization.ofFraction
        Data.Rat.SignedFraction.Arithmetic.oneFraction from
    Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 1]
  exact (Data.Rat.SignedFraction.Order.ofFraction_le_iff _ _).2 (by decide)

/-- The norm-two index-one gap `71/112` is at most `3/4`. -/
private theorem normTwoIndexOneGapThreshold_le_threeQuarters :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤ (3 / 4 : Fraction.Rational) := by
  let threeQuarters : Data.Rat.SignedFraction :=
    ⟨3, 4, by decide⟩
  have threeQuartersDisplay :
      Data.Rat.SignedFraction.Normalization.ofFraction threeQuarters =
        (3 / 4 : Fraction.Rational) := by
    simpa only [threeQuarters, Int.cast_ofNat] using
      Data.Rat.SignedFraction.Arithmetic.ofFraction_eq_div threeQuarters
  rw [← threeQuartersDisplay]
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold
  exact (Data.Rat.SignedFraction.Order.ofFraction_le_iff _ _).2 (by decide)

/-- The norm-two index-one window bound `112/71` is at most two. -/
theorem normTwoIndexOneWindowBound_le_two :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound ≤ 2 := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 71)
  · rw [Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_mul_denominator]
    simpa only [NatCast.mul, Nat.cast_ofNat] using
      Fraction.Cast.Order.natCast_le_direct
        (show 112 ≤ 2 * 71 by decide)
  · exact Fraction.Cast.Order.natCast_pos_direct (by decide)

/-- The window bound `112/71` is at most `28/15`. -/
theorem normTwoIndexOneWindowBound_le_twentyEight_fifteenths :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound ≤ (28 / 15 : Fraction.Rational) := by
  apply (Fraction.Order.Field.le_div_iff_pos
    (Fraction.Cast.Order.natCast_pos_direct
      (show 0 < 15 by decide))).2
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 71)
  · calc
      (Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound * 15) * 71 =
          (Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound * 71) * 15 := by ring1
      _ = 112 * 15 := by rw [Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_mul_denominator]
      _ ≤ 28 * 71 := by
        simpa only [NatCast.mul, Nat.cast_ofNat] using
          Fraction.Cast.Order.natCast_le_direct
            (show 112 * 15 ≤ 28 * 71 by decide)
  · exact Fraction.Cast.Order.natCast_pos_direct (by decide)

/-- The signed fraction `23859/37636` representing the quadratic boundary value. -/
private def diagonalErrorBoundaryScalarFraction :
    Data.Rat.SignedFraction :=
  { num := 23859, den := 37636, den_pos := by decide }

/-- The signed fraction `84/97` representing one minus the diagonal boundary. -/
private def diagonalErrorBoundaryComplementFraction :
    Data.Rat.SignedFraction :=
  { num := 84, den := 97, den_pos := by decide }

/-- Evaluate `3/4 + b² - b` at the diagonal boundary `b = 13/97`. -/
private theorem diagonalErrorBoundaryScalar_representation :
    3 / 4 + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
      Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary =
      Data.Rat.SignedFraction.Normalization.ofFraction
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryScalarFraction := by
  unfold Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryFraction
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryScalarFraction
  decide

/-- Represent one minus the diagonal boundary by the signed fraction `84/97`. -/
private theorem diagonalErrorBoundaryComplement_representation :
    1 - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary =
      Data.Rat.SignedFraction.Normalization.ofFraction
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryComplementFraction := by
  unfold Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryFraction
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryComplementFraction
  decide

/-- The quadratic boundary value is at least the norm-two gap `71/112`. -/
private theorem seventyOne_oneHundredTwelfths_le_boundaryScalar :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤
      3 / 4 + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary := by
  rw [Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryScalar_representation]
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold
  exact (Data.Rat.SignedFraction.Order.ofFraction_le_iff _ _).2 (by decide)

/-- One minus the diagonal boundary is at least the norm-two gap `71/112`. -/
private theorem seventyOne_oneHundredTwelfths_le_one_sub_boundary :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤ 1 -
      Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary := by
  rw [Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundaryComplement_representation]
  unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold
  exact (Data.Rat.SignedFraction.Order.ofFraction_le_iff _ _).2 (by decide)

/-- The two error-side circle exclusions in the critical first-octant chamber
force the imaginary coordinate below the displayed rational `13/97`.  This is
the square-root-free replacement for locating the smaller root of
`b² - 2b + 1/4`. -/
private theorem imaginary_le_diagonalErrorBoundary_of_diagonalErrorChamber
    (errorRatio : Gaussian.Basic.Canonical)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (errorImaginaryObstruction :
      2 * errorRatio.im ≤ Data.Gaussian.Norm.Basic.normSq errorRatio)
    (errorDiagonalObstruction :
      2 * (errorRatio.re + errorRatio.im) ≤ Data.Gaussian.Norm.Basic.normSq errorRatio + 1) :
    errorRatio.im ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary := by
  let a := errorRatio.re
  let b := errorRatio.im
  let xNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  have aNonnegative : 0 ≤ a := errorRealNonnegative
  have bNonnegative : 0 ≤ b := errorImaginaryNonnegative
  have xNormIdentity : xNorm = a ^ 2 + b ^ 2 := rfl
  have xNormLeOne : xNorm ≤ 1 := errorInside.le
  have aSquareLeNorm : a ^ 2 ≤ xNorm := by
    rw [xNormIdentity]
    exact le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct b)
  have aSquareLeOne : a ^ 2 ≤ (1 : Fraction.Rational) ^ 2 := by
    simpa only [one_pow] using aSquareLeNorm.trans xNormLeOne
  have aLeOne : a ≤ 1 :=
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct (by decide) aSquareLeOne
  have twiceBLeOne : 2 * b ≤ 1 :=
    (show 2 * b ≤ xNorm from errorImaginaryObstruction).trans xNormLeOne
  have bLeHalf : b ≤ (1 / 2 : Fraction.Rational) := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        b * 2 = 2 * b := by ring1
        _ ≤ 1 := twiceBLeOne
        _ = (1 / 2 : Fraction.Rational) * 2 := by decide
    · decide
  have twiceBMinusSquareLeASquare : 2 * b - b ^ 2 ≤ a ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ xNorm - 2 * b :=
        Fraction.Order.Arithmetic.sub_nonneg_direct errorImaginaryObstruction
      _ = a ^ 2 - (2 * b - b ^ 2) := by
        rw [xNormIdentity]
        ring1
  have twiceBMinusSquareLeComplementSquare :
      2 * b - b ^ 2 ≤ (1 - a) ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (xNorm + 1) - 2 * (a + b) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct errorDiagonalObstruction
      _ = (1 - a) ^ 2 - (2 * b - b ^ 2) := by
        rw [xNormIdentity]
        ring1
  have twiceBMinusSquareLeQuarter :
      2 * b - b ^ 2 ≤ (1 / 4 : Fraction.Rational) := by
    by_cases aLeHalf : a ≤ (1 / 2 : Fraction.Rational)
    · have aSquareLeQuarter : a ^ 2 ≤ (1 / 2 : Fraction.Rational) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct aNonnegative aLeHalf 2
      calc
        2 * b - b ^ 2 ≤ a ^ 2 := twiceBMinusSquareLeASquare
        _ ≤ (1 / 2 : Fraction.Rational) ^ 2 := aSquareLeQuarter
        _ = 1 / 4 := by decide
    · have halfLeA : (1 / 2 : Fraction.Rational) ≤ a := le_of_not_ge aLeHalf
      have complementNonnegative : 0 ≤ 1 - a :=
        Fraction.Order.Arithmetic.sub_nonneg_direct aLeOne
      have complementLeHalf : 1 - a ≤ (1 / 2 : Fraction.Rational) := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ a - 1 / 2 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct halfLeA
          _ = (1 / 2 : Fraction.Rational) - (1 - a) := by
            calc
              a - 1 / 2 = a + -(1 / 2) := by ring1
              _ = a + ((1 / 2 : Fraction.Rational) - 1) := by
                rw [show -(1 / 2 : Fraction.Rational) = 1 / 2 - 1 by decide]
              _ = (1 / 2 : Fraction.Rational) - (1 - a) := by ring1
      have complementSquareLeQuarter :
          (1 - a) ^ 2 ≤ (1 / 2 : Fraction.Rational) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct complementNonnegative
          complementLeHalf 2
      calc
        2 * b - b ^ 2 ≤ (1 - a) ^ 2 :=
          twiceBMinusSquareLeComplementSquare
        _ ≤ (1 / 2 : Fraction.Rational) ^ 2 := complementSquareLeQuarter
        _ = 1 / 4 := by decide
  have boundaryPolynomialNonnegative :
      0 ≤ b ^ 2 - 2 * b + 1 / 4 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 / 4 : Fraction.Rational) - (2 * b - b ^ 2) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct
          twiceBMinusSquareLeQuarter
      _ = (b ^ 2 - 2 * b + 1 / 4) - 0 := by ring1
  by_cases bLe : b ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary
  · exact bLe
  · have boundaryLtB : Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary < b := lt_of_not_ge bLe
    have positiveFactor : 0 < b - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary :=
      Fraction.Order.Arithmetic.sub_pos_direct boundaryLtB
    have sumLeOne : b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ≤ 1 := by
      have added := Fraction.Order.Arithmetic.add_le_add_direct bLeHalf
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary_le_half
      exact added.trans_eq (show
        (1 / 2 : Fraction.Rational) + 1 / 2 = 1 by decide)
    have secondFactorNegative : b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - 2 < 0 :=
      Fraction.Order.Arithmetic.sub_neg_direct
        (sumLeOne.trans_lt (show (1 : Fraction.Rational) < 2 by decide))
    have productNegative :
        (b - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) *
          (b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - 2) < 0 :=
      Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
        positiveFactor secondFactorNegative
    have polynomialNegative : b ^ 2 - 2 * b + 1 / 4 < 0 := by
      calc
        b ^ 2 - 2 * b + 1 / 4 =
            (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
              2 * Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + 1 / 4) +
              (b - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) *
                (b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - 2) := by ring1
        _ < 0 + 0 := Fraction.Order.Arithmetic.add_lt_add_direct
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary_polynomial_negative productNegative
        _ = 0 := by ring1
    exact (not_lt_of_ge boundaryPolynomialNonnegative polynomialNegative).elim

/-- The diagonal error chamber gives a determinant gap of at least `15/28`.

The first-octant error and both strict unit-disk bounds combine with the imaginary, diagonal and denominator-real
obstructions. A rational boundary split and explicit nonnegative polynomial certificate establish the estimate. -/
private theorem fifteen_twenty_eighths_le_of_diagonalErrorChamber
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorImaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (errorImaginaryObstruction :
      2 * errorRatio.im ≤ Data.Gaussian.Norm.Basic.normSq errorRatio)
    (errorDiagonalObstruction :
      2 * (errorRatio.re + errorRatio.im) ≤ Data.Gaussian.Norm.Basic.normSq errorRatio + 1)
    (denominatorRealObstruction :
      2 * denominatorRatio.re ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio) :
    (15 / 28 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let c := denominatorRatio.re
  let d := denominatorRatio.im
  let xNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  let yNorm := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  let dot := a * c - b * d
  have aNonnegative : 0 ≤ a := errorRealNonnegative
  have bNonnegative : 0 ≤ b := errorImaginaryNonnegative
  have xNormIdentity : xNorm = a ^ 2 + b ^ 2 := rfl
  have yNormIdentity : yNorm = c ^ 2 + d ^ 2 := rfl
  have xNormNonnegative : 0 ≤ xNorm := by
    dsimp only [xNorm]
    exact Gaussian.Norm.Basic.normSq_nonneg errorRatio
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact Gaussian.Norm.Basic.normSq_nonneg denominatorRatio
  have xNormLeOne : xNorm ≤ 1 := errorInside.le
  have yNormLeOne : yNorm ≤ 1 := denominatorInside.le
  have oneMinusYNonnegative : 0 ≤ 1 - yNorm :=
    Fraction.Order.Arithmetic.sub_nonneg_direct yNormLeOne
  have yMinusTwiceCNonnegative : 0 ≤ yNorm - 2 * c :=
    Fraction.Order.Arithmetic.sub_nonneg_direct denominatorRealObstruction
  have aSquareLeNorm : a ^ 2 ≤ xNorm := by
    rw [xNormIdentity]
    exact le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct b)
  have aSquareLeOne : a ^ 2 ≤ (1 : Fraction.Rational) ^ 2 := by
    simpa only [one_pow] using aSquareLeNorm.trans xNormLeOne
  have aLeOne : a ≤ 1 :=
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct (by decide) aSquareLeOne
  have twiceBLeOne : 2 * b ≤ 1 :=
    (show 2 * b ≤ xNorm from errorImaginaryObstruction).trans xNormLeOne
  have bLeHalf : b ≤ (1 / 2 : Fraction.Rational) := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        b * 2 = 2 * b := by ring1
        _ ≤ 1 := twiceBLeOne
        _ = (1 / 2 : Fraction.Rational) * 2 := by decide
    · decide
  have twiceBMinusSquareLeASquare : 2 * b - b ^ 2 ≤ a ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ xNorm - 2 * b :=
        Fraction.Order.Arithmetic.sub_nonneg_direct errorImaginaryObstruction
      _ = a ^ 2 - (2 * b - b ^ 2) := by
        rw [xNormIdentity]
        ring1
  have twiceBMinusSquareLeComplementSquare :
      2 * b - b ^ 2 ≤ (1 - a) ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (xNorm + 1) - 2 * (a + b) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct errorDiagonalObstruction
      _ = (1 - a) ^ 2 - (2 * b - b ^ 2) := by
        rw [xNormIdentity]
        ring1
  have twiceBMinusSquareLeQuarter :
      2 * b - b ^ 2 ≤ (1 / 4 : Fraction.Rational) := by
    by_cases aLeHalf : a ≤ (1 / 2 : Fraction.Rational)
    · have aSquareLeQuarter : a ^ 2 ≤ (1 / 2 : Fraction.Rational) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct aNonnegative aLeHalf 2
      calc
        2 * b - b ^ 2 ≤ a ^ 2 := twiceBMinusSquareLeASquare
        _ ≤ (1 / 2 : Fraction.Rational) ^ 2 := aSquareLeQuarter
        _ = 1 / 4 := by decide
    · have halfLeA : (1 / 2 : Fraction.Rational) ≤ a := le_of_not_ge aLeHalf
      have complementNonnegative : 0 ≤ 1 - a :=
        Fraction.Order.Arithmetic.sub_nonneg_direct aLeOne
      have complementLeHalf : 1 - a ≤ (1 / 2 : Fraction.Rational) := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ a - 1 / 2 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct halfLeA
          _ = (1 / 2 : Fraction.Rational) - (1 - a) := by
            calc
              a - 1 / 2 = a + -(1 / 2) := by ring1
              _ = a + ((1 / 2 : Fraction.Rational) - 1) := by
                rw [show -(1 / 2 : Fraction.Rational) = 1 / 2 - 1 by decide]
              _ = (1 / 2 : Fraction.Rational) - (1 - a) := by ring1
      have complementSquareLeQuarter :
          (1 - a) ^ 2 ≤ (1 / 2 : Fraction.Rational) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct complementNonnegative
          complementLeHalf 2
      calc
        2 * b - b ^ 2 ≤ (1 - a) ^ 2 :=
          twiceBMinusSquareLeComplementSquare
        _ ≤ (1 / 2 : Fraction.Rational) ^ 2 := complementSquareLeQuarter
        _ = 1 / 4 := by decide
  have boundaryPolynomialNonnegative :
      0 ≤ b ^ 2 - 2 * b + 1 / 4 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 / 4 : Fraction.Rational) - (2 * b - b ^ 2) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct
          twiceBMinusSquareLeQuarter
      _ = (b ^ 2 - 2 * b + 1 / 4) - 0 := by ring1
  have bLeRationalBoundary : b ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary := by
    by_cases bLe : b ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary
    · exact bLe
    · have boundaryLtB : Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary < b := lt_of_not_ge bLe
      have positiveFactor : 0 < b - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary :=
        Fraction.Order.Arithmetic.sub_pos_direct boundaryLtB
      have sumLeOne : b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ≤ 1 := by
        have added := Fraction.Order.Arithmetic.add_le_add_direct bLeHalf
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary_le_half
        exact added.trans_eq (show
          (1 / 2 : Fraction.Rational) + 1 / 2 = 1 by decide)
      have secondFactorNegative : b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - 2 < 0 :=
        Fraction.Order.Arithmetic.sub_neg_direct
          (sumLeOne.trans_lt (show (1 : Fraction.Rational) < 2 by decide))
      have productNegative :
          (b - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) *
            (b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - 2) < 0 :=
        Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
          positiveFactor secondFactorNegative
      have boundaryValueNegative :
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
            2 * Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + 1 / 4 < 0 :=
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary_polynomial_negative
      have polynomialNegative : b ^ 2 - 2 * b + 1 / 4 < 0 := by
        calc
          b ^ 2 - 2 * b + 1 / 4 =
              (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
                2 * Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + 1 / 4) +
                (b - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) *
                  (b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - 2) := by ring1
          _ < 0 + 0 := Fraction.Order.Arithmetic.add_lt_add_direct
            boundaryValueNegative productNegative
          _ = 0 := by ring1
      exact (not_lt_of_ge boundaryPolynomialNonnegative polynomialNegative).elim
  have decreasingFactorNonnegative :
      0 ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient - b -
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary := by
    have sumLe : b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ≤
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient := by
      calc
      b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ≤
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary +
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          bLeRationalBoundary Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary
      _ ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient :=
        Dirichlet.Window.IndexOne.Bounds.twice_diagonalErrorBoundary_le_linearCoefficient
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient -
          (b + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct sumLe
      _ = (Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient - b -
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) - 0 := by ring1
  have boundaryDifferenceNonnegative : 0 ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b :=
    Fraction.Order.Arithmetic.sub_nonneg_direct bLeRationalBoundary
  have boundaryProductNonnegative :
      0 ≤ (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b) *
        (Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient - b -
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      boundaryDifferenceNonnegative decreasingFactorNonnegative
  have boundaryQuadraticPositive :
      0 < Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient *
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + 3 / 14 :=
    Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary_quadratic_positive
  have bQuadraticNonnegative :
      0 ≤ b ^ 2 - Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b + 3 / 14 := by
    calc
      0 ≤ (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b) *
          (Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient - b -
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) +
            (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
              Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient *
                Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary +
                3 / 14) :=
        add_nonneg boundaryProductNonnegative boundaryQuadraticPositive.le
      _ = b ^ 2 - Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b + 3 / 14 := by ring1
  have shiftedSquareIdentity :
      (a - 1 / 2) ^ 2 = a ^ 2 - a + 1 / 4 := by
    calc
      (a - 1 / 2) ^ 2 =
          a ^ 2 - a * (1 / 2 + 1 / 2) + (1 / 2) ^ 2 := by ring1
      _ = a ^ 2 - a * 1 + (1 / 2) ^ 2 := by
        rw [show (1 / 2 : Fraction.Rational) + 1 / 2 = 1 by decide]
      _ = a ^ 2 - a + 1 / 4 := by
        rw [show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide]
        ring1
  have scalarLowerBound :
      (15 / 28 : Fraction.Rational) ≤
        1 + xNorm - a - Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b := by
    have constantIdentity :
        (1 / 4 : Fraction.Rational) + 3 / 14 = 1 - 15 / 28 := by decide
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (a - 1 / 2) ^ 2 +
          (b ^ 2 - Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b + 3 / 14) :=
        add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _)
          bQuadraticNonnegative
      _ = a ^ 2 + b ^ 2 - a -
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b + (1 / 4 + 3 / 14) := by
        rw [shiftedSquareIdentity]
        ring1
      _ = a ^ 2 + b ^ 2 - a -
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b + (1 - 15 / 28) := by
        rw [constantIdentity]
      _ = (1 + xNorm - a - Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b) -
          15 / 28 := by
        rw [xNormIdentity]
        ring1
  have aSquareLeA : a ^ 2 ≤ a := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        aLeOne aNonnegative
    calc
      a ^ 2 = a * a := by ring1
      _ ≤ a * 1 := scaled
      _ = a := by ring1
  have sevenBLeFour : 7 * b ≤ 4 := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        bLeHalf (show (0 : Fraction.Rational) ≤ 7 by decide)
    calc
      7 * b ≤ 7 * (1 / 2) := scaled
      _ ≤ 4 := by decide
  have sevenBSquareLeFourB : 7 * b ^ 2 ≤ 4 * b := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        sevenBLeFour bNonnegative
    calc
      7 * b ^ 2 = b * (7 * b) := by ring1
      _ ≤ b * 4 := scaled
      _ = 4 * b := by ring1
  have sevenASquareLeSevenA : 7 * a ^ 2 ≤ 7 * a :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      aSquareLeA (show (0 : Fraction.Rational) ≤ 7 by decide)
  have sevenNormLeLinear : 7 * xNorm ≤ 7 * a + 4 * b := by
    have added := Fraction.Order.Arithmetic.add_le_add_direct
      sevenASquareLeSevenA sevenBSquareLeFourB
    calc
      7 * xNorm = 7 * a ^ 2 + 7 * b ^ 2 := by
        rw [xNormIdentity]
        ring1
      _ ≤ 7 * a + 4 * b := added
  have sevenAMinusFourBNonnegative : 0 ≤ 7 * a - 4 * b := by
    apply Fraction.Order.Arithmetic.sub_nonneg_direct
    have fourBLeFourA :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (show b ≤ a from errorImaginaryLeReal)
        (show (0 : Fraction.Rational) ≤ 4 by decide)
    exact fourBLeFourA.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (4 : Fraction.Rational) ≤ 7 by decide) aNonnegative)
  have sevenAPlusFourBNonnegative : 0 ≤ 7 * a + 4 * b :=
    add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) aNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bNonnegative)
  let certificate :=
    8 * (7 * a + 4 * b) * (1 - yNorm) +
      8 * (7 * a - 4 * b) * (yNorm - 2 * c) +
      16 * b * (2 * c - 1) ^ 2 +
      b * (8 * d + 7) ^ 2
  have firstTermNonnegative :
      0 ≤ 8 * (7 * a + 4 * b) * (1 - yNorm) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        sevenAPlusFourBNonnegative)
      oneMinusYNonnegative
  have secondTermNonnegative :
      0 ≤ 8 * (7 * a - 4 * b) * (yNorm - 2 * c) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        sevenAMinusFourBNonnegative)
      yMinusTwiceCNonnegative
  have thirdTermNonnegative :
      0 ≤ 16 * b * (2 * c - 1) ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bNonnegative)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have fourthTermNonnegative : 0 ≤ b * (8 * d + 7) ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct bNonnegative
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have remainingTermsNonnegative :
      0 ≤ 8 * (7 * a - 4 * b) * (yNorm - 2 * c) +
        16 * b * (2 * c - 1) ^ 2 +
        b * (8 * d + 7) ^ 2 :=
    add_nonneg (add_nonneg secondTermNonnegative thirdTermNonnegative)
      fourthTermNonnegative
  have certificateIdentity :
      certificate = 56 * a + 97 * b - 112 * dot := by
    dsimp only [certificate]
    rw [yNormIdentity]
    dsimp only [dot]
    ring1
  have scaledFirstTerm :
      8 * (7 * xNorm) * (1 - yNorm) ≤
        8 * (7 * a + 4 * b) * (1 - yNorm) := by
    have complementScaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        sevenNormLeLinear oneMinusYNonnegative
    have eightScaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        complementScaled (show (0 : Fraction.Rational) ≤ 8 by decide)
    calc
      8 * (7 * xNorm) * (1 - yNorm) =
          8 * ((7 * xNorm) * (1 - yNorm)) := by ring1
      _ ≤ 8 * ((7 * a + 4 * b) * (1 - yNorm)) := eightScaled
      _ = 8 * (7 * a + 4 * b) * (1 - yNorm) := by ring1
  have scaledNormComplementLeCertificate :
      56 * xNorm * (1 - yNorm) ≤ certificate := by
    calc
      56 * xNorm * (1 - yNorm) =
          8 * (7 * xNorm) * (1 - yNorm) := by ring1
      _ ≤ 8 * (7 * a + 4 * b) * (1 - yNorm) := scaledFirstTerm
      _ ≤ 8 * (7 * a + 4 * b) * (1 - yNorm) +
          (8 * (7 * a - 4 * b) * (yNorm - 2 * c) +
            16 * b * (2 * c - 1) ^ 2 +
            b * (8 * d + 7) ^ 2) :=
        le_add_of_nonneg_right remainingTermsNonnegative
      _ = certificate := by
        dsimp only [certificate]
        ring1
  have scaledNormComplementBound :
      56 * xNorm * (1 - yNorm) ≤
        56 * a + 97 * b - 112 * dot := by
    rw [← certificateIdentity]
    exact scaledNormComplementLeCertificate
  have normComplementBound :
      xNorm * (1 - yNorm) ≤
        a + Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b - 2 * dot := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 56)
    · calc
        (xNorm * (1 - yNorm)) * 56 =
            56 * xNorm * (1 - yNorm) := by ring1
        _ ≤ 56 * a + 97 * b - 112 * dot :=
          scaledNormComplementBound
        _ = (a + Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b - 2 * dot) * 56 := by
          rw [← Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient_mul_denominator]
          ring1
    · calc
        (0 : Fraction.Rational) < 7 * 8 :=
          Fraction.Order.Arithmetic.mul_pos_direct (by decide) (by decide)
        _ = 56 := by ring1
  have algebraicGapLower :
      1 + xNorm - a - Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b ≤
        1 + xNorm * yNorm - 2 * dot := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      normComplementBound
      (1 + xNorm * yNorm -
        (a + Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b))
    calc
      1 + xNorm - a - Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b =
          xNorm * (1 - yNorm) +
            (1 + xNorm * yNorm -
              (a + Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b)) := by
        ring1
      _ ≤ (a + Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b - 2 * dot) +
          (1 + xNorm * yNorm -
            (a + Dirichlet.Window.IndexOne.Bounds.diagonalErrorLinearCoefficient * b)) := shifted
      _ = 1 + xNorm * yNorm - 2 * dot := by ring1
  have gapExpansion :
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, a, b, c, d, Data.Gaussian.Norm.Basic.normSq]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im]
    ring1
  rw [gapExpansion]
  exact scalarLowerBound.trans algebraicGapLower

/-- Adding the norm-two leading combination supplies the missing second
denominator projection in the critical chamber.  Together with the existing
`13/97` error-coordinate boundary it raises the normalized gap to
`71/112`, without naming the quadratic boundary's irrational root. -/
private theorem seventyOne_oneHundredTwelfths_le_of_diagonalErrorChamber
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorImaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (errorImaginaryObstruction :
      2 * errorRatio.im ≤ Data.Gaussian.Norm.Basic.normSq errorRatio)
    (errorDiagonalObstruction :
      2 * (errorRatio.re + errorRatio.im) ≤ Data.Gaussian.Norm.Basic.normSq errorRatio + 1)
    (denominatorRealObstruction :
      2 * denominatorRatio.re ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio)
    (denominatorDiagonalObstruction :
      2 * (denominatorRatio.re - denominatorRatio.im) ≤
        Data.Gaussian.Norm.Basic.normSq denominatorRatio + 1) :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let c := denominatorRatio.re
  let d := denominatorRatio.im
  let xNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  let yNorm := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  let dot := a * c - b * d
  have aNonnegative : 0 ≤ a := errorRealNonnegative
  have bNonnegative : 0 ≤ b := errorImaginaryNonnegative
  have bLeA : b ≤ a := errorImaginaryLeReal
  have xNormIdentity : xNorm = a ^ 2 + b ^ 2 := rfl
  have yNormIdentity : yNorm = c ^ 2 + d ^ 2 := rfl
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact Gaussian.Norm.Basic.normSq_nonneg denominatorRatio
  have yNormLeOne : yNorm ≤ 1 := denominatorInside.le
  have bLeBoundary : b ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary :=
    Dirichlet.Window.IndexOne.Bounds.imaginary_le_diagonalErrorBoundary_of_diagonalErrorChamber errorRatio
      errorRealNonnegative errorImaginaryNonnegative errorInside
      errorImaginaryObstruction errorDiagonalObstruction
  have boundaryPlusBLeOne : Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + b ≤ 1 := by
    calc
      Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + b ≤
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary +
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary :=
        calc
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + b = b +
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary := by ring1
          _ ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary +
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary :=
            Fraction.Order.Arithmetic.add_le_add_right_direct bLeBoundary
              Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary
      _ ≤ (1 / 2 : Fraction.Rational) + 1 / 2 :=
        Fraction.Order.Arithmetic.add_le_add_direct
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary_le_half
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary_le_half
      _ = 1 := by decide
  have firstBoundaryFactorNonnegative :
      0 ≤ Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b :=
    Fraction.Order.Arithmetic.sub_nonneg_direct bLeBoundary
  have secondBoundaryFactorNonnegative :
      0 ≤ 1 - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 1 - (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + b) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct boundaryPlusBLeOne
      _ = (1 - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b) - 0 := by ring1
  have boundaryProductNonnegative :
      0 ≤ (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b) *
        (1 - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      firstBoundaryFactorNonnegative secondBoundaryFactorNonnegative
  have boundaryQuadraticLe :
      Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
        Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ≤ b ^ 2 - b := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b) *
          (1 - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary - b) := boundaryProductNonnegative
      _ = (b ^ 2 - b) -
          (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) := by ring1
  have displayedBoundaryLower :
      Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤
        3 / 4 + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
          Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary :=
    Dirichlet.Window.IndexOne.Bounds.seventyOne_oneHundredTwelfths_le_boundaryScalar
  have scalarLowerBound :
      Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤ 1 + xNorm - a - b := by
    have shiftedSquareNonnegative : 0 ≤ (a - 1 / 2) ^ 2 :=
      Fraction.Order.Arithmetic.sq_nonneg_direct _
    have shiftedBoundary :=
      Fraction.Order.Arithmetic.add_le_add_right_direct boundaryQuadraticLe
        (3 / 4 : Fraction.Rational)
    calc
      Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤
          3 / 4 + Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary :=
        displayedBoundaryLower
      _ = 3 / 4 +
          (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) := by ring1
      _ ≤ 3 / 4 + (b ^ 2 - b) := by
        calc
          3 / 4 +
              (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
                Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) =
            (Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary ^ 2 -
              Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary) + 3 / 4 := by
              ring1
          _ ≤ (b ^ 2 - b) + 3 / 4 := shiftedBoundary
          _ = 3 / 4 + (b ^ 2 - b) := by ring1
      _ ≤ (a - 1 / 2) ^ 2 + (3 / 4 + (b ^ 2 - b)) :=
        le_add_of_nonneg_left shiftedSquareNonnegative
      _ = 1 + xNorm - a - b := by
        rw [xNormIdentity]
        calc
          (a - 1 / 2) ^ 2 + (3 / 4 + (b ^ 2 - b)) =
              (a ^ 2 - a + 1 / 4) + (3 / 4 + (b ^ 2 - b)) := by
            congr 1
            calc
              (a - 1 / 2) ^ 2 =
                  a ^ 2 - 2 * a * (1 / 2) + (1 / 2) ^ 2 := by
                ring1
              _ = a ^ 2 - a * (2 * (1 / 2)) + (1 / 2) ^ 2 := by
                ring1
              _ = a ^ 2 - a + 1 / 4 := by
                rw [show (2 : Fraction.Rational) * (1 / 2) = 1 by decide,
                  show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide]
                ring1
          _ = a ^ 2 + b ^ 2 - a - b + (1 / 4 + 3 / 4) := by
            ring1
          _ = 1 + (a ^ 2 + b ^ 2) - a - b := by
            rw [show (1 / 4 : Fraction.Rational) + 3 / 4 = 1 by decide]
            ring1
  have aMinusBNonnegative : 0 ≤ a - b :=
    Fraction.Order.Arithmetic.sub_nonneg_direct bLeA
  have realProjectionScaled :
      2 * (a - b) * c ≤ (a - b) * yNorm := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        denominatorRealObstruction aMinusBNonnegative
    calc
      2 * (a - b) * c = (a - b) * (2 * c) := by ring1
      _ ≤ (a - b) * yNorm := scaled
  have diagonalProjectionScaled :
      2 * b * (c - d) ≤ b * (yNorm + 1) := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        denominatorDiagonalObstruction bNonnegative
    calc
      2 * b * (c - d) = b * (2 * (c - d)) := by ring1
      _ ≤ b * (yNorm + 1) := scaled
  have twiceDotLe : 2 * dot ≤ a * yNorm + b := by
    have added := Fraction.Order.Arithmetic.add_le_add_direct
      realProjectionScaled diagonalProjectionScaled
    calc
      2 * dot = 2 * (a - b) * c + 2 * b * (c - d) := by
        dsimp only [dot]
        ring1
      _ ≤ (a - b) * yNorm + b * (yNorm + 1) := added
      _ = a * yNorm + b := by ring1
  have projectedGapLower :
      1 + xNorm * yNorm - a * yNorm - b ≤
        1 + xNorm * yNorm - 2 * dot := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (a * yNorm + b) - 2 * dot :=
        Fraction.Order.Arithmetic.sub_nonneg_direct twiceDotLe
      _ = (1 + xNorm * yNorm - 2 * dot) -
          (1 + xNorm * yNorm - a * yNorm - b) := by ring1
  have targetLeProjected :
      Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤
        1 + xNorm * yNorm - a * yNorm - b := by
    by_cases xNormLeA : xNorm ≤ a
    · have aMinusXNonnegative : 0 ≤ a - xNorm :=
        Fraction.Order.Arithmetic.sub_nonneg_direct xNormLeA
      have oneMinusYNonnegative : 0 ≤ 1 - yNorm :=
        Fraction.Order.Arithmetic.sub_nonneg_direct yNormLeOne
      have correctionNonnegative :
          0 ≤ (1 - yNorm) * (a - xNorm) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct
          oneMinusYNonnegative aMinusXNonnegative
      calc
        Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤ 1 + xNorm - a - b :=
          scalarLowerBound
        _ ≤ 1 + xNorm * yNorm - a * yNorm - b := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ (1 - yNorm) * (a - xNorm) := correctionNonnegative
            _ = (1 + xNorm * yNorm - a * yNorm - b) -
                (1 + xNorm - a - b) := by ring1
    · have aLeXNorm : a ≤ xNorm := le_of_not_ge xNormLeA
      have xMinusANonnegative : 0 ≤ xNorm - a :=
        Fraction.Order.Arithmetic.sub_nonneg_direct aLeXNorm
      have correctionNonnegative : 0 ≤ yNorm * (xNorm - a) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct yNormNonnegative
          xMinusANonnegative
      have targetLeOneMinusB :
          Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤ 1 - b := by
        calc
          Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤ 1 -
            Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary := by
            exact Dirichlet.Window.IndexOne.Bounds.seventyOne_oneHundredTwelfths_le_one_sub_boundary
          _ ≤ 1 - b := by
            have negated :=
              Fraction.Order.Arithmetic.neg_le_neg_direct bLeBoundary
            have shifted :=
              Fraction.Order.Arithmetic.add_le_add_right_direct negated 1
            calc
              1 - Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary =
                  -Dirichlet.Window.IndexOne.Bounds.diagonalErrorBoundary + 1 := by ring1
              _ ≤ -b + 1 := shifted
              _ = 1 - b := by ring1
      calc
        Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤ 1 - b := targetLeOneMinusB
        _ ≤ 1 + xNorm * yNorm - a * yNorm - b := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ yNorm * (xNorm - a) := correctionNonnegative
            _ = (1 + xNorm * yNorm - a * yNorm - b) -
                (1 - b) := by ring1
  have gapExpansion :
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, a, b, c, d, Data.Gaussian.Norm.Basic.normSq]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im]
    ring1
  rw [gapExpansion]
  exact targetLeProjected.trans projectedGapLower

/-- Specialize the two-coefficient exterior condition to each single coefficient.

The pair `(-coefficient, 1)` is nonzero and gives exactly the error-distance and denominator-distance alternatives. -/
private theorem coefficientExterior_of_linearCombinationExterior
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian coefficient * denominatorRatio) := by
  intro coefficient
  rcases linearCombinationExterior (-coefficient) 1
      (Or.inr (by decide)) with errorExterior | denominatorExterior
  · left
    have identity :
        GaussianInt.toGaussian (-coefficient) + GaussianInt.toGaussian (1 : GaussianInt) * errorRatio =
          errorRatio - GaussianInt.toGaussian coefficient := by
      rw [GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one,
        Gaussian.Basic.one_mul]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.neg_re,
          Gaussian.Basic.neg_im] <;>
        ring1
    rw [← identity]
    exact errorExterior
  · right
    have identity :
        GaussianInt.toGaussian (-coefficient) * denominatorRatio +
            GaussianInt.toGaussian (1 : GaussianInt) =
          1 - GaussianInt.toGaussian coefficient * denominatorRatio := by
      rw [GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.neg_re,
          Gaussian.Basic.neg_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im] <;>
        ring1
    rw [← identity]
    exact denominatorExterior

/-- The norm-two exterior test forces a first-octant error inside the unit disk to vanish.

The tested expression is `1 - (1 - i) * errorRatio`; its squared norm is assumed at least one. -/
private theorem firstOctant_errorRatio_eq_zero_of_normTwoExterior
    (errorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (normTwoErrorExterior :
      (1 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq
          (1 - GaussianInt.toGaussian
            (1 - GaussianInt.Norm.Small.imaginaryUnit) * errorRatio)) :
    errorRatio = 0 := by
  let a := errorRatio.re
  let b := errorRatio.im
  let xNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  have aNonnegative : 0 ≤ a := realNonnegative
  have bNonnegative : 0 ≤ b := imaginaryNonnegative
  have bLeA : b ≤ a := imaginaryLeReal
  have xNormIdentity : xNorm = a ^ 2 + b ^ 2 := rfl
  have sumLeNorm : a + b ≤ xNorm := by
    have twiceSumLeTwiceNorm :
        2 * (a + b) ≤ 2 * xNorm := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        0 ≤ Data.Gaussian.Norm.Basic.normSq
              (1 - GaussianInt.toGaussian
                (1 - GaussianInt.Norm.Small.imaginaryUnit) * errorRatio) - 1 :=
          Fraction.Order.Arithmetic.sub_nonneg_direct normTwoErrorExterior
        _ = 2 * xNorm - 2 * (a + b) := by
          rw [show GaussianInt.toGaussian (1 - GaussianInt.Norm.Small.imaginaryUnit) =
            (⟨1, -1⟩ : Gaussian.Basic.Canonical) by rfl]
          dsimp only [xNorm, Data.Gaussian.Norm.Basic.normSq]
          simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re, Gaussian.Basic.one_im]
          ring1
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        (a + b) * 2 = 2 * (a + b) := by ring1
        _ ≤ 2 * xNorm := twiceSumLeTwiceNorm
        _ = xNorm * 2 := by ring1
    · decide
  have aNonpositive : a ≤ 0 := by
    by_cases aPositive : 0 < a
    · have aSquareLeNorm : a ^ 2 ≤ xNorm := by
        rw [xNormIdentity]
        exact le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.sq_nonneg_direct b)
      have aSquareLtOne : a ^ 2 < 1 :=
        lt_of_le_of_lt aSquareLeNorm errorInside
      have aLtOne : a < 1 := by
        by_cases oneLeA : 1 ≤ a
        · have oneLeASquare : (1 : Fraction.Rational) ≤ a ^ 2 := by
            calc
              (1 : Fraction.Rational) = 1 ^ 2 := by ring1
              _ ≤ a ^ 2 :=
                Fraction.Order.Arithmetic.pow_le_pow_direct (by decide)
                  oneLeA 2
          exact ((not_lt_of_ge oneLeASquare) aSquareLtOne).elim
        · exact lt_of_not_ge oneLeA
      have aSquareLtA : a ^ 2 < a := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            aPositive aLtOne
        calc
          a ^ 2 = a * a := by ring1
          _ < a * 1 := scaled
          _ = a := by ring1
      have bLeOne : b ≤ 1 := bLeA.trans aLtOne.le
      have bSquareLeB : b ^ 2 ≤ b := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            bLeOne bNonnegative
        calc
          b ^ 2 = b * b := by ring1
          _ ≤ b * 1 := scaled
          _ = b := by ring1
      have normLtSum : xNorm < a + b := by
        rw [xNormIdentity]
        have firstStep :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct aSquareLtA
            (b ^ 2)
        have secondStep : a + b ^ 2 ≤ a + b := by
          calc
            a + b ^ 2 = b ^ 2 + a := by ring1
            _ ≤ b + a :=
              Fraction.Order.Arithmetic.add_le_add_right_direct bSquareLeB a
            _ = a + b := by ring1
        exact firstStep.trans_le secondStep
      exact ((not_lt_of_ge sumLeNorm) normLtSum).elim
    · exact le_of_not_gt aPositive
  have aZero : a = 0 := le_antisymm aNonpositive aNonnegative
  have bZero : b = 0 := by
    apply le_antisymm
    · simpa only [aZero] using bLeA
    · exact bNonnegative
  apply Gaussian.Basic.ext
  · exact aZero
  · exact bZero

/-- Three neighbouring coefficient exclusions in the first octant force a
half-unit normalized determinant gap.  The proof is entirely coordinatewise.
The alternatives correspond respectively to coefficients `1`, `i`, and
`1+i`.
-/
theorem half_le_determinantGap_of_firstOctantObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    (1 / 2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let xNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  let yNorm := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  let dot := errorRatio.re * denominatorRatio.re -
    errorRatio.im * denominatorRatio.im
  have xNormLeOne : xNorm ≤ 1 := (show xNorm < 1 from errorInside).le
  have yNormLeOne : yNorm ≤ 1 :=
    (show yNorm < 1 from denominatorInside).le
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact Gaussian.Norm.Basic.normSq_nonneg denominatorRatio
  have realSquareLeNorm : errorRatio.re ^ 2 ≤ xNorm := by
    dsimp only [xNorm, Data.Gaussian.Norm.Basic.normSq]
    exact le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct errorRatio.im)
  have realSquareLeOne : errorRatio.re ^ 2 ≤ (1 : Fraction.Rational) ^ 2 := by
    simpa only [one_pow] using realSquareLeNorm.trans xNormLeOne
  have realLeOne : errorRatio.re ≤ 1 :=
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct (by decide)
      realSquareLeOne
  have realLtOne : errorRatio.re < 1 := by
    by_cases realEqualsOne : errorRatio.re = 1
    · have oneLeXNorm : (1 : Fraction.Rational) ≤ xNorm := by
        calc
          (1 : Fraction.Rational) = errorRatio.re ^ 2 := by rw [realEqualsOne]; ring1
          _ ≤ xNorm := realSquareLeNorm
      exact ((not_lt_of_ge oneLeXNorm) errorInside).elim
    · exact lt_of_le_of_ne realLeOne realEqualsOne
  have twiceRealLeOnePlusNorm :
      2 * errorRatio.re ≤ 1 + xNorm := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 - errorRatio.re) ^ 2 + errorRatio.im ^ 2 :=
        add_nonneg
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = (1 + xNorm) - 2 * errorRatio.re := by
        dsimp only [xNorm, Data.Gaussian.Norm.Basic.normSq]
        ring1
  have twiceSumLeOnePlusTwiceNorm :
      2 * (errorRatio.re + errorRatio.im) ≤ 1 + 2 * xNorm := by
    have squareSumNonnegative :
        0 ≤ (2 * errorRatio.re - 1) ^ 2 +
          (2 * errorRatio.im - 1) ^ 2 :=
      add_nonneg
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    have scaledDifferenceNonnegative :
        0 ≤ ((1 + 2 * xNorm) -
          2 * (errorRatio.re + errorRatio.im)) * 2 := by
      calc
        0 ≤ (2 * errorRatio.re - 1) ^ 2 +
            (2 * errorRatio.im - 1) ^ 2 := squareSumNonnegative
        _ = ((1 + 2 * xNorm) -
            2 * (errorRatio.re + errorRatio.im)) * 2 := by
          dsimp only [xNorm, Data.Gaussian.Norm.Basic.normSq]
          ring1
    have differenceNonnegative :
        0 ≤ (1 + 2 * xNorm) -
          2 * (errorRatio.re + errorRatio.im) := by
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
      · calc
          (0 : Fraction.Rational) * 2 = 0 := by ring1
          _ ≤ ((1 + 2 * xNorm) -
              2 * (errorRatio.re + errorRatio.im)) * 2 :=
            scaledDifferenceNonnegative
      · decide
    exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      differenceNonnegative
  have negTwiceImagLeNormPlusOne :
      -2 * denominatorRatio.im ≤ yNorm + 1 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (denominatorRatio.im + 1) ^ 2 +
          denominatorRatio.re ^ 2 :=
        add_nonneg
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = (yNorm + 1) - (-2 * denominatorRatio.im) := by
        dsimp only [yNorm, Data.Gaussian.Norm.Basic.normSq]
        ring1
  have gapExpansion :
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, Data.Gaussian.Norm.Basic.normSq]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im]
    ring1
  rcases coefficientExterior 1 with errorOneExterior | denominatorOneExterior
  · have twiceRealLeNorm : 2 * errorRatio.re ≤ xNorm := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        0 ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (1 : GaussianInt)) - 1 :=
          Fraction.Order.Arithmetic.sub_nonneg_direct errorOneExterior
        _ = xNorm - 2 * errorRatio.re := by
          dsimp only [xNorm, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            GaussianInt.one_re,
            GaussianInt.one_im]
          simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    have imaginarySquareLeRealSquare :
        errorRatio.im ^ 2 ≤ errorRatio.re ^ 2 :=
      Fraction.Order.Arithmetic.pow_le_pow_direct imaginaryNonnegative
        imaginaryLeReal 2
    have normLeTwiceRealSquare :
        xNorm ≤ 2 * errorRatio.re ^ 2 := by
      dsimp only [xNorm, Data.Gaussian.Norm.Basic.normSq]
      calc
        errorRatio.re ^ 2 + errorRatio.im ^ 2 ≤
            errorRatio.re ^ 2 + errorRatio.re ^ 2 :=
          Fraction.Order.Arithmetic.add_le_add_direct le_rfl
            imaginarySquareLeRealSquare
        _ = 2 * errorRatio.re ^ 2 := by ring1
    have twiceRealLeTwiceRealSquare :
        2 * errorRatio.re ≤ 2 * errorRatio.re ^ 2 :=
      twiceRealLeNorm.trans normLeTwiceRealSquare
    have realLeRealSquare :
        errorRatio.re ≤ errorRatio.re ^ 2 := by
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
      · calc
          errorRatio.re * 2 = 2 * errorRatio.re := by ring1
          _ ≤ 2 * errorRatio.re ^ 2 := twiceRealLeTwiceRealSquare
          _ = errorRatio.re ^ 2 * 2 := by ring1
      · decide
    have oneMinusRealPositive : 0 < 1 - errorRatio.re :=
      Fraction.Order.Arithmetic.sub_pos_direct realLtOne
    have realTimesGapNonpositive :
        errorRatio.re * (1 - errorRatio.re) ≤
          0 * (1 - errorRatio.re) := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        0 ≤ errorRatio.re ^ 2 - errorRatio.re :=
          Fraction.Order.Arithmetic.sub_nonneg_direct realLeRealSquare
        _ = 0 * (1 - errorRatio.re) -
            errorRatio.re * (1 - errorRatio.re) := by ring1
    have realNonpositive : errorRatio.re ≤ 0 :=
      Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        realTimesGapNonpositive oneMinusRealPositive
    have realZero : errorRatio.re = 0 :=
      le_antisymm realNonpositive realNonnegative
    have imaginaryZero : errorRatio.im = 0 := by
      apply le_antisymm
      · simpa only [realZero] using imaginaryLeReal
      · exact imaginaryNonnegative
    have errorRatioZero : errorRatio = 0 := by
      apply Gaussian.Basic.ext
      · exact realZero
      · exact imaginaryZero
    rw [errorRatioZero, Gaussian.Basic.mul_zero,
      Gaussian.Basic.sub_zero, Gaussian.Norm.Basic.normSq_one]
    decide
  · have twiceDenominatorRealLeNorm :
        2 * denominatorRatio.re ≤ yNorm := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        0 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (1 : GaussianInt) * denominatorRatio) - 1 :=
          Fraction.Order.Arithmetic.sub_nonneg_direct denominatorOneExterior
        _ = yNorm - 2 * denominatorRatio.re := by
          dsimp only [yNorm, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im,
            GaussianInt.one_re,
            GaussianInt.one_im]
          simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    rcases coefficientExterior GaussianInt.Norm.Small.imaginaryUnit with
        errorImaginaryExterior | denominatorImaginaryExterior
    · have twiceImaginaryLeNorm : 2 * errorRatio.im ≤ xNorm := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (errorRatio -
                GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct errorImaginaryExterior
          _ = xNorm - 2 * errorRatio.im := by
            dsimp only [xNorm, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      rcases coefficientExterior
          (1 + GaussianInt.Norm.Small.imaginaryUnit) with
          errorDiagonalExterior | denominatorDiagonalExterior
      · have twiceSumLeNormPlusOne :
            2 * (errorRatio.re + errorRatio.im) ≤ xNorm + 1 := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ Data.Gaussian.Norm.Basic.normSq
                (errorRatio - GaussianInt.toGaussian
                  (1 + GaussianInt.Norm.Small.imaginaryUnit)) - 1 :=
              Fraction.Order.Arithmetic.sub_nonneg_direct errorDiagonalExterior
            _ = (xNorm + 1) -
                2 * (errorRatio.re + errorRatio.im) := by
              dsimp only [xNorm, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
                GaussianInt.Norm.Small.imaginaryUnit]
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                GaussianInt.add_re,
                GaussianInt.add_im,
                GaussianInt.one_re,
                GaussianInt.one_im]
              simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
              ring1
        have realScaled :
            2 * errorRatio.re * denominatorRatio.re ≤
              errorRatio.re * yNorm := by
          have scaled :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              twiceDenominatorRealLeNorm realNonnegative
          calc
            2 * errorRatio.re * denominatorRatio.re =
                errorRatio.re * (2 * denominatorRatio.re) := by ring1
            _ ≤ errorRatio.re * yNorm := scaled
        have imaginaryScaled :
            -2 * errorRatio.im * denominatorRatio.im ≤
              errorRatio.im * (yNorm + 1) := by
          have scaled :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              negTwiceImagLeNormPlusOne imaginaryNonnegative
          calc
            -2 * errorRatio.im * denominatorRatio.im =
                errorRatio.im * (-2 * denominatorRatio.im) := by ring1
            _ ≤ errorRatio.im * (yNorm + 1) := scaled
        have summedDotBound :
            2 * dot ≤
              yNorm * (errorRatio.re + errorRatio.im) + errorRatio.im := by
          have added := Fraction.Order.Arithmetic.add_le_add_direct
            realScaled imaginaryScaled
          dsimp only [dot]
          calc
            2 * (errorRatio.re * denominatorRatio.re -
                errorRatio.im * denominatorRatio.im) =
                2 * errorRatio.re * denominatorRatio.re +
                  (-2 * errorRatio.im * denominatorRatio.im) := by ring1
            _ ≤ errorRatio.re * yNorm +
                errorRatio.im * (yNorm + 1) := added
            _ = yNorm * (errorRatio.re + errorRatio.im) +
                errorRatio.im := by ring1
        have sumScaled :
            2 * (yNorm * (errorRatio.re + errorRatio.im)) ≤
              yNorm * (xNorm + 1) := by
          have scaled :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              twiceSumLeNormPlusOne yNormNonnegative
          calc
            2 * (yNorm * (errorRatio.re + errorRatio.im)) =
                yNorm * (2 * (errorRatio.re + errorRatio.im)) := by ring1
            _ ≤ yNorm * (xNorm + 1) := scaled
        have doubledDotBound :
            4 * dot ≤
              2 * (yNorm * (errorRatio.re + errorRatio.im) +
                errorRatio.im) := by
          have scaled :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              summedDotBound (show (0 : Fraction.Rational) ≤ 2 by decide)
          calc
            4 * dot = (2 * dot) * 2 := by ring1
            _ ≤ (yNorm * (errorRatio.re + errorRatio.im) +
                errorRatio.im) * 2 := scaled
            _ = 2 * (yNorm * (errorRatio.re + errorRatio.im) +
                errorRatio.im) := by ring1
        have boundaryDotBound :
            4 * dot ≤ yNorm * (xNorm + 1) + xNorm := by
          calc
            4 * dot ≤
                2 * (yNorm * (errorRatio.re + errorRatio.im) +
                  errorRatio.im) := doubledDotBound
            _ = 2 * (yNorm * (errorRatio.re + errorRatio.im)) +
                2 * errorRatio.im := by ring1
            _ ≤ yNorm * (xNorm + 1) + xNorm :=
              Fraction.Order.Arithmetic.add_le_add_direct sumScaled
                twiceImaginaryLeNorm
        rw [gapExpansion]
        exact Dirichlet.Window.IndexOne.Bounds.half_le_of_fourDot_le_boundary xNorm yNorm dot xNormLeOne
          yNormLeOne boundaryDotBound
      · have twiceDiagonalProjection :
            2 * (denominatorRatio.re - denominatorRatio.im) ≤
              2 * yNorm := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ Data.Gaussian.Norm.Basic.normSq
                (1 - GaussianInt.toGaussian
                  (1 + GaussianInt.Norm.Small.imaginaryUnit) *
                    denominatorRatio) - 1 :=
              Fraction.Order.Arithmetic.sub_nonneg_direct
                denominatorDiagonalExterior
            _ = 2 * yNorm -
                2 * (denominatorRatio.re - denominatorRatio.im) := by
              dsimp only [yNorm, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
                GaussianInt.Norm.Small.imaginaryUnit]
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im,
                Gaussian.Basic.one_re,
                Gaussian.Basic.one_im,
                GaussianInt.add_re,
                GaussianInt.add_im,
                GaussianInt.one_re,
                GaussianInt.one_im]
              simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
              ring1
        have diagonalProjection :
            denominatorRatio.re - denominatorRatio.im ≤ yNorm := by
          apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
            (c := 2)
          · calc
              (denominatorRatio.re - denominatorRatio.im) * 2 =
                  2 * (denominatorRatio.re - denominatorRatio.im) := by
                ring1
              _ ≤ 2 * yNorm := twiceDiagonalProjection
              _ = yNorm * 2 := by ring1
          · decide
        have realDifferenceNonnegative :
            0 ≤ errorRatio.re - errorRatio.im :=
          Fraction.Order.Arithmetic.sub_nonneg_direct imaginaryLeReal
        have realScaled :
            2 * (errorRatio.re - errorRatio.im) *
                denominatorRatio.re ≤
              (errorRatio.re - errorRatio.im) * yNorm := by
          have scaled :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              twiceDenominatorRealLeNorm realDifferenceNonnegative
          calc
            2 * (errorRatio.re - errorRatio.im) * denominatorRatio.re =
                (errorRatio.re - errorRatio.im) *
                  (2 * denominatorRatio.re) := by ring1
            _ ≤ (errorRatio.re - errorRatio.im) * yNorm := scaled
        have diagonalScaled :
            2 * errorRatio.im *
                (denominatorRatio.re - denominatorRatio.im) ≤
              2 * errorRatio.im * yNorm :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            diagonalProjection
            (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
              imaginaryNonnegative)
        have summedDotBound :
            2 * dot ≤
              (errorRatio.re + errorRatio.im) * yNorm := by
          have added := Fraction.Order.Arithmetic.add_le_add_direct
            realScaled diagonalScaled
          dsimp only [dot]
          calc
            2 * (errorRatio.re * denominatorRatio.re -
                errorRatio.im * denominatorRatio.im) =
                2 * (errorRatio.re - errorRatio.im) *
                    denominatorRatio.re +
                  2 * errorRatio.im *
                    (denominatorRatio.re - denominatorRatio.im) := by
              ring1
            _ ≤ (errorRatio.re - errorRatio.im) * yNorm +
                2 * errorRatio.im * yNorm := added
            _ = (errorRatio.re + errorRatio.im) * yNorm := by ring1
        have twiceSumLeOnePlusTwiceNormFromExterior :
            2 * (errorRatio.re + errorRatio.im) ≤ 1 + 2 * xNorm := by
          have added := Fraction.Order.Arithmetic.add_le_add_direct
            twiceRealLeOnePlusNorm twiceImaginaryLeNorm
          calc
            2 * (errorRatio.re + errorRatio.im) =
                2 * errorRatio.re + 2 * errorRatio.im := by ring1
            _ ≤ (1 + xNorm) + xNorm := added
            _ = 1 + 2 * xNorm := by ring1
        have doubledDotBound :
            4 * dot ≤
              2 * ((errorRatio.re + errorRatio.im) * yNorm) := by
          have scaled :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              summedDotBound (show (0 : Fraction.Rational) ≤ 2 by decide)
          calc
            4 * dot = (2 * dot) * 2 := by ring1
            _ ≤ ((errorRatio.re + errorRatio.im) * yNorm) * 2 := scaled
            _ = 2 * ((errorRatio.re + errorRatio.im) * yNorm) := by ring1
        have sumScaled :
            2 * ((errorRatio.re + errorRatio.im) * yNorm) ≤
              (1 + 2 * xNorm) * yNorm := by
          have scaled :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              twiceSumLeOnePlusTwiceNormFromExterior yNormNonnegative
          calc
            2 * ((errorRatio.re + errorRatio.im) * yNorm) =
                (2 * (errorRatio.re + errorRatio.im)) * yNorm := by ring1
            _ ≤ (1 + 2 * xNorm) * yNorm := scaled
        rw [gapExpansion]
        exact Dirichlet.Window.IndexOne.Bounds.half_le_of_fourDot_le xNorm yNorm dot yNormLeOne
          (doubledDotBound.trans sumScaled)
    · have negTwiceDenominatorImagLeNorm :
          -2 * denominatorRatio.im ≤ yNorm := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (1 - GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
                denominatorRatio) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct
              denominatorImaginaryExterior
          _ = yNorm - (-2 * denominatorRatio.im) := by
            dsimp only [yNorm, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have realScaled :
          2 * errorRatio.re * denominatorRatio.re ≤
            errorRatio.re * yNorm := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            twiceDenominatorRealLeNorm realNonnegative
        calc
          2 * errorRatio.re * denominatorRatio.re =
              errorRatio.re * (2 * denominatorRatio.re) := by ring1
          _ ≤ errorRatio.re * yNorm := scaled
      have imaginaryScaled :
          -2 * errorRatio.im * denominatorRatio.im ≤
            errorRatio.im * yNorm := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            negTwiceDenominatorImagLeNorm imaginaryNonnegative
        calc
          -2 * errorRatio.im * denominatorRatio.im =
              errorRatio.im * (-2 * denominatorRatio.im) := by ring1
          _ ≤ errorRatio.im * yNorm := scaled
      have summedDotBound :
          2 * dot ≤ (errorRatio.re + errorRatio.im) * yNorm := by
        have added := Fraction.Order.Arithmetic.add_le_add_direct
          realScaled imaginaryScaled
        dsimp only [dot]
        calc
          2 * (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) =
              2 * errorRatio.re * denominatorRatio.re +
                (-2 * errorRatio.im * denominatorRatio.im) := by ring1
          _ ≤ errorRatio.re * yNorm + errorRatio.im * yNorm := added
          _ = (errorRatio.re + errorRatio.im) * yNorm := by ring1
      have doubledDotBound :
          4 * dot ≤ 2 * ((errorRatio.re + errorRatio.im) * yNorm) := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            summedDotBound (show (0 : Fraction.Rational) ≤ 2 by decide)
        calc
          4 * dot = (2 * dot) * 2 := by ring1
          _ ≤ ((errorRatio.re + errorRatio.im) * yNorm) * 2 := scaled
          _ = 2 * ((errorRatio.re + errorRatio.im) * yNorm) := by ring1
      have sumScaled :
          2 * ((errorRatio.re + errorRatio.im) * yNorm) ≤
            (1 + 2 * xNorm) * yNorm := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            twiceSumLeOnePlusTwiceNorm yNormNonnegative
        calc
          2 * ((errorRatio.re + errorRatio.im) * yNorm) =
              (2 * (errorRatio.re + errorRatio.im)) * yNorm := by ring1
          _ ≤ (1 + 2 * xNorm) * yNorm := scaled
      rw [gapExpansion]
      exact Dirichlet.Window.IndexOne.Bounds.half_le_of_fourDot_le xNorm yNorm dot yNormLeOne
        (doubledDotBound.trans sumScaled)

/-- Distance at least one from the unit coefficient forces a first-octant error to vanish.

The error itself has squared norm strictly less than one, with imaginary coordinate between zero and its real
coordinate. -/
private theorem firstOctant_errorRatio_eq_zero_of_oneExterior
    (errorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (errorOneExterior :
      (1 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (1 : GaussianInt))) :
    errorRatio = 0 := by
  have realSquareLeNorm : errorRatio.re ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq errorRatio := by
    exact le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct errorRatio.im)
  have realSquareLeOne : errorRatio.re ^ 2 ≤ (1 : Fraction.Rational) ^ 2 := by
    simpa only [one_pow] using realSquareLeNorm.trans errorInside.le
  have realLeOne : errorRatio.re ≤ 1 :=
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct (by decide)
      realSquareLeOne
  have realLtOne : errorRatio.re < 1 := by
    by_cases realEqualsOne : errorRatio.re = 1
    · have oneLeNorm : (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq errorRatio := by
        calc
          (1 : Fraction.Rational) = errorRatio.re ^ 2 := by
            rw [realEqualsOne]
            ring1
          _ ≤ Data.Gaussian.Norm.Basic.normSq errorRatio := realSquareLeNorm
      exact ((not_lt_of_ge oneLeNorm) errorInside).elim
    · exact lt_of_le_of_ne realLeOne realEqualsOne
  have twiceRealLeNorm : 2 * errorRatio.re ≤ Data.Gaussian.Norm.Basic.normSq errorRatio := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (1 : GaussianInt)) - 1 :=
        Fraction.Order.Arithmetic.sub_nonneg_direct errorOneExterior
      _ = Data.Gaussian.Norm.Basic.normSq errorRatio - 2 * errorRatio.re := by
        dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          GaussianInt.one_re,
          GaussianInt.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have imaginarySquareLeRealSquare :
      errorRatio.im ^ 2 ≤ errorRatio.re ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct imaginaryNonnegative
      imaginaryLeReal 2
  have normLeTwiceRealSquare :
      Data.Gaussian.Norm.Basic.normSq errorRatio ≤ 2 * errorRatio.re ^ 2 := by
    calc
      Data.Gaussian.Norm.Basic.normSq errorRatio = errorRatio.re ^ 2 + errorRatio.im ^ 2 := rfl
      _ ≤ errorRatio.re ^ 2 + errorRatio.re ^ 2 :=
        Fraction.Order.Arithmetic.add_le_add_direct le_rfl
          imaginarySquareLeRealSquare
      _ = 2 * errorRatio.re ^ 2 := by ring1
  have realLeRealSquare : errorRatio.re ≤ errorRatio.re ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        errorRatio.re * 2 = 2 * errorRatio.re := by ring1
        _ ≤ 2 * errorRatio.re ^ 2 := twiceRealLeNorm.trans
          normLeTwiceRealSquare
        _ = errorRatio.re ^ 2 * 2 := by ring1
    · decide
  have oneMinusRealPositive : 0 < 1 - errorRatio.re :=
    Fraction.Order.Arithmetic.sub_pos_direct realLtOne
  have realTimesGapNonpositive :
      errorRatio.re * (1 - errorRatio.re) ≤
        0 * (1 - errorRatio.re) := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ errorRatio.re ^ 2 - errorRatio.re :=
        Fraction.Order.Arithmetic.sub_nonneg_direct realLeRealSquare
      _ = 0 * (1 - errorRatio.re) -
          errorRatio.re * (1 - errorRatio.re) := by ring1
  have realNonpositive : errorRatio.re ≤ 0 :=
    Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      realTimesGapNonpositive oneMinusRealPositive
  have realZero : errorRatio.re = 0 :=
    le_antisymm realNonpositive realNonnegative
  have imaginaryZero : errorRatio.im = 0 := by
    apply le_antisymm
    · simpa only [realZero] using imaginaryLeReal
    · exact imaginaryNonnegative
  apply Gaussian.Basic.ext
  · exact realZero
  · exact imaginaryZero

/-- The exact finite first-octant chamber certificate strengthens the
three-coefficient normalized determinant gap from `1/2` to `15/28`.  The
two noncritical chambers actually have gap at least `3/4`; the displayed
rational constant is needed only when both non-real coefficient exclusions
occur on the error side. -/
theorem fifteen_twenty_eighths_le_determinantGap_of_firstOctantObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    (15 / 28 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  rcases coefficientExterior 1 with errorOneExterior | denominatorOneExterior
  · have errorRatioZero := Dirichlet.Window.IndexOne.Bounds.firstOctant_errorRatio_eq_zero_of_oneExterior
      errorRatio realNonnegative imaginaryNonnegative imaginaryLeReal
        errorInside errorOneExterior
    rw [errorRatioZero, Gaussian.Basic.mul_zero,
      Gaussian.Basic.sub_zero, Gaussian.Norm.Basic.normSq_one]
    decide
  · have denominatorRealObstruction :
        2 * denominatorRatio.re ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        0 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (1 : GaussianInt) * denominatorRatio) - 1 :=
          Fraction.Order.Arithmetic.sub_nonneg_direct denominatorOneExterior
        _ = Data.Gaussian.Norm.Basic.normSq denominatorRatio - 2 * denominatorRatio.re := by
          dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im,
            GaussianInt.one_re,
            GaussianInt.one_im]
          simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    rcases coefficientExterior GaussianInt.Norm.Small.imaginaryUnit with
        errorImaginaryExterior | denominatorImaginaryExterior
    · have errorImaginaryObstruction :
          2 * errorRatio.im ≤ Data.Gaussian.Norm.Basic.normSq errorRatio := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (errorRatio -
                GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct errorImaginaryExterior
          _ = Data.Gaussian.Norm.Basic.normSq errorRatio - 2 * errorRatio.im := by
            dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      rcases coefficientExterior
          (1 + GaussianInt.Norm.Small.imaginaryUnit) with
          errorDiagonalExterior | denominatorDiagonalExterior
      · have errorDiagonalObstruction :
            2 * (errorRatio.re + errorRatio.im) ≤
              Data.Gaussian.Norm.Basic.normSq errorRatio + 1 := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ Data.Gaussian.Norm.Basic.normSq
                (errorRatio - GaussianInt.toGaussian
                  (1 + GaussianInt.Norm.Small.imaginaryUnit)) - 1 :=
              Fraction.Order.Arithmetic.sub_nonneg_direct errorDiagonalExterior
            _ = (Data.Gaussian.Norm.Basic.normSq errorRatio + 1) -
                2 * (errorRatio.re + errorRatio.im) := by
              dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
                GaussianInt.Norm.Small.imaginaryUnit]
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                GaussianInt.add_re,
                GaussianInt.add_im,
                GaussianInt.one_re,
                GaussianInt.one_im]
              simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
              ring1
        exact Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_of_diagonalErrorChamber
          errorRatio denominatorRatio realNonnegative imaginaryNonnegative
          imaginaryLeReal errorInside denominatorInside
          errorImaginaryObstruction errorDiagonalObstruction
          denominatorRealObstruction
      · have twiceDiagonalProjection :
            2 * (denominatorRatio.re - denominatorRatio.im) ≤
              2 * Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ Data.Gaussian.Norm.Basic.normSq
                (1 - GaussianInt.toGaussian
                  (1 + GaussianInt.Norm.Small.imaginaryUnit) *
                    denominatorRatio) - 1 :=
              Fraction.Order.Arithmetic.sub_nonneg_direct
                denominatorDiagonalExterior
            _ = 2 * Data.Gaussian.Norm.Basic.normSq denominatorRatio -
                2 * (denominatorRatio.re - denominatorRatio.im) := by
              dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
                GaussianInt.Norm.Small.imaginaryUnit]
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im,
                Gaussian.Basic.one_re,
                Gaussian.Basic.one_im,
                GaussianInt.add_re,
                GaussianInt.add_im,
                GaussianInt.one_re,
                GaussianInt.one_im]
              simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
              ring1
        have denominatorDiagonalObstruction :
            denominatorRatio.re - denominatorRatio.im ≤
              Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
          apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
          · calc
              (denominatorRatio.re - denominatorRatio.im) * 2 =
                  2 * (denominatorRatio.re - denominatorRatio.im) := by ring1
              _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq denominatorRatio := twiceDiagonalProjection
              _ = Data.Gaussian.Norm.Basic.normSq denominatorRatio * 2 := by ring1
          · decide
        have chamberBound :=
          Dirichlet.Window.IndexOne.Bounds.three_quarters_le_of_diagonalDenominatorChamber
            errorRatio denominatorRatio realNonnegative imaginaryNonnegative
            errorInside denominatorInside errorImaginaryObstruction
            denominatorRealObstruction denominatorDiagonalObstruction
        exact (show (15 / 28 : Fraction.Rational) ≤ 3 / 4 by decide).trans
          chamberBound
    · have denominatorImaginaryObstruction :
          -2 * denominatorRatio.im ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (1 - GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
                denominatorRatio) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct
              denominatorImaginaryExterior
          _ = Data.Gaussian.Norm.Basic.normSq denominatorRatio - (-2 * denominatorRatio.im) := by
            dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have chamberBound := Dirichlet.Window.IndexOne.Bounds.three_quarters_le_of_axisChamber
        errorRatio denominatorRatio realNonnegative imaginaryNonnegative
        denominatorInside denominatorRealObstruction
        denominatorImaginaryObstruction
      exact (show (15 / 28 : Fraction.Rational) ≤ 3 / 4 by decide).trans
        chamberBound

/-- The full two-coefficient exterior condition adds the norm-two leading
combination `(1, -(1-i))` to the three neighbouring coefficient tests.  In
the only first-octant chamber below `3/4`, that combination supplies a second
denominator projection and raises the rational gap to `71/112`. -/
private theorem normTwoIndexOneGapThreshold_le_of_firstOctantLinearObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  have coefficientExterior :=
    Dirichlet.Window.IndexOne.Bounds.coefficientExterior_of_linearCombinationExterior errorRatio
      denominatorRatio linearCombinationExterior
  rcases coefficientExterior 1 with errorOneExterior | denominatorOneExterior
  · have errorRatioZero := Dirichlet.Window.IndexOne.Bounds.firstOctant_errorRatio_eq_zero_of_oneExterior
      errorRatio realNonnegative imaginaryNonnegative imaginaryLeReal
        errorInside errorOneExterior
    rw [errorRatioZero, Gaussian.Basic.mul_zero,
      Gaussian.Basic.sub_zero, Gaussian.Norm.Basic.normSq_one]
    exact Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold_le_one
  · have denominatorRealObstruction :
        2 * denominatorRatio.re ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        0 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (1 : GaussianInt) * denominatorRatio) - 1 :=
          Fraction.Order.Arithmetic.sub_nonneg_direct denominatorOneExterior
        _ = Data.Gaussian.Norm.Basic.normSq denominatorRatio - 2 * denominatorRatio.re := by
          dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im,
            GaussianInt.one_re,
            GaussianInt.one_im]
          simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    rcases coefficientExterior GaussianInt.Norm.Small.imaginaryUnit with
        errorImaginaryExterior | denominatorImaginaryExterior
    · have errorImaginaryObstruction :
          2 * errorRatio.im ≤ Data.Gaussian.Norm.Basic.normSq errorRatio := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (errorRatio -
                GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct errorImaginaryExterior
          _ = Data.Gaussian.Norm.Basic.normSq errorRatio - 2 * errorRatio.im := by
            dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      rcases coefficientExterior
          (1 + GaussianInt.Norm.Small.imaginaryUnit) with
          errorDiagonalExterior | denominatorDiagonalExterior
      · have errorDiagonalObstruction :
            2 * (errorRatio.re + errorRatio.im) ≤
              Data.Gaussian.Norm.Basic.normSq errorRatio + 1 := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ Data.Gaussian.Norm.Basic.normSq
                (errorRatio - GaussianInt.toGaussian
                  (1 + GaussianInt.Norm.Small.imaginaryUnit)) - 1 :=
              Fraction.Order.Arithmetic.sub_nonneg_direct errorDiagonalExterior
            _ = (Data.Gaussian.Norm.Basic.normSq errorRatio + 1) -
                2 * (errorRatio.re + errorRatio.im) := by
              dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
                GaussianInt.Norm.Small.imaginaryUnit]
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                GaussianInt.add_re,
                GaussianInt.add_im,
                GaussianInt.one_re,
                GaussianInt.one_im]
              simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
              ring1
        let diagonalCoefficient : GaussianInt :=
          1 - GaussianInt.Norm.Small.imaginaryUnit
        rcases linearCombinationExterior 1 (-diagonalCoefficient)
            (Or.inl (by decide)) with
            normTwoErrorExterior | normTwoDenominatorExterior
        · have errorExterior :
              (1 : Fraction.Rational) ≤
                Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian diagonalCoefficient * errorRatio) := by
            have identity :
                GaussianInt.toGaussian (1 : GaussianInt) +
                    GaussianInt.toGaussian (-diagonalCoefficient) * errorRatio =
                  1 - GaussianInt.toGaussian diagonalCoefficient * errorRatio := by
              rw [GaussianInt.toGaussian_one, GaussianInt.toGaussian_neg]
              apply Gaussian.Basic.ext <;>
                simp only [Gaussian.Basic.add_re,
                  Gaussian.Basic.add_im,
                  Gaussian.Basic.sub_re,
                  Gaussian.Basic.sub_im,
                  Gaussian.Basic.mul_re,
                  Gaussian.Basic.mul_im,
                  Gaussian.Basic.neg_re,
                  Gaussian.Basic.neg_im,
                  Gaussian.Basic.one_re,
                  Gaussian.Basic.one_im] <;>
                ring1
            rw [← identity]
            exact normTwoErrorExterior
          have errorRatioZero :=
            Dirichlet.Window.IndexOne.Bounds.firstOctant_errorRatio_eq_zero_of_normTwoExterior errorRatio
              realNonnegative imaginaryNonnegative imaginaryLeReal errorInside
              (by simpa only [diagonalCoefficient] using errorExterior)
          rw [errorRatioZero, Gaussian.Basic.mul_zero,
            Gaussian.Basic.sub_zero, Gaussian.Norm.Basic.normSq_one]
          exact Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold_le_one
        · have denominatorExterior :
              (1 : Fraction.Rational) ≤
                Data.Gaussian.Norm.Basic.normSq (denominatorRatio - GaussianInt.toGaussian diagonalCoefficient) :=
                  by
            have identity :
                GaussianInt.toGaussian (1 : GaussianInt) * denominatorRatio +
                    GaussianInt.toGaussian (-diagonalCoefficient) =
                  denominatorRatio - GaussianInt.toGaussian diagonalCoefficient := by
              rw [GaussianInt.toGaussian_one, GaussianInt.toGaussian_neg,
                Gaussian.Basic.one_mul]
              apply Gaussian.Basic.ext <;>
                simp only [Gaussian.Basic.add_re,
                  Gaussian.Basic.add_im,
                  Gaussian.Basic.sub_re,
                  Gaussian.Basic.sub_im,
                  Gaussian.Basic.neg_re,
                  Gaussian.Basic.neg_im] <;>
                ring1
            rw [← identity]
            exact normTwoDenominatorExterior
          have denominatorDiagonalObstruction :
              2 * (denominatorRatio.re - denominatorRatio.im) ≤
                Data.Gaussian.Norm.Basic.normSq denominatorRatio + 1 := by
            apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
            calc
              0 ≤ Data.Gaussian.Norm.Basic.normSq
                    (denominatorRatio - GaussianInt.toGaussian diagonalCoefficient) - 1 :=
                Fraction.Order.Arithmetic.sub_nonneg_direct denominatorExterior
              _ = (Data.Gaussian.Norm.Basic.normSq denominatorRatio + 1) -
                  2 * (denominatorRatio.re - denominatorRatio.im) := by
                dsimp only [diagonalCoefficient]
                rw [show GaussianInt.toGaussian (1 - GaussianInt.Norm.Small.imaginaryUnit) =
                    (⟨1, -1⟩ : Gaussian.Basic.Canonical) by rfl]
                dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
                simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
                ring1
          exact Dirichlet.Window.IndexOne.Bounds.seventyOne_oneHundredTwelfths_le_of_diagonalErrorChamber
            errorRatio denominatorRatio realNonnegative imaginaryNonnegative
            imaginaryLeReal errorInside denominatorInside
            errorImaginaryObstruction errorDiagonalObstruction
            denominatorRealObstruction denominatorDiagonalObstruction
      · have twiceDiagonalProjection :
            2 * (denominatorRatio.re - denominatorRatio.im) ≤
              2 * Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ Data.Gaussian.Norm.Basic.normSq
                (1 - GaussianInt.toGaussian
                  (1 + GaussianInt.Norm.Small.imaginaryUnit) *
                    denominatorRatio) - 1 :=
              Fraction.Order.Arithmetic.sub_nonneg_direct
                denominatorDiagonalExterior
            _ = 2 * Data.Gaussian.Norm.Basic.normSq denominatorRatio -
                2 * (denominatorRatio.re - denominatorRatio.im) := by
              dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
                GaussianInt.Norm.Small.imaginaryUnit]
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im,
                Gaussian.Basic.one_re,
                Gaussian.Basic.one_im,
                GaussianInt.add_re,
                GaussianInt.add_im,
                GaussianInt.one_re,
                GaussianInt.one_im]
              simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
              ring1
        have denominatorDiagonalObstruction :
            denominatorRatio.re - denominatorRatio.im ≤
              Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
          apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
          · calc
              (denominatorRatio.re - denominatorRatio.im) * 2 =
                  2 * (denominatorRatio.re - denominatorRatio.im) := by ring1
              _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq denominatorRatio := twiceDiagonalProjection
              _ = Data.Gaussian.Norm.Basic.normSq denominatorRatio * 2 := by ring1
          · decide
        have chamberBound :=
          Dirichlet.Window.IndexOne.Bounds.three_quarters_le_of_diagonalDenominatorChamber
            errorRatio denominatorRatio realNonnegative imaginaryNonnegative
            errorInside denominatorInside errorImaginaryObstruction
            denominatorRealObstruction denominatorDiagonalObstruction
        exact Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold_le_threeQuarters.trans chamberBound
    · have denominatorImaginaryObstruction :
          -2 * denominatorRatio.im ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (1 - GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
                denominatorRatio) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct
              denominatorImaginaryExterior
          _ = Data.Gaussian.Norm.Basic.normSq denominatorRatio - (-2 * denominatorRatio.im) := by
            dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have chamberBound := Dirichlet.Window.IndexOne.Bounds.three_quarters_le_of_axisChamber
        errorRatio denominatorRatio realNonnegative imaginaryNonnegative
        denominatorInside denominatorRealObstruction
        denominatorImaginaryObstruction
      exact Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold_le_threeQuarters.trans chamberBound

/-- All five small linear-combination certificates in the normalized first
octant imply every displayed threshold in the exact root-free gap cut.  This
is the Gaussian-coordinate bridge to the scalar four-region calculation. -/
theorem gapThreshold_le_of_firstOctantLinearObstructions
    (threshold : Fraction.Rational)
    (thresholdCertificate :
      Dirichlet.Window.IndexOne.Optimal.IsGapThreshold threshold)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    threshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let c := denominatorRatio.re
  let d := denominatorRatio.im
  let xNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  let yNorm := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  have coefficientExterior :=
    Dirichlet.Window.IndexOne.Bounds.coefficientExterior_of_linearCombinationExterior errorRatio
      denominatorRatio linearCombinationExterior
  rcases coefficientExterior 1 with errorOneExterior | denominatorOneExterior
  · have errorRatioZero := Dirichlet.Window.IndexOne.Bounds.firstOctant_errorRatio_eq_zero_of_oneExterior
      errorRatio realNonnegative imaginaryNonnegative imaginaryLeReal
        errorInside errorOneExterior
    rw [errorRatioZero, Gaussian.Basic.mul_zero,
      Gaussian.Basic.sub_zero, Gaussian.Norm.Basic.normSq_one]
    exact thresholdCertificate.1.le
  · have denominatorOne : 2 * c ≤ yNorm := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        0 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (1 : GaussianInt) * denominatorRatio) - 1 :=
          Fraction.Order.Arithmetic.sub_nonneg_direct denominatorOneExterior
        _ = yNorm - 2 * c := by
          dsimp only [yNorm, c, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im,
            GaussianInt.one_re,
            GaussianInt.one_im]
          simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    have imaginaryObstruction :
        2 * b ≤ xNorm ∨ -2 * d ≤ yNorm := by
      rcases coefficientExterior GaussianInt.Norm.Small.imaginaryUnit with
          errorExterior | denominatorExterior
      · left
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
                (errorRatio -
                  GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct errorExterior
          _ = xNorm - 2 * b := by
            dsimp only [xNorm, b, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      · right
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
                (1 - GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
                  denominatorRatio) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct denominatorExterior
          _ = yNorm - (-2 * d) := by
            dsimp only [yNorm, d, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
    have diagonalObstruction :
        2 * (a + b) ≤ xNorm + 1 ∨ c - d ≤ yNorm := by
      rcases coefficientExterior
          (1 + GaussianInt.Norm.Small.imaginaryUnit) with
          errorExterior | denominatorExterior
      · left
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
                (errorRatio - GaussianInt.toGaussian
                  (1 + GaussianInt.Norm.Small.imaginaryUnit)) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct errorExterior
          _ = (xNorm + 1) - 2 * (a + b) := by
            dsimp only [xNorm, a, b, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.one_re,
              GaussianInt.one_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      · right
        have twiceProjection : 2 * (c - d) ≤ 2 * yNorm := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ Data.Gaussian.Norm.Basic.normSq
                  (1 - GaussianInt.toGaussian
                    (1 + GaussianInt.Norm.Small.imaginaryUnit) *
                      denominatorRatio) - 1 :=
              Fraction.Order.Arithmetic.sub_nonneg_direct denominatorExterior
            _ = 2 * yNorm - 2 * (c - d) := by
              dsimp only [yNorm, c, d, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
                GaussianInt.Norm.Small.imaginaryUnit]
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im,
                Gaussian.Basic.one_re,
                Gaussian.Basic.one_im,
                GaussianInt.add_re,
                GaussianInt.add_im,
                GaussianInt.one_re,
                GaussianInt.one_im]
              simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
              ring1
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
        · calc
            (c - d) * 2 = 2 * (c - d) := by ring1
            _ ≤ 2 * yNorm := twiceProjection
            _ = yNorm * 2 := by ring1
        · decide
    let minusDiagonalCoefficient : GaussianInt :=
      1 - GaussianInt.Norm.Small.imaginaryUnit
    rcases linearCombinationExterior 1 (-minusDiagonalCoefficient)
        (Or.inl (by decide)) with
        minusErrorExterior | minusDenominatorExterior
    · have errorExterior :
          (1 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian minusDiagonalCoefficient * errorRatio) := by
        have identity :
            GaussianInt.toGaussian (1 : GaussianInt) +
                GaussianInt.toGaussian (-minusDiagonalCoefficient) * errorRatio =
              1 - GaussianInt.toGaussian minusDiagonalCoefficient * errorRatio := by
          rw [GaussianInt.toGaussian_one, GaussianInt.toGaussian_neg]
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.add_re,
              Gaussian.Basic.add_im,
              Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.neg_re,
              Gaussian.Basic.neg_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im] <;>
            ring1
        rw [← identity]
        exact minusErrorExterior
      have errorRatioZero :=
        Dirichlet.Window.IndexOne.Bounds.firstOctant_errorRatio_eq_zero_of_normTwoExterior errorRatio
          realNonnegative imaginaryNonnegative imaginaryLeReal errorInside
          (by simpa only [minusDiagonalCoefficient] using errorExterior)
      rw [errorRatioZero, Gaussian.Basic.mul_zero,
        Gaussian.Basic.sub_zero, Gaussian.Norm.Basic.normSq_one]
      exact thresholdCertificate.1.le
    · have denominatorExterior :
          (1 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (denominatorRatio -
              GaussianInt.toGaussian minusDiagonalCoefficient) := by
        have identity :
            GaussianInt.toGaussian (1 : GaussianInt) * denominatorRatio +
                GaussianInt.toGaussian (-minusDiagonalCoefficient) =
              denominatorRatio - GaussianInt.toGaussian minusDiagonalCoefficient := by
          rw [GaussianInt.toGaussian_one, GaussianInt.toGaussian_neg,
            Gaussian.Basic.one_mul]
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.add_re,
              Gaussian.Basic.add_im,
              Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.neg_re,
              Gaussian.Basic.neg_im] <;>
            ring1
        rw [← identity]
        exact minusDenominatorExterior
      have denominatorOneMinusI : 2 * (c - d) ≤ yNorm + 1 := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq (denominatorRatio -
                GaussianInt.toGaussian minusDiagonalCoefficient) - 1 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct denominatorExterior
          _ = (yNorm + 1) - 2 * (c - d) := by
            dsimp only [minusDiagonalCoefficient]
            rw [show GaussianInt.toGaussian (1 - GaussianInt.Norm.Small.imaginaryUnit) =
                (⟨1, -1⟩ : Gaussian.Basic.Canonical) by rfl]
            dsimp only [yNorm, c, d, Data.Gaussian.Norm.Basic.normSq,
              GaussianInt.toGaussian]
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
            ring1
      let plusDiagonalCoefficient : GaussianInt :=
        1 + GaussianInt.Norm.Small.imaginaryUnit
      have oppositeDiagonalObstruction :
          a - b ≤ xNorm ∨ 2 * (c + d) ≤ yNorm + 1 := by
        rcases linearCombinationExterior 1 (-plusDiagonalCoefficient)
            (Or.inl (by decide)) with
            plusErrorExterior | plusDenominatorExterior
        · left
          have errorExterior :
              (1 : Fraction.Rational) ≤
                Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian plusDiagonalCoefficient * errorRatio) :=
                  by
            have identity :
                GaussianInt.toGaussian (1 : GaussianInt) +
                    GaussianInt.toGaussian (-plusDiagonalCoefficient) * errorRatio =
                  1 - GaussianInt.toGaussian plusDiagonalCoefficient * errorRatio := by
              rw [GaussianInt.toGaussian_one, GaussianInt.toGaussian_neg]
              apply Gaussian.Basic.ext <;>
                simp only [Gaussian.Basic.add_re,
                  Gaussian.Basic.add_im,
                  Gaussian.Basic.sub_re,
                  Gaussian.Basic.sub_im,
                  Gaussian.Basic.mul_re,
                  Gaussian.Basic.mul_im,
                  Gaussian.Basic.neg_re,
                  Gaussian.Basic.neg_im,
                  Gaussian.Basic.one_re,
                  Gaussian.Basic.one_im] <;>
                ring1
            rw [← identity]
            exact plusErrorExterior
          have twiceProjection : 2 * (a - b) ≤ 2 * xNorm := by
            apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
            calc
              0 ≤ Data.Gaussian.Norm.Basic.normSq
                    (1 - GaussianInt.toGaussian plusDiagonalCoefficient * errorRatio) - 1 :=
                Fraction.Order.Arithmetic.sub_nonneg_direct errorExterior
              _ = 2 * xNorm - 2 * (a - b) := by
                dsimp only [plusDiagonalCoefficient, xNorm, a, b, Data.Gaussian.Norm.Basic.normSq,
                  GaussianInt.toGaussian, GaussianInt.Norm.Small.imaginaryUnit]
                simp only [Gaussian.Basic.sub_re,
                  Gaussian.Basic.sub_im,
                  Gaussian.Basic.mul_re,
                  Gaussian.Basic.mul_im,
                  Gaussian.Basic.one_re,
                  Gaussian.Basic.one_im,
                  GaussianInt.add_re,
                  GaussianInt.add_im,
                  GaussianInt.one_re,
                  GaussianInt.one_im]
                simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
                ring1
          apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
          · calc
              (a - b) * 2 = 2 * (a - b) := by ring1
              _ ≤ 2 * xNorm := twiceProjection
              _ = xNorm * 2 := by ring1
          · decide
        · right
          have denominatorExterior :
              (1 : Fraction.Rational) ≤
                Data.Gaussian.Norm.Basic.normSq (denominatorRatio -
                  GaussianInt.toGaussian plusDiagonalCoefficient) := by
            have identity :
                GaussianInt.toGaussian (1 : GaussianInt) * denominatorRatio +
                    GaussianInt.toGaussian (-plusDiagonalCoefficient) =
                  denominatorRatio - GaussianInt.toGaussian plusDiagonalCoefficient := by
              rw [GaussianInt.toGaussian_one, GaussianInt.toGaussian_neg,
                Gaussian.Basic.one_mul]
              apply Gaussian.Basic.ext <;>
                simp only [Gaussian.Basic.add_re,
                  Gaussian.Basic.add_im,
                  Gaussian.Basic.sub_re,
                  Gaussian.Basic.sub_im,
                  Gaussian.Basic.neg_re,
                  Gaussian.Basic.neg_im] <;>
                ring1
            rw [← identity]
            exact plusDenominatorExterior
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ Data.Gaussian.Norm.Basic.normSq (denominatorRatio -
                  GaussianInt.toGaussian plusDiagonalCoefficient) - 1 :=
              Fraction.Order.Arithmetic.sub_nonneg_direct denominatorExterior
            _ = (yNorm + 1) - 2 * (c + d) := by
              dsimp only [plusDiagonalCoefficient, yNorm, c, d, Data.Gaussian.Norm.Basic.normSq,
                GaussianInt.toGaussian, GaussianInt.Norm.Small.imaginaryUnit]
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                GaussianInt.add_re,
                GaussianInt.add_im,
                GaussianInt.one_re,
                GaussianInt.one_im]
              simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
              ring1
      have scalarBound :=
        Dirichlet.Window.IndexOne.Optimal.gapThreshold_le_gap_of_firstOctantFiveObstructions
          a b c d xNorm yNorm threshold realNonnegative imaginaryNonnegative
            imaginaryLeReal rfl rfl errorInside.le denominatorInside.le
            denominatorOne denominatorOneMinusI imaginaryObstruction
            diagonalObstruction oppositeDiagonalObstruction thresholdCertificate
      have gapExpansion :
          Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) =
            1 + xNorm * yNorm - 2 * (a * c - b * d) := by
        dsimp only [xNorm, yNorm, a, b, c, d, Data.Gaussian.Norm.Basic.normSq]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        ring1
      rw [gapExpansion]
      exact scalarBound

/-- The dyadic chamber bound `205/256` satisfies the exact rational gap cut. -/
private theorem firstRegionGapBound_isGapThreshold :
    Dirichlet.Window.IndexOne.Optimal.IsGapThreshold
      Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound := by
  constructor
  · unfold Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound
      Dirichlet.Window.IndexOne.Chambers.firstRegionProjectionBound
    decide
  · unfold Dirichlet.Window.IndexOne.Optimal.gapPolynomial
      Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound
      Dirichlet.Window.IndexOne.Chambers.firstRegionProjectionBound
    decide

/-- Compatibility form of the exact first-octant bridge at the earlier dyadic
threshold `205/256`. -/
theorem sharpIndexOneGapBound_le_of_firstOctantLinearObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) :=
  Dirichlet.Window.IndexOne.Bounds.gapThreshold_le_of_firstOctantLinearObstructions
    Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound
    Dirichlet.Window.IndexOne.Bounds.firstRegionGapBound_isGapThreshold errorRatio denominatorRatio
    realNonnegative imaginaryNonnegative imaginaryLeReal errorInside
    denominatorInside linearCombinationExterior

/-- Rotate normalized error data by the inverse of a displayed unit. -/
@[expose] def rotateErrorRatio (unit : GaussianInt) (value : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) * value

/-- Apply the matching unit rotation to normalized denominator data. -/
@[expose] def rotateDenominatorRatio
    (unit : GaussianInt) (value : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian unit * value

/-- Complex conjugation preserves the squared Gaussian norm. -/
private theorem normSq_conj (value : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj value) =
      Data.Gaussian.Norm.Basic.normSq value := by
  dsimp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.conj]
  ring1

/-- Multiplication by the conjugate of a Gaussian unit preserves the error norm. -/
private theorem normSq_rotateErrorRatio
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (value : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit value) =
      Data.Gaussian.Norm.Basic.normSq value := by
  unfold Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio
  rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian,
    GaussianInt.Embedding.normNat_conjugate, unitNorm]
  ring1

/-- Multiplication by a Gaussian unit preserves the denominator norm. -/
private theorem normSq_rotateDenominatorRatio
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (value : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit value) =
      Data.Gaussian.Norm.Basic.normSq value := by
  unfold Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio
  rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, unitNorm]
  ring1

/-- The paired unit rotations preserve the product of denominator and error ratios. -/
private theorem rotatedProduct
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical) :
    Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio *
        Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio =
      denominatorRatio * errorRatio := by
  have unitProperty :=
    GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one unitNorm
  have unitInverseInteger :
      unit * GaussianInt.Norm.Basic.conjugate unit = 1 :=
    GaussianInt.Norm.Small.self_mul_conjugate_of_isGaussianUnit unitProperty
  have unitInverse :
      GaussianInt.toGaussian unit *
          GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) =
        (1 : Gaussian.Basic.Canonical) := by
    rw [← GaussianInt.toGaussian_mul, unitInverseInteger, GaussianInt.toGaussian_one]
  unfold Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio
  calc
    (GaussianInt.toGaussian unit * denominatorRatio) *
        (GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) * errorRatio) =
      (GaussianInt.toGaussian unit *
          GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit)) *
        (denominatorRatio * errorRatio) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    _ = denominatorRatio * errorRatio := by
      rw [unitInverse, Gaussian.Basic.one_mul]

/-- Transport all single-coefficient exterior alternatives through paired unit rotations.

The coefficient is reindexed by a Gaussian unit, whose norm is one, so both tested squared norms retain their original
values. -/
private theorem rotatedCoefficientExterior
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio -
            GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq
          (1 - GaussianInt.toGaussian coefficient *
            Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio) := by
  intro coefficient
  let inverseUnit := GaussianInt.Norm.Basic.conjugate unit
  let sourceCoefficient := unit * coefficient
  have unitProperty :=
    GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one unitNorm
  have inverseUnitNorm : GaussianInt.normNat inverseUnit = 1 := by
    dsimp only [inverseUnit]
    rw [GaussianInt.Embedding.normNat_conjugate, unitNorm]
  have inverseUnitQuadrance :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian inverseUnit) = (1 : Fraction.Rational) := by
    rw [GaussianInt.normSq_toGaussian, inverseUnitNorm]
    rfl
  have inverseUnitIdentity : inverseUnit * unit = 1 := by
    dsimp only [inverseUnit]
    exact GaussianInt.Norm.Small.conjugate_mul_self_of_isGaussianUnit
      unitProperty
  rcases coefficientExterior sourceCoefficient with
      errorExterior | denominatorExterior
  · left
    have differenceIdentity :
        Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio - GaussianInt.toGaussian coefficient =
          GaussianInt.toGaussian inverseUnit *
            (errorRatio - GaussianInt.toGaussian sourceCoefficient) := by
      dsimp only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio, inverseUnit, sourceCoefficient]
      rw [GaussianInt.toGaussian_mul]
      have inverseIdentity :
          GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) *
              GaussianInt.toGaussian unit = (1 : Gaussian.Basic.Canonical) := by
        rw [← GaussianInt.toGaussian_mul, inverseUnitIdentity, GaussianInt.toGaussian_one]
      calc
        GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) * errorRatio -
              GaussianInt.toGaussian coefficient =
            GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) * errorRatio -
              (1 : Gaussian.Basic.Canonical) * GaussianInt.toGaussian coefficient := by
          rw [Gaussian.Basic.one_mul]
        _ = GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) * errorRatio -
              (GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) *
                GaussianInt.toGaussian unit) * GaussianInt.toGaussian coefficient := by
          rw [inverseIdentity]
        _ = GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) *
              (errorRatio - GaussianInt.toGaussian unit * GaussianInt.toGaussian coefficient) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im] <;>
            ring1
    rw [differenceIdentity, Gaussian.Norm.Basic.normSq_mul, inverseUnitQuadrance]
    calc
      (1 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian sourceCoefficient) := errorExterior
      _ = 1 * Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian sourceCoefficient) := by ring1
  · right
    have differenceIdentity :
        1 - GaussianInt.toGaussian coefficient *
            Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio =
          1 - GaussianInt.toGaussian sourceCoefficient * denominatorRatio := by
      dsimp only [Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio, sourceCoefficient]
      rw [GaussianInt.toGaussian_mul]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im] <;>
        ring1
    rw [differenceIdentity]
    exact denominatorExterior

/-- Transport the two-coefficient exterior predicate through paired unit rotations.

Unit multiplication reindexes the Gaussian coefficients and preserves both their nontriviality and the two norm
alternatives. -/
private theorem rotatedLinearCombinationExterior
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    ∀ leftCoefficient rightCoefficient : GaussianInt,
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
        (1 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian leftCoefficient +
                GaussianInt.toGaussian rightCoefficient *
                  Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio) ∨
          1 ≤
            Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian leftCoefficient *
                  Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio +
                GaussianInt.toGaussian rightCoefficient) := by
  intro leftCoefficient rightCoefficient coefficientNonzero
  let sourceLeft := unit * leftCoefficient
  have sourceNonzero : sourceLeft ≠ 0 ∨ rightCoefficient ≠ 0 := by
    rcases coefficientNonzero with leftNonzero | rightNonzero
    · left
      intro sourceZero
      have sourceNormZero : GaussianInt.normNat sourceLeft = 0 := by rw [sourceZero]; rfl
      have leftNormZero : GaussianInt.normNat leftCoefficient = 0 := by
        dsimp only [sourceLeft] at sourceNormZero
        rw [GaussianInt.normNat_mul, unitNorm, Nat.one_mul] at sourceNormZero
        exact sourceNormZero
      exact leftNonzero
        (GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero leftNormZero)
    · exact Or.inr rightNonzero
  rcases linearCombinationExterior sourceLeft rightCoefficient sourceNonzero with
      errorExterior | denominatorExterior
  · left
    have unitQuadrance : Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian unit) = (1 : Fraction.Rational) :=
      by
      rw [GaussianInt.normSq_toGaussian, unitNorm]
      rfl
    have identity :
        GaussianInt.toGaussian sourceLeft + GaussianInt.toGaussian rightCoefficient * errorRatio =
          GaussianInt.toGaussian unit *
            (GaussianInt.toGaussian leftCoefficient +
              GaussianInt.toGaussian rightCoefficient *
                Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio) := by
      have unitProperty :=
        GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one unitNorm
      have inverseIdentity :
          GaussianInt.toGaussian unit *
              GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) =
            (1 : Gaussian.Basic.Canonical) := by
        rw [← GaussianInt.toGaussian_mul,
          GaussianInt.Norm.Small.self_mul_conjugate_of_isGaussianUnit
            unitProperty,
          GaussianInt.toGaussian_one]
      dsimp only [sourceLeft, Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio]
      rw [GaussianInt.toGaussian_mul]
      calc
        GaussianInt.toGaussian unit * GaussianInt.toGaussian leftCoefficient +
              GaussianInt.toGaussian rightCoefficient * errorRatio =
            GaussianInt.toGaussian unit * GaussianInt.toGaussian leftCoefficient +
              GaussianInt.toGaussian rightCoefficient *
                ((GaussianInt.toGaussian unit *
                    GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit)) *
                  errorRatio) := by
            rw [inverseIdentity,
              Gaussian.Basic.one_mul]
        _ = GaussianInt.toGaussian unit *
            (GaussianInt.toGaussian leftCoefficient +
              GaussianInt.toGaussian rightCoefficient *
                (GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) *
                  errorRatio)) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.add_re,
              Gaussian.Basic.add_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im] <;>
            ring1
    rw [identity, Gaussian.Norm.Basic.normSq_mul, unitQuadrance] at errorExterior
    calc
      (1 : Fraction.Rational) ≤ 1 *
          Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian leftCoefficient +
              GaussianInt.toGaussian rightCoefficient *
                Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio) := errorExterior
      _ = Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian leftCoefficient +
            GaussianInt.toGaussian rightCoefficient *
              Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio) := by ring1
  · right
    have identity :
        GaussianInt.toGaussian sourceLeft * denominatorRatio +
            GaussianInt.toGaussian rightCoefficient =
          GaussianInt.toGaussian leftCoefficient *
              Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio +
            GaussianInt.toGaussian rightCoefficient := by
      dsimp only [sourceLeft, Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio]
      rw [GaussianInt.toGaussian_mul]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    rw [← identity]
    exact denominatorExterior

/-- Simultaneous conjugation preserves the single-coefficient exterior predicate.

Conjugate the Gaussian coefficient and use invariance of the two tested squared norms. -/
private theorem conjugatedCoefficientExterior
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj errorRatio -
            GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq
          (1 - GaussianInt.toGaussian coefficient *
            Data.Gaussian.Basic.conj denominatorRatio) := by
  intro coefficient
  have imaginaryCast : ((-coefficient.im : Int) : Fraction.Rational) =
      -(coefficient.im : Fraction.Rational) := Ring.IntCast.neg coefficient.im
  let sourceCoefficient :=
    GaussianInt.conj coefficient
  rcases coefficientExterior sourceCoefficient with
      errorExterior | denominatorExterior
  · left
    have differenceIdentity :
        Data.Gaussian.Basic.conj errorRatio -
            GaussianInt.toGaussian coefficient =
          Data.Gaussian.Basic.conj
            (errorRatio - GaussianInt.toGaussian sourceCoefficient) := by
      dsimp only [sourceCoefficient,
        GaussianInt.conj, GaussianInt.toGaussian,
        Data.Gaussian.Basic.conj]
      apply Gaussian.Basic.ext
      · rfl
      · simp only [Gaussian.Basic.sub_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt, imaginaryCast]
        ring1
    rw [differenceIdentity, Dirichlet.Window.IndexOne.Bounds.normSq_conj]
    exact errorExterior
  · right
    have differenceIdentity :
        1 - GaussianInt.toGaussian coefficient *
            Data.Gaussian.Basic.conj denominatorRatio =
          Data.Gaussian.Basic.conj
            (1 - GaussianInt.toGaussian sourceCoefficient * denominatorRatio) := by
      dsimp only [sourceCoefficient,
        GaussianInt.conj, GaussianInt.toGaussian,
        Data.Gaussian.Basic.conj]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im] <;>
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt, imaginaryCast] <;>
        ring1
    rw [differenceIdentity, Dirichlet.Window.IndexOne.Bounds.normSq_conj]
    exact denominatorExterior

/-- Simultaneous conjugation preserves all nontrivial two-coefficient exterior tests.

Conjugation retains the nonzero-coefficient disjunction and the squared norms of both linear combinations. -/
private theorem conjugatedLinearCombinationExterior
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    ∀ leftCoefficient rightCoefficient : GaussianInt,
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
        (1 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian leftCoefficient +
                GaussianInt.toGaussian rightCoefficient *
                  Data.Gaussian.Basic.conj errorRatio) ∨
          1 ≤
            Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian leftCoefficient *
                  Data.Gaussian.Basic.conj denominatorRatio +
                GaussianInt.toGaussian rightCoefficient) := by
  intro leftCoefficient rightCoefficient coefficientNonzero
  let sourceLeft :=
    GaussianInt.conj leftCoefficient
  let sourceRight :=
    GaussianInt.conj rightCoefficient
  have sourceNonzero : sourceLeft ≠ 0 ∨ sourceRight ≠ 0 := by
    rcases coefficientNonzero with leftNonzero | rightNonzero
    · left
      intro sourceZero
      have sourceNormZero : GaussianInt.normNat sourceLeft = 0 := by rw [sourceZero]; rfl
      have leftNormZero : GaussianInt.normNat leftCoefficient = 0 := by
        dsimp only [sourceLeft] at sourceNormZero
        rw [GaussianInt.normNat_conj] at sourceNormZero
        exact sourceNormZero
      exact leftNonzero
        (GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero leftNormZero)
    · right
      intro sourceZero
      have sourceNormZero : GaussianInt.normNat sourceRight = 0 := by rw [sourceZero]; rfl
      have rightNormZero : GaussianInt.normNat rightCoefficient = 0 := by
        dsimp only [sourceRight] at sourceNormZero
        rw [GaussianInt.normNat_conj] at sourceNormZero
        exact sourceNormZero
      exact rightNonzero
        (GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero rightNormZero)
  rcases linearCombinationExterior sourceLeft sourceRight sourceNonzero with
      errorExterior | denominatorExterior
  · left
    have identity :
        GaussianInt.toGaussian leftCoefficient +
            GaussianInt.toGaussian rightCoefficient *
              Data.Gaussian.Basic.conj errorRatio =
          Data.Gaussian.Basic.conj
            (GaussianInt.toGaussian sourceLeft +
              GaussianInt.toGaussian sourceRight * errorRatio) := by
      dsimp only [sourceLeft, sourceRight]
      rw [Gaussian.Basic.conj_add,
        Gaussian.Basic.conj_mul,
        GaussianInt.toGaussian_conj,
        GaussianInt.toGaussian_conj,
        Gaussian.Basic.conj_conj,
        Gaussian.Basic.conj_conj]
    rw [identity, Dirichlet.Window.IndexOne.Bounds.normSq_conj]
    exact errorExterior
  · right
    have identity :
        GaussianInt.toGaussian leftCoefficient *
              Data.Gaussian.Basic.conj denominatorRatio +
            GaussianInt.toGaussian rightCoefficient =
          Data.Gaussian.Basic.conj
            (GaussianInt.toGaussian sourceLeft * denominatorRatio +
              GaussianInt.toGaussian sourceRight) := by
      dsimp only [sourceLeft, sourceRight]
      rw [Gaussian.Basic.conj_add,
        Gaussian.Basic.conj_mul,
        GaussianInt.toGaussian_conj,
        GaussianInt.toGaussian_conj,
        Gaussian.Basic.conj_conj,
        Gaussian.Basic.conj_conj]
    rw [identity, Dirichlet.Window.IndexOne.Bounds.normSq_conj]
    exact denominatorExterior

/-- Transport the centered unit obstruction through paired unit rotations.

The reindexed coefficient still has Gaussian norm one, and the exterior threshold remains two. -/
private theorem rotatedCenteredUnitObstruction
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (obstruction : ∀ centeredUnit : GaussianInt,
      GaussianInt.normNat centeredUnit = 1 →
        (2 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian centeredUnit) ∨
          2 ≤ Data.Gaussian.Norm.Basic.normSq
            (1 - GaussianInt.toGaussian centeredUnit * denominatorRatio)) :
    ∀ centeredUnit : GaussianInt, GaussianInt.normNat centeredUnit = 1 →
      (2 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio -
            GaussianInt.toGaussian centeredUnit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq
          (1 - GaussianInt.toGaussian centeredUnit *
            Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio) := by
  intro centeredUnit centeredUnitNorm
  let inverseUnit := GaussianInt.Norm.Basic.conjugate unit
  let sourceUnit := unit * centeredUnit
  have sourceUnitNorm : GaussianInt.normNat sourceUnit = 1 := by
    dsimp only [sourceUnit]
    rw [GaussianInt.normNat_mul, unitNorm, centeredUnitNorm, Nat.one_mul]
  have unitProperty :=
    GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one unitNorm
  have inverseUnitNorm : GaussianInt.normNat inverseUnit = 1 := by
    dsimp only [inverseUnit]
    rw [GaussianInt.Embedding.normNat_conjugate, unitNorm]
  have inverseUnitQuadrance :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian inverseUnit) = (1 : Fraction.Rational) := by
    rw [GaussianInt.normSq_toGaussian, inverseUnitNorm]
    rfl
  have inverseUnitIdentity : inverseUnit * unit = 1 := by
    dsimp only [inverseUnit]
    exact GaussianInt.Norm.Small.conjugate_mul_self_of_isGaussianUnit
      unitProperty
  rcases obstruction sourceUnit sourceUnitNorm with
      errorExterior | denominatorExterior
  · left
    have differenceIdentity :
        Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio - GaussianInt.toGaussian centeredUnit =
          GaussianInt.toGaussian inverseUnit *
            (errorRatio - GaussianInt.toGaussian sourceUnit) := by
      dsimp only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio, inverseUnit, sourceUnit]
      rw [GaussianInt.toGaussian_mul]
      have inverseIdentity :
          GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) *
              GaussianInt.toGaussian unit = (1 : Gaussian.Basic.Canonical) := by
        rw [← GaussianInt.toGaussian_mul, inverseUnitIdentity, GaussianInt.toGaussian_one]
      calc
        GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) * errorRatio -
              GaussianInt.toGaussian centeredUnit =
            GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) * errorRatio -
              (1 : Gaussian.Basic.Canonical) * GaussianInt.toGaussian centeredUnit := by
          rw [Gaussian.Basic.one_mul]
        _ = GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) * errorRatio -
              (GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) *
                GaussianInt.toGaussian unit) * GaussianInt.toGaussian centeredUnit := by
          rw [inverseIdentity]
        _ = GaussianInt.toGaussian (GaussianInt.Norm.Basic.conjugate unit) *
              (errorRatio - GaussianInt.toGaussian unit * GaussianInt.toGaussian centeredUnit) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im] <;>
            ring1
    rw [differenceIdentity, Gaussian.Norm.Basic.normSq_mul, inverseUnitQuadrance]
    calc
      (2 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian sourceUnit) := errorExterior
      _ = 1 * Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian sourceUnit) := by ring1
  · right
    have differenceIdentity :
        1 - GaussianInt.toGaussian centeredUnit *
            Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio =
          1 - GaussianInt.toGaussian sourceUnit * denominatorRatio := by
      dsimp only [Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio, sourceUnit]
      rw [GaussianInt.toGaussian_mul]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im] <;>
        ring1
    rw [differenceIdentity]
    exact denominatorExterior

/-- Simultaneous conjugation preserves the centered unit obstruction.

Conjugating each unit retains its norm-one certificate and both threshold-two alternatives. -/
private theorem conjugatedCenteredUnitObstruction
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (obstruction : ∀ centeredUnit : GaussianInt,
      GaussianInt.normNat centeredUnit = 1 →
        (2 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian centeredUnit) ∨
          2 ≤ Data.Gaussian.Norm.Basic.normSq
            (1 - GaussianInt.toGaussian centeredUnit * denominatorRatio)) :
    ∀ centeredUnit : GaussianInt, GaussianInt.normNat centeredUnit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
          (Data.Gaussian.Basic.conj errorRatio -
            GaussianInt.toGaussian centeredUnit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq
          (1 - GaussianInt.toGaussian centeredUnit *
            Data.Gaussian.Basic.conj denominatorRatio) := by
  intro centeredUnit centeredUnitNorm
  have imaginaryCast : ((-centeredUnit.im : Int) : Fraction.Rational) =
      -(centeredUnit.im : Fraction.Rational) := Ring.IntCast.neg centeredUnit.im
  let sourceUnit :=
    GaussianInt.conj centeredUnit
  have sourceUnitNorm : GaussianInt.normNat sourceUnit = 1 := by
    dsimp only [sourceUnit]
    rw [GaussianInt.normNat_conj,
      centeredUnitNorm]
  rcases obstruction sourceUnit sourceUnitNorm with
      errorExterior | denominatorExterior
  · left
    have differenceIdentity :
        Data.Gaussian.Basic.conj errorRatio -
            GaussianInt.toGaussian centeredUnit =
          Data.Gaussian.Basic.conj
            (errorRatio - GaussianInt.toGaussian sourceUnit) := by
      dsimp only [sourceUnit,
        GaussianInt.conj, GaussianInt.toGaussian,
        Data.Gaussian.Basic.conj]
      apply Gaussian.Basic.ext
      · rfl
      · simp only [Gaussian.Basic.sub_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt, imaginaryCast]
        ring1
    rw [differenceIdentity, Dirichlet.Window.IndexOne.Bounds.normSq_conj]
    exact errorExterior
  · right
    have differenceIdentity :
        1 - GaussianInt.toGaussian centeredUnit *
            Data.Gaussian.Basic.conj denominatorRatio =
          Data.Gaussian.Basic.conj
            (1 - GaussianInt.toGaussian sourceUnit * denominatorRatio) := by
      dsimp only [sourceUnit,
        GaussianInt.conj, GaussianInt.toGaussian,
        Data.Gaussian.Basic.conj]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im, ← Rat.Fraction.Cast.intCast_eq_fromInt, imaginaryCast] <;>
        ring1
    rw [differenceIdentity, Dirichlet.Window.IndexOne.Bounds.normSq_conj]
    exact denominatorExterior

/-- Simultaneous conjugation preserves the squared norm of `1 - denominatorRatio * errorRatio`. -/
private theorem conjugatedProductGapNorm
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (1 - Data.Gaussian.Basic.conj denominatorRatio *
      Data.Gaussian.Basic.conj errorRatio) =
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  have identity :
      1 - Data.Gaussian.Basic.conj denominatorRatio *
          Data.Gaussian.Basic.conj errorRatio =
        Data.Gaussian.Basic.conj
          (1 - denominatorRatio * errorRatio) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        Gaussian.Basic.one_re,
        Gaussian.Basic.one_im,
        Data.Gaussian.Basic.conj] <;>
      ring1
  rw [identity, Dirichlet.Window.IndexOne.Bounds.normSq_conj]

/-- Transport the dyadic centered gap `205/128` from the first octant through a unit rotation.

The strict unit-disk bounds and centered unit exterior tests are preserved; the transformed product has the original
determinant-gap norm. -/
private theorem dyadicCenteredGapThreshold_le_of_rotatedFirstOctant
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re)
    (imaginaryNonnegative : 0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im)
    (imaginaryLeReal :
      (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im ≤
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      GaussianInt.normNat centeredUnit = 1 →
        (2 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian centeredUnit) ∨
          2 ≤ Data.Gaussian.Norm.Basic.normSq
            (1 - GaussianInt.toGaussian centeredUnit * denominatorRatio)) :
    IndexTwo.Bounds.dyadicCenteredGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  have rotatedErrorInside : Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit
    errorRatio) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have rotatedDenominatorInside :
      Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit
        denominatorRatio) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have result :=
    IndexTwo.Bounds.dyadicCenteredGapThreshold_le_determinantGap_of_firstOctantObstructions
      (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)
      (Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio)
      realNonnegative imaginaryNonnegative imaginaryLeReal rotatedErrorInside
      rotatedDenominatorInside
      (Dirichlet.Window.IndexOne.Bounds.rotatedCenteredUnitObstruction unit unitNorm errorRatio
        denominatorRatio obstruction)
  rw [Dirichlet.Window.IndexOne.Bounds.rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

/-- Transport the dyadic centered gap `205/128` from the first octant through a unit rotation followed by conjugation.

The strict unit-disk bounds and centered unit exterior tests are preserved; the transformed product has the original
determinant-gap norm. -/
private theorem dyadicCenteredGapThreshold_le_of_reflectedRotatedFirstOctant
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative :
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re)
    (imaginaryNonnegative :
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im)
    (imaginaryLeReal :
      (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im ≤
        (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      GaussianInt.normNat centeredUnit = 1 →
        (2 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian centeredUnit) ∨
          2 ≤ Data.Gaussian.Norm.Basic.normSq
            (1 - GaussianInt.toGaussian centeredUnit * denominatorRatio)) :
    IndexTwo.Bounds.dyadicCenteredGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let rotatedError := Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio
  let rotatedDenominator := Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio
  have reflectedErrorInside :
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj rotatedError) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_conj, Dirichlet.Window.IndexOne.Bounds.normSq_rotateErrorRatio unit
      unitNorm]
    exact errorInside
  have reflectedDenominatorInside :
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj rotatedDenominator) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_conj, Dirichlet.Window.IndexOne.Bounds.normSq_rotateDenominatorRatio
      unit unitNorm]
    exact denominatorInside
  have rotatedObstruction := Dirichlet.Window.IndexOne.Bounds.rotatedCenteredUnitObstruction unit unitNorm
    errorRatio denominatorRatio obstruction
  have result :=
    IndexTwo.Bounds.dyadicCenteredGapThreshold_le_determinantGap_of_firstOctantObstructions
      (Data.Gaussian.Basic.conj rotatedError)
      (Data.Gaussian.Basic.conj rotatedDenominator)
      realNonnegative imaginaryNonnegative imaginaryLeReal
      reflectedErrorInside reflectedDenominatorInside
      (Dirichlet.Window.IndexOne.Bounds.conjugatedCenteredUnitObstruction rotatedError rotatedDenominator
        rotatedObstruction)
  rw [Dirichlet.Window.IndexOne.Bounds.conjugatedProductGapNorm rotatedError rotatedDenominator] at result
  dsimp only [rotatedError, rotatedDenominator] at result
  rw [Dirichlet.Window.IndexOne.Bounds.rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

/-- Transport twice a certified exact centered gap threshold from the first octant through a unit rotation.

The strict unit-disk bounds and centered unit exterior tests are preserved; the transformed product has the original
determinant-gap norm. -/
private theorem twice_gapThreshold_le_of_rotatedFirstOctant
    (gap : Fraction.Rational)
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re)
    (imaginaryNonnegative : 0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im)
    (imaginaryLeReal :
      (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im ≤
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      GaussianInt.normNat centeredUnit = 1 →
        (2 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian centeredUnit) ∨
          2 ≤ Data.Gaussian.Norm.Basic.normSq
            (1 - GaussianInt.toGaussian centeredUnit * denominatorRatio)) :
    2 * gap ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  have rotatedErrorInside : Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit
    errorRatio) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have rotatedDenominatorInside :
      Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit
        denominatorRatio) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have result :=
    Dirichlet.Window.IndexTwo.Optimal.twice_gapThreshold_le_determinantGap_of_firstOctantObstructions
      gap certificate (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)
      (Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio) realNonnegative
      imaginaryNonnegative imaginaryLeReal rotatedErrorInside
      rotatedDenominatorInside
      (Dirichlet.Window.IndexOne.Bounds.rotatedCenteredUnitObstruction unit unitNorm errorRatio
        denominatorRatio obstruction)
  rw [Dirichlet.Window.IndexOne.Bounds.rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

/-- Transport twice a certified exact centered gap threshold from the first octant through a unit rotation followed by
conjugation.

The strict unit-disk bounds and centered unit exterior tests are preserved; the transformed product has the original
determinant-gap norm. -/
private theorem twice_gapThreshold_le_of_reflectedRotatedFirstOctant
    (gap : Fraction.Rational)
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative :
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re)
    (imaginaryNonnegative :
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im)
    (imaginaryLeReal :
      (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im ≤
        (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      GaussianInt.normNat centeredUnit = 1 →
        (2 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian centeredUnit) ∨
          2 ≤ Data.Gaussian.Norm.Basic.normSq
            (1 - GaussianInt.toGaussian centeredUnit * denominatorRatio)) :
    2 * gap ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let rotatedError := Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio
  let rotatedDenominator := Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio
  have reflectedErrorInside :
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj rotatedError) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_conj, Dirichlet.Window.IndexOne.Bounds.normSq_rotateErrorRatio unit
      unitNorm]
    exact errorInside
  have reflectedDenominatorInside :
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj rotatedDenominator) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_conj, Dirichlet.Window.IndexOne.Bounds.normSq_rotateDenominatorRatio
      unit unitNorm]
    exact denominatorInside
  have rotatedObstruction := Dirichlet.Window.IndexOne.Bounds.rotatedCenteredUnitObstruction unit unitNorm
    errorRatio denominatorRatio obstruction
  have result :=
    Dirichlet.Window.IndexTwo.Optimal.twice_gapThreshold_le_determinantGap_of_firstOctantObstructions
      gap certificate
      (Data.Gaussian.Basic.conj rotatedError)
      (Data.Gaussian.Basic.conj rotatedDenominator)
      realNonnegative imaginaryNonnegative imaginaryLeReal
      reflectedErrorInside reflectedDenominatorInside
      (Dirichlet.Window.IndexOne.Bounds.conjugatedCenteredUnitObstruction rotatedError rotatedDenominator
        rotatedObstruction)
  rw [Dirichlet.Window.IndexOne.Bounds.conjugatedProductGapNorm rotatedError rotatedDenominator] at result
  dsimp only [rotatedError, rotatedDenominator] at result
  rw [Dirichlet.Window.IndexOne.Bounds.rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

/-- Transport the gap `15/28` from the first octant through a unit rotation.

The strict unit-disk bounds and single-coefficient exterior tests are preserved; the transformed product has the
original determinant-gap norm. -/
private theorem fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re)
    (imaginaryNonnegative : 0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im)
    (imaginaryLeReal :
      (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im ≤
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    (15 / 28 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  have rotatedErrorInside : Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit
    errorRatio) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have rotatedDenominatorInside :
      Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit
        denominatorRatio) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have result := Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_firstOctantObstructions
    (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)
    (Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio)
    realNonnegative imaginaryNonnegative imaginaryLeReal rotatedErrorInside
    rotatedDenominatorInside
    (Dirichlet.Window.IndexOne.Bounds.rotatedCoefficientExterior unit unitNorm errorRatio denominatorRatio
      coefficientExterior)
  rw [Dirichlet.Window.IndexOne.Bounds.rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

/-- Transport the gap `15/28` from the first octant through a unit rotation followed by conjugation.

The strict unit-disk bounds and single-coefficient exterior tests are preserved; the transformed product has the
original determinant-gap norm. -/
private theorem fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative :
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re)
    (imaginaryNonnegative :
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im)
    (imaginaryLeReal :
      (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im ≤
        (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    (15 / 28 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let rotatedError := Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio
  let rotatedDenominator := Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio
  have reflectedErrorInside :
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj rotatedError) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_conj, Dirichlet.Window.IndexOne.Bounds.normSq_rotateErrorRatio unit
      unitNorm]
    exact errorInside
  have reflectedDenominatorInside :
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj rotatedDenominator) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_conj, Dirichlet.Window.IndexOne.Bounds.normSq_rotateDenominatorRatio
      unit unitNorm]
    exact denominatorInside
  have rotatedExterior := Dirichlet.Window.IndexOne.Bounds.rotatedCoefficientExterior unit unitNorm errorRatio
    denominatorRatio coefficientExterior
  have result := Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_firstOctantObstructions
    (Data.Gaussian.Basic.conj rotatedError)
    (Data.Gaussian.Basic.conj rotatedDenominator)
    realNonnegative imaginaryNonnegative imaginaryLeReal reflectedErrorInside
    reflectedDenominatorInside
    (Dirichlet.Window.IndexOne.Bounds.conjugatedCoefficientExterior rotatedError rotatedDenominator
      rotatedExterior)
  rw [Dirichlet.Window.IndexOne.Bounds.conjugatedProductGapNorm rotatedError rotatedDenominator] at result
  dsimp only [rotatedError, rotatedDenominator] at result
  rw [Dirichlet.Window.IndexOne.Bounds.rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

/-- A uniform determinant-gap lower bound for first-octant normalized ratios.

Both ratios lie strictly inside the unit disk and every nontrivial Gaussian two-coefficient combination satisfies an
exterior alternative. -/
private abbrev FirstOctantLinearCombinationGapBound
    (gapBound : Fraction.Rational) : Prop :=
  ∀ (errorRatio denominatorRatio : Gaussian.Basic.Canonical),
    0 ≤ errorRatio.re →
    0 ≤ errorRatio.im →
    errorRatio.im ≤ errorRatio.re →
    Data.Gaussian.Norm.Basic.normSq errorRatio < 1 →
    Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1 →
    (∀ leftCoefficient rightCoefficient : GaussianInt,
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
        (1 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian leftCoefficient +
                GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
          1 ≤
            Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                GaussianInt.toGaussian rightCoefficient)) →
    gapBound ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio)

/-- Transport a uniform first-octant gap bound through a Gaussian unit rotation.

The paired rotation preserves the product, strict disk bounds and all two-coefficient exterior tests. -/
private theorem gapBound_le_of_rotatedFirstOctant
    (gapBound : Fraction.Rational)
    (firstOctantBound : Dirichlet.Window.IndexOne.Bounds.FirstOctantLinearCombinationGapBound gapBound)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re)
    (imaginaryNonnegative : 0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im)
    (imaginaryLeReal :
      (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im ≤
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    gapBound ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  have rotatedErrorInside : Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit
    errorRatio) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have rotatedDenominatorInside :
      Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit
        denominatorRatio) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have result :=
    firstOctantBound
      (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)
      (Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio)
      realNonnegative imaginaryNonnegative imaginaryLeReal rotatedErrorInside
      rotatedDenominatorInside
      (Dirichlet.Window.IndexOne.Bounds.rotatedLinearCombinationExterior unit unitNorm errorRatio
        denominatorRatio linearCombinationExterior)
  rw [Dirichlet.Window.IndexOne.Bounds.rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

/-- Transport a uniform first-octant gap bound through rotation and conjugation.

The reflected rotated error satisfies the octant inequalities, while the original ratios retain the same determinant-gap
norm. -/
private theorem gapBound_le_of_reflectedRotatedFirstOctant
    (gapBound : Fraction.Rational)
    (firstOctantBound : Dirichlet.Window.IndexOne.Bounds.FirstOctantLinearCombinationGapBound gapBound)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative :
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re)
    (imaginaryNonnegative :
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im)
    (imaginaryLeReal :
      (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im ≤
        (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    gapBound ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let rotatedError := Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio
  let rotatedDenominator := Dirichlet.Window.IndexOne.Bounds.rotateDenominatorRatio unit denominatorRatio
  have reflectedErrorInside :
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj rotatedError) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_conj, Dirichlet.Window.IndexOne.Bounds.normSq_rotateErrorRatio unit
      unitNorm]
    exact errorInside
  have reflectedDenominatorInside :
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj rotatedDenominator) < 1 := by
    rw [Dirichlet.Window.IndexOne.Bounds.normSq_conj, Dirichlet.Window.IndexOne.Bounds.normSq_rotateDenominatorRatio
      unit unitNorm]
    exact denominatorInside
  have rotatedExterior := Dirichlet.Window.IndexOne.Bounds.rotatedLinearCombinationExterior unit unitNorm
    errorRatio denominatorRatio linearCombinationExterior
  have result :=
    firstOctantBound
      (Data.Gaussian.Basic.conj rotatedError)
      (Data.Gaussian.Basic.conj rotatedDenominator)
      realNonnegative imaginaryNonnegative imaginaryLeReal reflectedErrorInside
      reflectedDenominatorInside
      (Dirichlet.Window.IndexOne.Bounds.conjugatedLinearCombinationExterior rotatedError rotatedDenominator
        rotatedExterior)
  rw [Dirichlet.Window.IndexOne.Bounds.conjugatedProductGapNorm rotatedError rotatedDenominator] at result
  dsimp only [rotatedError, rotatedDenominator] at result
  rw [Dirichlet.Window.IndexOne.Bounds.rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

/-- Compute the error coordinates after rotation by `one` as `(re, im)`. -/
private theorem rotateErrorRatio_one (value : Gaussian.Basic.Canonical) :
    Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio (1 : GaussianInt) value = value := by
  apply Gaussian.Basic.ext <;>
    simp only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio, GaussianInt.Norm.Basic.conjugate,
      GaussianInt.toGaussian,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      GaussianInt.one_re,
      GaussianInt.one_im, Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
    ring1

/-- Compute the error coordinates after rotation by `imaginaryUnit` as `(im, -re)`. -/
private theorem rotateErrorRatio_imaginaryUnit (value : Gaussian.Basic.Canonical) :
    Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio GaussianInt.Norm.Small.imaginaryUnit value =
      ⟨value.im, -value.re⟩ := by
  apply Gaussian.Basic.ext <;>
    simp only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio, GaussianInt.Norm.Basic.conjugate,
      GaussianInt.Norm.Small.imaginaryUnit, GaussianInt.toGaussian,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
       Ring.IntCast.cast_zero, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
    ring1

/-- Compute the error coordinates after rotation by `negOne` as `(-re, -im)`. -/
private theorem rotateErrorRatio_negOne (value : Gaussian.Basic.Canonical) :
    Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio (-1 : GaussianInt) value =
      ⟨-value.re, -value.im⟩ := by
  apply Gaussian.Basic.ext <;>
    simp only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio, GaussianInt.Norm.Basic.conjugate,
      GaussianInt.toGaussian,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      GaussianInt.neg_re,
      GaussianInt.neg_im,
      GaussianInt.one_re,
      GaussianInt.one_im, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
    ring1

/-- Compute the error coordinates after rotation by `negImaginaryUnit` as `(-im, re)`. -/
private theorem rotateErrorRatio_negImaginaryUnit (value : Gaussian.Basic.Canonical) :
    Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio (-GaussianInt.Norm.Small.imaginaryUnit) value =
      ⟨-value.im, value.re⟩ := by
  apply Gaussian.Basic.ext <;>
    simp only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio, GaussianInt.Norm.Basic.conjugate,
      GaussianInt.Norm.Small.imaginaryUnit, GaussianInt.toGaussian,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      GaussianInt.neg_re,
      GaussianInt.neg_im, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
    ring1

/-- Compute the conjugated error rotation by `one` as `(re, -im)`. -/
private theorem conj_rotateErrorRatio_one (value : Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio (1 : GaussianInt) value) =
      ⟨value.re, -value.im⟩ := by
  rw [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_one]
  rfl

/-- Compute the conjugated error rotation by `imaginaryUnit` as `(im, re)`. -/
private theorem conj_rotateErrorRatio_imaginaryUnit (value : Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio GaussianInt.Norm.Small.imaginaryUnit value) =
      ⟨value.im, value.re⟩ := by
  rw [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_imaginaryUnit]
  apply Gaussian.Basic.ext
  · rfl
  · change - -value.re = value.re
    ring1

/-- Compute the conjugated error rotation by `negOne` as `(-re, im)`. -/
private theorem conj_rotateErrorRatio_negOne (value : Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio (-1 : GaussianInt) value) =
      ⟨-value.re, value.im⟩ := by
  rw [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negOne]
  apply Gaussian.Basic.ext
  · rfl
  · change - -value.im = value.im
    ring1

/-- Compute the conjugated error rotation by `negImaginaryUnit` as `(-im, -re)`. -/
private theorem conj_rotateErrorRatio_negImaginaryUnit (value : Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio (-GaussianInt.Norm.Small.imaginaryUnit) value) =
      ⟨-value.im, -value.re⟩ := by
  rw [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negImaginaryUnit]
  rfl

/-- The three-coefficient first-octant estimate covers every normalized pair:
one of four explicit unit rotations, optionally followed by conjugation,
places the displayed error ratio in that octant.  The case split is finite
and decidable on rational coordinates. -/
theorem fifteen_twenty_eighths_le_determinantGap_of_coefficientObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    (15 / 28 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  by_cases realNonnegative : 0 ≤ errorRatio.re
  · by_cases imaginaryNonnegative : 0 ≤ errorRatio.im
    · by_cases imaginaryLeReal : errorRatio.im ≤ errorRatio.re
      · apply Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
          (1 : GaussianInt) (by decide) errorRatio denominatorRatio
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_one] using realNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_one] using imaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_one] using imaginaryLeReal
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
      · have realLeImaginary : errorRatio.re ≤ errorRatio.im :=
          le_of_not_ge imaginaryLeReal
        apply Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
          GaussianInt.Norm.Small.imaginaryUnit (by decide) errorRatio
          denominatorRatio
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_imaginaryUnit] using
            imaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_imaginaryUnit] using
            realNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_imaginaryUnit] using
            realLeImaginary
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
    · have imaginaryNonpositive : errorRatio.im ≤ 0 :=
        le_of_not_ge imaginaryNonnegative
      have negImaginaryNonnegative : 0 ≤ -errorRatio.im := by
        have negated := Fraction.Order.Arithmetic.neg_le_neg_direct
          imaginaryNonpositive
        calc
          (0 : Fraction.Rational) = -0 := by ring1
          _ ≤ -errorRatio.im := negated
      by_cases negImaginaryLeReal : -errorRatio.im ≤ errorRatio.re
      · apply Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
          (1 : GaussianInt) (by decide) errorRatio denominatorRatio
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_one] using realNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_one] using
            negImaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_one] using negImaginaryLeReal
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
      · have realLeNegImaginary : errorRatio.re ≤ -errorRatio.im :=
          le_of_not_ge negImaginaryLeReal
        apply Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
          (-GaussianInt.Norm.Small.imaginaryUnit) (by decide) errorRatio
          denominatorRatio
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negImaginaryUnit] using
            negImaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negImaginaryUnit] using realNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negImaginaryUnit] using
            realLeNegImaginary
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
  · have realNonpositive : errorRatio.re ≤ 0 := le_of_not_ge realNonnegative
    have negRealNonnegative : 0 ≤ -errorRatio.re := by
      have negated := Fraction.Order.Arithmetic.neg_le_neg_direct
        realNonpositive
      calc
        (0 : Fraction.Rational) = -0 := by ring1
        _ ≤ -errorRatio.re := negated
    by_cases imaginaryNonnegative : 0 ≤ errorRatio.im
    · by_cases negRealLeImaginary : -errorRatio.re ≤ errorRatio.im
      · apply Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
          GaussianInt.Norm.Small.imaginaryUnit (by decide) errorRatio
          denominatorRatio
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_imaginaryUnit] using
            imaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_imaginaryUnit] using
            negRealNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_imaginaryUnit] using
            negRealLeImaginary
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
      · have imaginaryLeNegReal : errorRatio.im ≤ -errorRatio.re :=
          le_of_not_ge negRealLeImaginary
        apply Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
          (-1 : GaussianInt) (by decide) errorRatio denominatorRatio
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negOne] using negRealNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negOne] using
            imaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negOne] using imaginaryLeNegReal
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
    · have imaginaryNonpositive : errorRatio.im ≤ 0 :=
        le_of_not_ge imaginaryNonnegative
      have negImaginaryNonnegative : 0 ≤ -errorRatio.im := by
        have negated := Fraction.Order.Arithmetic.neg_le_neg_direct
          imaginaryNonpositive
        calc
          (0 : Fraction.Rational) = -0 := by ring1
          _ ≤ -errorRatio.im := negated
      by_cases negImaginaryLeNegReal :
          -errorRatio.im ≤ -errorRatio.re
      · apply Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
          (-1 : GaussianInt) (by decide) errorRatio denominatorRatio
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negOne] using negRealNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negOne] using negImaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negOne] using negImaginaryLeNegReal
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
      · have negRealLeNegImaginary :
            -errorRatio.re ≤ -errorRatio.im :=
          le_of_not_ge negImaginaryLeNegReal
        apply Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
          (-GaussianInt.Norm.Small.imaginaryUnit) (by decide) errorRatio
          denominatorRatio
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negImaginaryUnit] using
            negImaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negImaginaryUnit] using
            negRealNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negImaginaryUnit] using
            negRealLeNegImaginary
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior

/-- A bound supplied in both rotated first-octant forms covers all eight
displayed coordinate octants.  The dispatcher depends only on decidable
rational signs and is shared by the index-one and centered index-two proofs. -/
private theorem gapBound_le_of_eightFirstOctants
    (gapBound : Fraction.Rational)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (rotatedCase : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re →
      0 ≤ (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im →
      (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).im ≤
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio).re →
      gapBound ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio))
    (reflectedCase : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re →
      0 ≤ (Data.Gaussian.Basic.conj
        (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im →
      (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).im ≤
        (Data.Gaussian.Basic.conj
          (Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio unit errorRatio)).re →
      gapBound ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio)) :
    gapBound ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  by_cases realNonnegative : 0 ≤ errorRatio.re
  · by_cases imaginaryNonnegative : 0 ≤ errorRatio.im
    · by_cases imaginaryLeReal : errorRatio.im ≤ errorRatio.re
      · apply rotatedCase (1 : GaussianInt) (by decide)
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_one] using realNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_one] using imaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_one] using imaginaryLeReal
      · have realLeImaginary : errorRatio.re ≤ errorRatio.im :=
          le_of_not_ge imaginaryLeReal
        apply reflectedCase GaussianInt.Norm.Small.imaginaryUnit (by decide)
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_imaginaryUnit] using
            imaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_imaginaryUnit] using
            realNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_imaginaryUnit] using
            realLeImaginary
    · have imaginaryNonpositive : errorRatio.im ≤ 0 :=
        le_of_not_ge imaginaryNonnegative
      have negImaginaryNonnegative : 0 ≤ -errorRatio.im := by
        have negated := Fraction.Order.Arithmetic.neg_le_neg_direct
          imaginaryNonpositive
        calc
          (0 : Fraction.Rational) = -0 := by ring1
          _ ≤ -errorRatio.im := negated
      by_cases negImaginaryLeReal : -errorRatio.im ≤ errorRatio.re
      · apply reflectedCase (1 : GaussianInt) (by decide)
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_one] using realNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_one] using
            negImaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_one] using negImaginaryLeReal
      · have realLeNegImaginary : errorRatio.re ≤ -errorRatio.im :=
          le_of_not_ge negImaginaryLeReal
        apply rotatedCase (-GaussianInt.Norm.Small.imaginaryUnit) (by decide)
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negImaginaryUnit] using
            negImaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negImaginaryUnit] using realNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negImaginaryUnit] using
            realLeNegImaginary
  · have realNonpositive : errorRatio.re ≤ 0 := le_of_not_ge realNonnegative
    have negRealNonnegative : 0 ≤ -errorRatio.re := by
      have negated := Fraction.Order.Arithmetic.neg_le_neg_direct
        realNonpositive
      calc
        (0 : Fraction.Rational) = -0 := by ring1
        _ ≤ -errorRatio.re := negated
    by_cases imaginaryNonnegative : 0 ≤ errorRatio.im
    · by_cases negRealLeImaginary : -errorRatio.re ≤ errorRatio.im
      · apply rotatedCase GaussianInt.Norm.Small.imaginaryUnit (by decide)
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_imaginaryUnit] using
            imaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_imaginaryUnit] using
            negRealNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_imaginaryUnit] using
            negRealLeImaginary
      · have imaginaryLeNegReal : errorRatio.im ≤ -errorRatio.re :=
          le_of_not_ge negRealLeImaginary
        apply reflectedCase (-1 : GaussianInt) (by decide)
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negOne] using negRealNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negOne] using
            imaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negOne] using imaginaryLeNegReal
    · have imaginaryNonpositive : errorRatio.im ≤ 0 :=
        le_of_not_ge imaginaryNonnegative
      have negImaginaryNonnegative : 0 ≤ -errorRatio.im := by
        have negated := Fraction.Order.Arithmetic.neg_le_neg_direct
          imaginaryNonpositive
        calc
          (0 : Fraction.Rational) = -0 := by ring1
          _ ≤ -errorRatio.im := negated
      by_cases negImaginaryLeNegReal :
          -errorRatio.im ≤ -errorRatio.re
      · apply rotatedCase (-1 : GaussianInt) (by decide)
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negOne] using negRealNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negOne] using negImaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.rotateErrorRatio_negOne] using negImaginaryLeNegReal
      · have negRealLeNegImaginary :
            -errorRatio.re ≤ -errorRatio.im :=
          le_of_not_ge negImaginaryLeNegReal
        apply reflectedCase (-GaussianInt.Norm.Small.imaginaryUnit) (by decide)
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negImaginaryUnit] using
            negImaginaryNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negImaginaryUnit] using
            negRealNonnegative
        · simpa only [Dirichlet.Window.IndexOne.Bounds.conj_rotateErrorRatio_negImaginaryUnit] using
            negRealLeNegImaginary

/-- Extend a first-octant gap bound to all normalized ratios.

A finite split on rational coordinate signs selects one of four unit rotations and optional conjugation, preserving the
full two-coefficient exterior predicate. -/
private theorem gapBound_le_of_linearCombinationObstructions
    (gapBound : Fraction.Rational)
    (firstOctantBound : Dirichlet.Window.IndexOne.Bounds.FirstOctantLinearCombinationGapBound gapBound)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    gapBound ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  apply Dirichlet.Window.IndexOne.Bounds.gapBound_le_of_eightFirstOctants gapBound errorRatio denominatorRatio
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact Dirichlet.Window.IndexOne.Bounds.gapBound_le_of_rotatedFirstOctant gapBound firstOctantBound unit
      unitNorm errorRatio denominatorRatio realNonnegative imaginaryNonnegative
      imaginaryLeReal errorInside denominatorInside linearCombinationExterior
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact Dirichlet.Window.IndexOne.Bounds.gapBound_le_of_reflectedRotatedFirstOctant gapBound firstOctantBound
      unit unitNorm errorRatio denominatorRatio realNonnegative
      imaginaryNonnegative imaginaryLeReal errorInside denominatorInside
      linearCombinationExterior

/-- The centered index-two chamber is invariant under the same eight finite
coordinate symmetries.  Combining the forced centered orientation with the
affine first-octant calculation gives the global gap `205/128`. -/
theorem dyadicCenteredGapThreshold_le_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      GaussianInt.normNat centeredUnit = 1 →
        (2 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian centeredUnit) ∨
          2 ≤ Data.Gaussian.Norm.Basic.normSq
            (1 - GaussianInt.toGaussian centeredUnit * denominatorRatio)) :
    IndexTwo.Bounds.dyadicCenteredGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  apply Dirichlet.Window.IndexOne.Bounds.gapBound_le_of_eightFirstOctants
    IndexTwo.Bounds.dyadicCenteredGapThreshold errorRatio denominatorRatio
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact Dirichlet.Window.IndexOne.Bounds.dyadicCenteredGapThreshold_le_of_rotatedFirstOctant unit unitNorm
      errorRatio denominatorRatio realNonnegative imaginaryNonnegative
      imaginaryLeReal errorInside denominatorInside obstruction
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact Dirichlet.Window.IndexOne.Bounds.dyadicCenteredGapThreshold_le_of_reflectedRotatedFirstOctant unit
      unitNorm errorRatio denominatorRatio realNonnegative
      imaginaryNonnegative imaginaryLeReal errorInside denominatorInside
      obstruction

/-- Every displayed threshold in the exact centered cut survives the eight
rational coordinate symmetries. -/
theorem twice_gapThreshold_le_of_centeredUnitObstructions
    (gap : Fraction.Rational)
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      GaussianInt.normNat centeredUnit = 1 →
        (2 : Fraction.Rational) ≤
            Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian centeredUnit) ∨
          2 ≤ Data.Gaussian.Norm.Basic.normSq
            (1 - GaussianInt.toGaussian centeredUnit * denominatorRatio)) :
    2 * gap ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  apply Dirichlet.Window.IndexOne.Bounds.gapBound_le_of_eightFirstOctants
    (2 * gap) errorRatio denominatorRatio
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact Dirichlet.Window.IndexOne.Bounds.twice_gapThreshold_le_of_rotatedFirstOctant gap certificate unit
      unitNorm errorRatio denominatorRatio realNonnegative
      imaginaryNonnegative imaginaryLeReal errorInside denominatorInside
      obstruction
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact Dirichlet.Window.IndexOne.Bounds.twice_gapThreshold_le_of_reflectedRotatedFirstOctant gap certificate
      unit unitNorm errorRatio denominatorRatio realNonnegative
      imaginaryNonnegative imaginaryLeReal errorInside denominatorInside
      obstruction

/-- The earlier norm-two first-octant certificate, lifted through the shared
eight-symmetry dispatcher. -/
private theorem normTwoIndexOneGapThreshold_le_of_linearCombinationObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  exact Dirichlet.Window.IndexOne.Bounds.gapBound_le_of_linearCombinationObstructions
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold_le_of_firstOctantLinearObstructions
    errorRatio denominatorRatio errorInside denominatorInside
    linearCombinationExterior

/-- Every displayed threshold in the exact root-free gap cut survives the
eight rational coordinate symmetries. -/
theorem gapThreshold_le_of_linearCombinationObstructions
    (threshold : Fraction.Rational)
    (thresholdCertificate :
      Dirichlet.Window.IndexOne.Optimal.IsGapThreshold threshold)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    threshold ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  exact Dirichlet.Window.IndexOne.Bounds.gapBound_le_of_linearCombinationObstructions threshold
    (Dirichlet.Window.IndexOne.Bounds.gapThreshold_le_of_firstOctantLinearObstructions threshold
      thresholdCertificate)
    errorRatio denominatorRatio errorInside denominatorInside
    linearCombinationExterior

/-- The dyadic first-octant chamber certificate is stable under the same
eight finite coordinate symmetries.  Thus every normalized pair satisfying
the full coefficient exterior predicate has gap at least `205/256`. -/
theorem sharpIndexOneGapBound_le_of_linearCombinationObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient * denominatorRatio +
                  GaussianInt.toGaussian rightCoefficient)) :
    Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  exact Dirichlet.Window.IndexOne.Bounds.gapBound_le_of_linearCombinationObstructions
    Dirichlet.Window.IndexOne.Chambers.firstRegionGapBound
    Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound_le_of_firstOctantLinearObstructions
    errorRatio denominatorRatio errorInside denominatorInside
    linearCombinationExterior

/-- Single-coefficient exterior obstructions give a determinant gap of at least `1/2`.

Both normalized ratios lie strictly inside the unit disk; the stronger `15/28` octant estimate implies the stated bound.
-/
theorem half_le_determinantGap_of_coefficientObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    (1 / 2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  exact (show (1 / 2 : Fraction.Rational) ≤ 15 / 28 by decide).trans
    (Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_coefficientObstructions
      errorRatio denominatorRatio errorInside denominatorInside
      coefficientExterior)

/-- Every consecutive normalized pair has determinant gap at least `15/28`.
Unlike the earlier nearest-coefficient quadratic estimate, this uses all
three neighbouring coefficients in the finite octant containing the error
ratio. -/
theorem AreConsecutiveBest.fifteen_twenty_eighths_le_normalizedDeterminantGap
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    (15 / 28 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.IndexOne.Bounds.fifteen_twenty_eighths_le_determinantGap_of_coefficientObstructions
    (Dirichlet.Window.Basic.errorRatio source.value lower upper)
    (Dirichlet.Window.Basic.denominatorRatio lower upper)
    (IndexTwo.Bounds.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.normalizedCoefficientExterior
      consecutive)

/-- Every consecutive normalized pair has determinant gap at least the
displayed `71/112`.  The proof uses arbitrary nontrivial two-coefficient
combinations, including the norm-two leading combination that is unavailable
to the one-coefficient normalization. -/
theorem AreConsecutiveBest.normTwoIndexOneGapThreshold_le_normalizedDeterminantGap
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold_le_of_linearCombinationObstructions
    (Dirichlet.Window.Basic.errorRatio source.value lower upper)
    (Dirichlet.Window.Basic.denominatorRatio lower upper)
    (IndexTwo.Bounds.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.normalizedLinearCombinationExterior
      consecutive)

/-- Every consecutive normalized pair satisfies the strengthened displayed
gap `205/256`.  The proof uses five coefficient obstructions in one rational
octant and the shared finite eight-symmetry dispatcher. -/
theorem AreConsecutiveBest.sharpIndexOneGapBound_le_normalizedDeterminantGap
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound_le_of_linearCombinationObstructions
    (Dirichlet.Window.Basic.errorRatio source.value lower upper)
    (Dirichlet.Window.Basic.denominatorRatio lower upper)
    (IndexTwo.Bounds.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.normalizedLinearCombinationExterior
      consecutive)

/-- Every rational threshold on the exact quadratic cut bounds the normalized
determinant gap of consecutive best pairs.  This is the square-root-free
index-one form of Chevallier's optimal chamber constant. -/
theorem AreConsecutiveBest.gapThreshold_le_normalizedDeterminantGap
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (threshold : Fraction.Rational)
    (thresholdCertificate :
      Dirichlet.Window.IndexOne.Optimal.IsGapThreshold threshold)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    threshold ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.IndexOne.Bounds.gapThreshold_le_of_linearCombinationObstructions threshold
    thresholdCertificate
    (Dirichlet.Window.Basic.errorRatio source.value lower upper)
    (Dirichlet.Window.Basic.denominatorRatio lower upper)
    (IndexTwo.Bounds.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.normalizedLinearCombinationExterior
      consecutive)

/-- At determinant index two, the centered obstruction chamber has normalized
gap at least `205/128`. -/
theorem AreConsecutiveBest.dyadicCenteredGapThreshold_le_normalizedDeterminantGap_of_indexTwo
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    IndexTwo.Bounds.dyadicCenteredGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.IndexOne.Bounds.dyadicCenteredGapThreshold_le_of_centeredUnitObstructions
    (Dirichlet.Window.Basic.errorRatio source.value lower upper)
    (Dirichlet.Window.Basic.denominatorRatio lower upper)
    (IndexTwo.Bounds.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (IndexTwo.Bounds.AreConsecutiveBest.normalizedCenteredUnitObstruction
      consecutive indexTwo)

/-- At determinant index two, every rational point of the exact centered cut
gives twice the corresponding index-one normalized gap. -/
theorem AreConsecutiveBest.twice_gapThreshold_le_normalizedDeterminantGap_of_indexTwo
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (gap : Fraction.Rational)
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    2 * gap ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.IndexOne.Bounds.twice_gapThreshold_le_of_centeredUnitObstructions gap certificate
    (Dirichlet.Window.Basic.errorRatio source.value lower upper)
    (Dirichlet.Window.Basic.denominatorRatio lower upper)
    (IndexTwo.Bounds.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (IndexTwo.Bounds.AreConsecutiveBest.normalizedCenteredUnitObstruction
      consecutive indexTwo)

/-- Consecutive best pairs have normalized determinant gap at least `1/2`. -/
theorem AreConsecutiveBest.half_le_normalizedDeterminantGap
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    (1 / 2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact (show (1 / 2 : Fraction.Rational) ≤ 15 / 28 by decide).trans
    (Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.fifteen_twenty_eighths_le_normalizedDeterminantGap
      consecutive)

/-- At determinant index one, the `15/28` gap certificate and the exact
window-times-gap identity give the rational window bound `28/15`. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_twentyEight_fifteenths_of_indexOne
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 1) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ 28 / 15 := by
  have scaledWindow :=
    Dirichlet.Window.Basic.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive (15 / 28 : Fraction.Rational)
        (Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.fifteen_twenty_eighths_le_normalizedDeterminantGap
          consecutive)
  rw [indexOne, Nat.cast_one] at scaledWindow
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scaledWindow
      (Fraction.Order.Field.div_nonneg_direct
        (numerator := (28 : Fraction.Rational)) (denominator := (15 : Fraction.Rational))
        (Fraction.Cast.Order.natCast_pos_direct (by decide)).le
        (Fraction.Cast.Order.natCast_pos_direct (by decide)).le)
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
          source.value lower upper =
        ((15 / 28 : Fraction.Rational) *
          Dirichlet.Window.SourceBound.dirichletWindowQuadrance
            source.value lower upper) * (28 / 15) := by
      have factorsCancel : (15 / 28 : Fraction.Rational) * (28 / 15) = 1 := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        calc
          ((15 : Fraction.Rational) * (28 : Fraction.Rational)⁻¹) *
                ((28 : Fraction.Rational) * (15 : Fraction.Rational)⁻¹) =
              ((15 : Fraction.Rational) * (15 : Fraction.Rational)⁻¹) *
                ((28 : Fraction.Rational)⁻¹ * (28 : Fraction.Rational)) := by ring1
          _ = 1 * 1 := by
            rw [Fraction.Field.mul_inv_cancel (15 : Fraction.Rational)
                (Fraction.Cast.Order.natCast_pos_direct
                  (show 0 < 15 by decide)).ne',
              Fraction.Field.inv_mul_cancel (28 : Fraction.Rational)
                (Fraction.Cast.Order.natCast_pos_direct
                  (show 0 < 28 by decide)).ne']
          _ = 1 := by ring1
      calc
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance
              source.value lower upper =
            1 * Dirichlet.Window.SourceBound.dirichletWindowQuadrance
              source.value lower upper := by ring1
        _ = ((15 / 28 : Fraction.Rational) * (28 / 15)) *
            Dirichlet.Window.SourceBound.dirichletWindowQuadrance
              source.value lower upper := by rw [factorsCancel]
        _ = ((15 / 28 : Fraction.Rational) *
            Dirichlet.Window.SourceBound.dirichletWindowQuadrance
              source.value lower upper) * (28 / 15) := by ring1
    _ ≤ (1 : Fraction.Rational) * (28 / 15) := scaled
    _ = 28 / 15 := by ring1

/-- At determinant index one, the norm-two leading coefficient certificate
and the exact window-times-gap identity give the displayed rational bound
`112/71`.  The proof only multiplies by the positive gap threshold. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoIndexOneWindowBound_of_indexOne
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 1) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound := by
  have scaledWindow :=
    Dirichlet.Window.Basic.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold
        (Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.normTwoIndexOneGapThreshold_le_normalizedDeterminantGap
          consecutive)
  rw [indexOne, Nat.cast_one] at scaledWindow
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold)
  · calc
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance
            source.value lower upper * Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold =
          Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold *
            Dirichlet.Window.SourceBound.dirichletWindowQuadrance
              source.value lower upper := by ring1
      _ ≤ 1 := scaledWindow
      _ = Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound *
          Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold :=
        Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_mul_gapThreshold.symm
  · exact Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold_pos

/-- At determinant index one, every rational point of the exact gap cut gives
the division-free optimal-window family `threshold * window ≤ 1`.  Choosing
rational thresholds arbitrarily close to the cut recovers the optimal upper
constant without constructing its algebraic endpoint. -/
theorem AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one_of_indexOne
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (threshold : Fraction.Rational)
    (thresholdCertificate :
      Dirichlet.Window.IndexOne.Optimal.IsGapThreshold threshold)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 1) :
    threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ 1 := by
  have scaledWindow :=
    Dirichlet.Window.Basic.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive threshold
        (Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.gapThreshold_le_normalizedDeterminantGap
          threshold thresholdCertificate consecutive)
  rw [indexOne, Nat.cast_one] at scaledWindow
  exact scaledWindow

/-- At determinant index two, every rational point of the exact centered cut
gives the same division-free window family as at index one. -/
theorem AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one_of_indexTwo
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (gap : Fraction.Rational)
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    gap * Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ 1 := by
  have scaledWindow :=
    Dirichlet.Window.Basic.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive (2 * gap)
        (Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.twice_gapThreshold_le_normalizedDeterminantGap_of_indexTwo
          gap certificate consecutive indexTwo)
  rw [indexTwo, Nat.cast_ofNat] at scaledWindow
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      (gap * Dirichlet.Window.SourceBound.dirichletWindowQuadrance
          source.value lower upper) * 2 =
          (2 * gap) * Dirichlet.Window.SourceBound.dirichletWindowQuadrance
            source.value lower upper := by ring1
      _ ≤ 2 := scaledWindow
      _ = 1 * 2 := by ring1
  · decide

/-- Every consecutive displayed window satisfies the exact root-free
quadratic family `gap * window ≤ 1`.  Rational cuts in this family approach
Chevallier's optimal squared constant without naming its algebraic endpoint. -/
theorem AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (gap : Fraction.Rational)
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    gap * Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ 1 := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two consecutive) with
      indexOne | indexTwo
  · exact Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one_of_indexOne gap
      certificate.2 consecutive indexOne
  · exact Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one_of_indexTwo gap
      certificate
      consecutive indexTwo

/-- At determinant index one, the dyadic five-obstruction chamber and the
exact window-times-gap identity give the stronger rational bound `256/205`.
This approaches the optimal algebraic constant without naming its square
root. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_sharpIndexOneWindowBound_of_indexOne
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 1) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound := by
  have scaledWindow :=
    Dirichlet.Window.Basic.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound
        (Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.sharpIndexOneGapBound_le_normalizedDeterminantGap
          consecutive)
  rw [indexOne, Nat.cast_one] at scaledWindow
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound)
  · calc
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance
            source.value lower upper * Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound =
          Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound *
            Dirichlet.Window.SourceBound.dirichletWindowQuadrance
              source.value lower upper := by ring1
      _ ≤ 1 := scaledWindow
      _ = Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound *
        Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound :=
        Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound_mul_gapBound.symm
  · exact Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound_pos

/-- At determinant index two, the strengthened centered gap and the exact
index-two factor give the matching squared-window bound `256/205`. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_dyadicCenteredWindowBound_of_indexTwo
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      IndexTwo.Bounds.dyadicCenteredWindowBound := by
  have scaledWindow :=
    Dirichlet.Window.Basic.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive IndexTwo.Bounds.dyadicCenteredGapThreshold

          (AreConsecutiveBest.dyadicCenteredGapThreshold_le_normalizedDeterminantGap_of_indexTwo
          consecutive indexTwo)
  rw [indexTwo, Nat.cast_ofNat] at scaledWindow
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := IndexTwo.Bounds.dyadicCenteredGapThreshold)
  · calc
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper *
            IndexTwo.Bounds.dyadicCenteredGapThreshold =
          IndexTwo.Bounds.dyadicCenteredGapThreshold *
            Dirichlet.Window.SourceBound.dirichletWindowQuadrance
              source.value lower upper := by ring1
      _ ≤ 2 := scaledWindow
      _ = IndexTwo.Bounds.dyadicCenteredWindowBound *
          IndexTwo.Bounds.dyadicCenteredGapThreshold :=
        IndexTwo.Bounds.dyadicCenteredWindowBound_mul_gapThreshold.symm
  · exact IndexTwo.Bounds.dyadicCenteredGapThreshold_pos

/-- At determinant index one, the rational `28/15` bound in particular
recovers the earlier integer bound two. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_two_of_indexOne
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 1) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ 2 :=

    (AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoIndexOneWindowBound_of_indexOne
      consecutive indexOne).trans Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_le_two

/-- Every consecutive squared Dirichlet window is at most `256/205`.  The
five-obstruction octant chamber supplies this value at index one, and the
oriented centered chamber supplies the same value at index two. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two consecutive) with
      indexOne | indexTwo
  · exact

        AreConsecutiveBest.dirichletWindowQuadrance_le_sharpIndexOneWindowBound_of_indexOne
        consecutive indexOne
  · calc
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance
            source.value lower upper ≤
          IndexTwo.Bounds.dyadicCenteredWindowBound :=

          AreConsecutiveBest.dirichletWindowQuadrance_le_dyadicCenteredWindowBound_of_indexTwo
          consecutive indexTwo
      _ = Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound :=
        Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound_eq_dyadicCenteredWindowBound.symm

/-- Every consecutive squared Dirichlet window is at most the displayed
`112/71`.  The norm-two leading coefficient test gives this value at index
one, and the centered-coset certificates give the same value at index two. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two consecutive) with
      indexOne | indexTwo
  · exact

        AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoIndexOneWindowBound_of_indexOne
        consecutive indexOne
  · calc
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance
            source.value lower upper ≤
          IndexTwo.Bounds.centeredWindowBound :=

          IndexTwo.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
          consecutive indexTwo
      _ = Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound :=
        Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_eq_centeredIndexTwoWindowBound.symm

/-- Every consecutive squared Dirichlet window is at most `28/15`: this is
the index-one finite-octant bound, while the centered index-two bound
`112/71` is strictly smaller. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_twentyEight_fifteenths
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ 28 / 15 := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two consecutive) with
      indexOne | indexTwo
  · exact
      Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_twentyEight_fifteenths_of_indexOne
        consecutive indexOne
  · exact

        (IndexTwo.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
        consecutive indexTwo).trans (by
          rw [← Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_eq_centeredIndexTwoWindowBound]
          exact Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_le_twentyEight_fifteenths)

/-- Every consecutive squared Dirichlet window is at most two.

The bound follows from the stronger rational estimate `112/71` for the same retained pair. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_two
    {source : GaussianInt.Fraction}
    {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      source.value lower upper ≤ 2 :=
  (Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
    consecutive).trans
    Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_le_two

end Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Bounds

end
