module
import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Hermitian
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib
open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Hermitian

open Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

public section

/-!
# Choice-free projective quadrance over constructive Gaussian fractions

This is the finite projective geometry used by the constructive CCL layer.  It
is deliberately separate from `Purelib.CCL.Geometry.Chordal`, whose coordinates are Mathlib's
`Rat`.  Every coordinate here is an explicit quotient of an integer numerator
and a positive integer denominator.
-/

namespace Purelib.Geometry.Projective.Chordal.Matrix

namespace Mat2

/-- Exact squared chordal quadrance between the affine image and the first-column image.

Its numerator is the matrix determinant squared norm; its denominator is the product of the two displayed homogeneous
weights. -/
theorem chordalSq_truncation (M : GaussianMatrix) (t : Gaussian.Basic.Canonical) :
    Chordal.Basic.chordalSq (Line.Matrix.act M (Proj.affine t))
        (Line.Matrix.act M Proj.omega) =
      Data.Gaussian.Norm.Basic.normSq (Matrix2.determinant M) /
        ((Data.Gaussian.Norm.Basic.normSq M.a + Data.Gaussian.Norm.Basic.normSq M.c) *
          (Data.Gaussian.Norm.Basic.normSq (M.a * t + M.b) + Data.Gaussian.Norm.Basic.normSq (M.c * t + M.d)))
            := by
  have numerator :
      (M.a * t + M.b) * M.c - M.a * (M.c * t + M.d) = -(Matrix2.determinant M) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
        Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Matrix2.determinant] <;>
      ring1
  simp only [Chordal.Basic.chordalSq, Line.Matrix.act, Proj.affine, Proj.omega,
    Gaussian.Basic.mul_one, Gaussian.Basic.mul_zero, Gaussian.Basic.add_zero, numerator, Gaussian.Norm.Basic.normSq_neg]
  congr 1
  ring1

/-- Exact determinant scaling between two affine inputs under one matrix.

The retained affine coordinates yield their original alternating numerator. Its exact determinant factor is transported
through squared norm while both matrix-image weights remain unchanged. -/
theorem chordalSq_act_affine (M : GaussianMatrix) (left right : Gaussian.Basic.Canonical) :
    Chordal.Basic.chordalSq (Line.Matrix.act M (Proj.affine left))
        (Line.Matrix.act M (Proj.affine right)) =
      Data.Gaussian.Norm.Basic.normSq (Matrix2.determinant M) * Data.Gaussian.Norm.Basic.normSq (left - right) /
        (Proj.weight (Line.Matrix.act M (Proj.affine left)) *
          Proj.weight (Line.Matrix.act M (Proj.affine right))) := by
  have crossIdentity :
      (M.a * left + M.b) * (M.c * right + M.d) -
          (M.a * right + M.b) * (M.c * left + M.d) =
        (Matrix2.determinant M) * (left - right) := by
    apply Gaussian.Basic.ext <;>
      simp only [Matrix2.determinant, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
      ring1
  rw [Chordal.Basic.chordalSq_eq_cross]
  dsimp only [Proj.cross, Line.Matrix.act, Proj.affine]
  rewrite [Gaussian.Basic.mul_one, Gaussian.Basic.mul_one, crossIdentity,
    Gaussian.Norm.Basic.normSq_mul]
  rfl

/-- Exact determinant scaling of the homogeneous cross numerator. -/
theorem cross_act (M : GaussianMatrix) (left right : GaussianLine) :
    Proj.cross (Line.Matrix.act M left) (Line.Matrix.act M right) =
      (Matrix2.determinant M) * Proj.cross left right := by
  apply Gaussian.Basic.ext <;>
    simp only [Proj.cross, Line.Matrix.act, Matrix2.determinant, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
    ring1

/-- Exact projective two-point transport under an arbitrary displayed matrix. -/
theorem chordalSq_act (M : GaussianMatrix) (left right : GaussianLine) :
    Chordal.Basic.chordalSq (Line.Matrix.act M left) (Line.Matrix.act M right) =
      Data.Gaussian.Norm.Basic.normSq (Matrix2.determinant M) * Data.Gaussian.Norm.Basic.normSq (Proj.cross left
        right) /
        (Proj.weight (Line.Matrix.act M left) *
          Proj.weight (Line.Matrix.act M right)) := by
  rw [Chordal.Basic.chordalSq_eq_cross, Mat2.cross_act, Gaussian.Norm.Basic.normSq_mul]

end Mat2

/-- A strictly positive coarse coefficient controlling the homogeneous weight under one displayed matrix action. -/
@[expose] def Mat2.actionWeightCoefficient (matrix : GaussianMatrix) : Fraction.Rational :=
  2 * (Data.Gaussian.Norm.Basic.normSq matrix.a + Data.Gaussian.Norm.Basic.normSq matrix.b +
    Data.Gaussian.Norm.Basic.normSq matrix.c +
    Data.Gaussian.Norm.Basic.normSq matrix.d + 1)

/-- The computed coefficient bounding matrix-action weight is strictly positive.

Every retained matrix coordinate contributes a nonnegative squared norm. The original added unit makes their sum
strictly positive before multiplication by the positive factor two. -/
theorem Mat2.actionWeightCoefficient_pos (matrix : GaussianMatrix) :
    0 < (Mat2.actionWeightCoefficient matrix) := by
  apply Fraction.Order.Arithmetic.mul_pos_direct (by decide)
  exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (add_nonneg
      (add_nonneg
        (add_nonneg (Gaussian.Norm.Basic.normSq_nonneg matrix.a) (Gaussian.Norm.Basic.normSq_nonneg matrix.b))
        (Gaussian.Norm.Basic.normSq_nonneg matrix.c))
      (Gaussian.Norm.Basic.normSq_nonneg matrix.d))
    (by decide)

/-- Coefficient-only upper bound for homogeneous projective weight under a matrix action.

The original matrix and homogeneous point determine both sides. The missing cross-coordinate products are nonnegative,
so exact scalar expansion bounds the output weight by the retained coefficient sum. -/
theorem Mat2.act_weight_le (matrix : GaussianMatrix) (point : GaussianLine)
  :
    Proj.weight (Line.Matrix.act matrix point) ≤
      (Mat2.actionWeightCoefficient matrix) * (Proj.weight point) := by
  let coefficientSum := Data.Gaussian.Norm.Basic.normSq matrix.a + Data.Gaussian.Norm.Basic.normSq matrix.b +
    Data.Gaussian.Norm.Basic.normSq matrix.c + Data.Gaussian.Norm.Basic.normSq matrix.d
  let productSum :=
    Data.Gaussian.Norm.Basic.normSq matrix.a * Data.Gaussian.Norm.Basic.normSq point.p +
      Data.Gaussian.Norm.Basic.normSq matrix.b * Data.Gaussian.Norm.Basic.normSq point.q +
      Data.Gaussian.Norm.Basic.normSq matrix.c * Data.Gaussian.Norm.Basic.normSq point.p +
      Data.Gaussian.Norm.Basic.normSq matrix.d * Data.Gaussian.Norm.Basic.normSq point.q
  have numeratorBound :
      Data.Gaussian.Norm.Basic.normSq (matrix.a * point.p + matrix.b * point.q) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq matrix.a * Data.Gaussian.Norm.Basic.normSq point.p +
          Data.Gaussian.Norm.Basic.normSq matrix.b * Data.Gaussian.Norm.Basic.normSq point.q) := by
    simpa only [Gaussian.Norm.Basic.normSq_mul] using
      Gaussian.Norm.Bounds.normSq_add_le_two (matrix.a * point.p) (matrix.b * point.q)
  have denominatorBound :
      Data.Gaussian.Norm.Basic.normSq (matrix.c * point.p + matrix.d * point.q) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq matrix.c * Data.Gaussian.Norm.Basic.normSq point.p +
          Data.Gaussian.Norm.Basic.normSq matrix.d * Data.Gaussian.Norm.Basic.normSq point.q) := by
    simpa only [Gaussian.Norm.Basic.normSq_mul] using
      Gaussian.Norm.Bounds.normSq_add_le_two (matrix.c * point.p) (matrix.d * point.q)
  have productBound : productSum ≤ coefficientSum * (Proj.weight point) := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    have missingNonnegative : 0 ≤
        Data.Gaussian.Norm.Basic.normSq matrix.a * Data.Gaussian.Norm.Basic.normSq point.q +
          Data.Gaussian.Norm.Basic.normSq matrix.b * Data.Gaussian.Norm.Basic.normSq point.p +
          Data.Gaussian.Norm.Basic.normSq matrix.c * Data.Gaussian.Norm.Basic.normSq point.q +
          Data.Gaussian.Norm.Basic.normSq matrix.d * Data.Gaussian.Norm.Basic.normSq point.p :=
      add_nonneg
        (add_nonneg
          (add_nonneg
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              (Gaussian.Norm.Basic.normSq_nonneg matrix.a) (Gaussian.Norm.Basic.normSq_nonneg point.q))
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              (Gaussian.Norm.Basic.normSq_nonneg matrix.b) (Gaussian.Norm.Basic.normSq_nonneg point.p)))
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            (Gaussian.Norm.Basic.normSq_nonneg matrix.c) (Gaussian.Norm.Basic.normSq_nonneg point.q)))
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Gaussian.Norm.Basic.normSq_nonneg matrix.d) (Gaussian.Norm.Basic.normSq_nonneg point.p))
    calc
      0 ≤ Data.Gaussian.Norm.Basic.normSq matrix.a * Data.Gaussian.Norm.Basic.normSq point.q +
          Data.Gaussian.Norm.Basic.normSq matrix.b * Data.Gaussian.Norm.Basic.normSq point.p +
          Data.Gaussian.Norm.Basic.normSq matrix.c * Data.Gaussian.Norm.Basic.normSq point.q +
          Data.Gaussian.Norm.Basic.normSq matrix.d * Data.Gaussian.Norm.Basic.normSq point.p :=
            missingNonnegative
      _ = coefficientSum * (Proj.weight point) - productSum := by
        simp only [coefficientSum, productSum, Proj.weight]
        ring1
  have coefficientSumNonnegative : 0 ≤ coefficientSum :=
    add_nonneg
      (add_nonneg
        (add_nonneg (Gaussian.Norm.Basic.normSq_nonneg matrix.a) (Gaussian.Norm.Basic.normSq_nonneg matrix.b))
        (Gaussian.Norm.Basic.normSq_nonneg matrix.c))
      (Gaussian.Norm.Basic.normSq_nonneg matrix.d)
  have weightNonnegative := (Proj.weight_nonneg point)
  calc
    Proj.weight (Line.Matrix.act matrix point) =
        Data.Gaussian.Norm.Basic.normSq (matrix.a * point.p + matrix.b * point.q) +
          Data.Gaussian.Norm.Basic.normSq (matrix.c * point.p + matrix.d * point.q) := rfl
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq matrix.a * Data.Gaussian.Norm.Basic.normSq point.p +
          Data.Gaussian.Norm.Basic.normSq matrix.b * Data.Gaussian.Norm.Basic.normSq point.q) +
        2 * (Data.Gaussian.Norm.Basic.normSq matrix.c * Data.Gaussian.Norm.Basic.normSq point.p +
          Data.Gaussian.Norm.Basic.normSq matrix.d * Data.Gaussian.Norm.Basic.normSq point.q) :=
      add_le_add numeratorBound denominatorBound
    _ = 2 * productSum := by
      simp only [productSum]
      ring1
    _ ≤ 2 * (coefficientSum * (Proj.weight point)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productBound
        (by decide)
    _ ≤ 2 * ((coefficientSum + 1) * (Proj.weight point)) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      · apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        · exact le_add_of_nonneg_right (show (0 : Fraction.Rational) ≤ 1 by decide)
        · exact weightNonnegative
      · decide
    _ = (Mat2.actionWeightCoefficient matrix) * (Proj.weight point) := by
      simp only [Mat2.actionWeightCoefficient, coefficientSum]
      ring1
end Purelib.Geometry.Projective.Chordal.Matrix
