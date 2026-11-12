module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Matrix
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Hermitian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal.Matrix

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Hermitian

open Purelib.Geometry.Projective.Line.Matrix

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Productive unary padding at a projective CCL terminal

An arithmetic transducer cannot in general decide that opaque nonterminating
inputs have combined to an exact Gaussian rational.  The canonical finite
encoder remains unchanged.  This module supplies a separate projective
continuation convention: after a completed sector, an unresolved zero
residual may remain at `omega`, and every further unary `1` fixes that formal
coordinate while strengthening the finite large-tail predicate.
-/

namespace Purelib.Geometry.Projective.Chordal.Transport

/-! ## Transport of the unary estimate through a finite decoder -/

/-- A matrix action followed by its adjugate action scales both homogeneous coordinates by the determinant. -/
private theorem adjugate_act_act (matrix :
  GaussianMatrix) (point : GaussianLine) :
    Line.Matrix.act (BoundaryAdjugate.adjugate matrix)
        (Line.Matrix.act matrix point) =
      Proj.scale
        (BoundaryAdjugate.determinant matrix) point := by
  apply Proj.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [Line.Matrix.act, BoundaryAdjugate.adjugate,
        BoundaryAdjugate.determinant,
        Matrix2.determinant,
        Proj.scale,
        Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
          Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im] <;>
      ring1

/-- Applying an invertible displayed decoder cannot reduce projective weight below this explicit adjugate-coefficient
estimate. -/
theorem determinant_mul_weight_le_act_weight
    (matrix : GaussianMatrix) (point : GaussianLine) :
    Basic.normSq (BoundaryAdjugate.determinant matrix) *
        Proj.weight point ≤
      Mat2.actionWeightCoefficient
          (BoundaryAdjugate.adjugate matrix) *
        Proj.weight (Line.Matrix.act matrix point) := by
  let inverse := BoundaryAdjugate.adjugate matrix
  let image := Line.Matrix.act matrix point
  have upper := Mat2.act_weight_le inverse image
  calc
    Basic.normSq (BoundaryAdjugate.determinant matrix) *
        Proj.weight point =
        Proj.weight
          (Proj.scale
            (BoundaryAdjugate.determinant matrix) point) :=
      (Proj.weight_scale _ _).symm
    _ = Proj.weight
        (Line.Matrix.act inverse image) := by
      rw [adjugate_act_act]
    _ ≤ Mat2.actionWeightCoefficient inverse *
        Proj.weight image := upper

/-- A finite condition-number coefficient for transporting arbitrary projective two-point error through one invertible
displayed decoder. -/
def transportCoefficient (matrix :
  GaussianMatrix) : Fraction.Rational :=
  let coefficient :=
    Mat2.actionWeightCoefficient
      (BoundaryAdjugate.adjugate matrix)
  coefficient ^ 2 /
    Basic.normSq (BoundaryAdjugate.determinant matrix)

/-- A nonzero matrix determinant makes the squared-chordal transport coefficient positive. -/
theorem transportCoefficient_pos (matrix :
  GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0) :
    0 < transportCoefficient matrix := by
  exact Field.div_pos_direct
    (Arithmetic.pow_pos_direct
      (Mat2.actionWeightCoefficient_pos
        (BoundaryAdjugate.adjugate matrix)) 2)
    (Basic.normSq_pos determinantNonzero)

/-- Any one finite invertible decoder can enlarge squared-chordal error by at most its displayed rational condition
coefficient. This is the accounting needed before later half-contracting blocks make up for one annulus-free initial
arithmetic digit. -/
theorem chordalSq_act_le_transportCoefficient
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (left right : GaussianLine)
    (leftValid : Proj.HasNonzeroCoordinate left)
    (rightValid : Proj.HasNonzeroCoordinate right) :
    Basic.chordalSq
        (Line.Matrix.act matrix left) (Line.Matrix.act matrix right) ≤
      transportCoefficient matrix *
        Basic.chordalSq left right := by
  let determinantNorm :=
    Basic.normSq (BoundaryAdjugate.determinant matrix)
  let coefficient :=
    Mat2.actionWeightCoefficient
      (BoundaryAdjugate.adjugate matrix)
  let numerator := Basic.normSq (Proj.cross left right)
  let inputDenominator :=
    Proj.weight left *
      Proj.weight right
  let outputDenominator :=
    Proj.weight (Line.Matrix.act matrix left) *
      Proj.weight (Line.Matrix.act matrix right)
  have determinantPositive : 0 < determinantNorm :=
    Basic.normSq_pos determinantNonzero
  have coefficientPositive : 0 < coefficient :=
    Mat2.actionWeightCoefficient_pos _
  have inputDenominatorPositive : 0 < inputDenominator :=
    Arithmetic.mul_pos_direct
      (Proj.weight_pos leftValid)
      (Proj.weight_pos rightValid)
  have leftImageValid :=
    Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftValid
  have rightImageValid :=
    Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightValid
  have outputDenominatorPositive : 0 < outputDenominator :=
    Arithmetic.mul_pos_direct
      (Proj.weight_pos leftImageValid)
      (Proj.weight_pos rightImageValid)
  have leftWeight := determinant_mul_weight_le_act_weight matrix left
  have rightWeight := determinant_mul_weight_le_act_weight matrix right
  have denominatorOrder :
      determinantNorm ^ 2 * inputDenominator ≤
        coefficient ^ 2 * outputDenominator := by
    have productOrder := Arithmetic.mul_le_mul_direct
      leftWeight rightWeight
      (Arithmetic.mul_nonneg_direct determinantPositive.le
        (Proj.weight_pos rightValid).le)
      (Arithmetic.mul_nonneg_direct coefficientPositive.le
        (Proj.weight_pos leftImageValid).le)
    calc
      determinantNorm ^ 2 * inputDenominator =
          (determinantNorm *
              Proj.weight left) *
            (determinantNorm *
              Proj.weight right) := by
        dsimp only [inputDenominator]
        ring1
      _ ≤ (coefficient * Proj.weight
              (Line.Matrix.act matrix left)) *
            (coefficient * Proj.weight
              (Line.Matrix.act matrix right)) := productOrder
      _ = coefficient ^ 2 * outputDenominator := by
        dsimp only [outputDenominator]
        ring1
  have numeratorNonnegative : 0 ≤ numerator := Basic.normSq_nonneg _
  have denominatorProductPositive :
      0 < determinantNorm * inputDenominator :=
    Arithmetic.mul_pos_direct determinantPositive
      inputDenominatorPositive
  rw [Mat2.chordalSq_act]
  simp only [Basic.chordalSq_eq_cross]
  change determinantNorm * numerator / outputDenominator ≤
    (coefficient ^ 2 / determinantNorm) *
      (numerator / inputDenominator)
  have quotientProduct :
      (coefficient ^ 2 / determinantNorm) *
          (numerator / inputDenominator) =
        (coefficient ^ 2 * numerator) /
          (determinantNorm * inputDenominator) :=
    Fraction.Field.div_mul_div_direct _ _ _ _
  rw [quotientProduct]
  apply (Field.div_le_iff_pos
    outputDenominatorPositive).2
  have rightIdentity :
      ((coefficient ^ 2 * numerator) /
          (determinantNorm * inputDenominator)) * outputDenominator =
        (coefficient ^ 2 * numerator * outputDenominator) /
          (determinantNorm * inputDenominator) := by
    calc
      ((coefficient ^ 2 * numerator) /
          (determinantNorm * inputDenominator)) * outputDenominator =
          ((coefficient ^ 2 * numerator) /
            (determinantNorm * inputDenominator)) *
              (outputDenominator / 1) := by
        congr 1
        calc
          outputDenominator =
              (outputDenominator / 1) * 1 :=
            (Fraction.Field.div_mul_cancel_of_ne
              outputDenominator 1 (by decide)).symm
          _ = outputDenominator / 1 :=
            Fraction.Field.mul_one_direct _
      _ = ((coefficient ^ 2 * numerator) * outputDenominator) /
          ((determinantNorm * inputDenominator) * 1) :=
        Fraction.Field.div_mul_div_direct _ _ _ _
      _ = (coefficient ^ 2 * numerator * outputDenominator) /
          (determinantNorm * inputDenominator) := by
        rw [Fraction.Field.mul_one_direct]
  rw [rightIdentity]
  apply (Field.le_div_iff_pos
    denominatorProductPositive).2
  have scaledOrder :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      denominatorOrder numeratorNonnegative
  calc
    determinantNorm * numerator *
        (determinantNorm * inputDenominator) =
        numerator * (determinantNorm ^ 2 * inputDenominator) := by ring1
    _ ≤ numerator * (coefficient ^ 2 * outputDenominator) := scaledOrder
    _ = coefficient ^ 2 * numerator * outputDenominator := by ring1

/-- Coefficient displayed in the transported no-return bound. -/
def terminalCoefficient (matrix :
  GaussianMatrix) : Fraction.Rational :=
  Mat2.actionWeightCoefficient
      (BoundaryAdjugate.adjugate matrix) /
    Proj.weight
      (Line.Matrix.act matrix Proj.omega)

/-- An invertible matrix has a strictly positive terminal transport coefficient. -/
theorem terminalCoefficient_pos (matrix :
  GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0) :
    0 < terminalCoefficient matrix := by
  have imageValid := Gaussian.Mat2.act_hasNonzeroCoordinate
    determinantNonzero Proj.omega_hasNonzeroCoordinate
  exact Field.div_pos_direct
    (Mat2.actionWeightCoefficient_pos
      (BoundaryAdjugate.adjugate matrix))
    (Proj.weight_pos imageValid)

/-- A large affine tail remains close to the decoder's terminal coordinate. The constant depends only on the already
displayed finite decoder matrix.

The displayed coefficient uses the retained decoder matrix and its adjugate. Its bound applies to the same affine tail
and terminal projective coordinate. -/
theorem chordalSq_act_affine_omega_le
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (tail : Data.Gaussian.Basic.Canonical) :
    Basic.chordalSq
        (Line.Matrix.act matrix (Proj.affine tail))
        (Line.Matrix.act matrix Proj.omega) ≤
      terminalCoefficient matrix / (1 + Basic.normSq
        tail) := by
  let determinantNorm :=
    Basic.normSq (BoundaryAdjugate.determinant matrix)
  let coefficient :=
    Mat2.actionWeightCoefficient
      (BoundaryAdjugate.adjugate matrix)
  let omegaWeight := Proj.weight
    (Line.Matrix.act matrix Proj.omega)
  let affineWeight :=
    Proj.weight
      (Line.Matrix.act matrix (Proj.affine tail))
  let tailWeight := 1 + Basic.normSq tail
  have determinantPositive : 0 < determinantNorm :=
    Basic.normSq_pos determinantNonzero
  have coefficientPositive : 0 < coefficient :=
    Mat2.actionWeightCoefficient_pos _
  have omegaValid := Gaussian.Mat2.act_hasNonzeroCoordinate
    determinantNonzero Proj.omega_hasNonzeroCoordinate
  have affineValid := Gaussian.Mat2.act_hasNonzeroCoordinate
    determinantNonzero (Proj.affine_hasNonzeroCoordinate tail)
  have omegaPositive : 0 < omegaWeight :=
    Proj.weight_pos omegaValid
  have affinePositive : 0 < affineWeight :=
    Proj.weight_pos affineValid
  have tailPositive : 0 < tailWeight :=
    add_pos_of_pos_of_nonneg (by decide) (Basic.normSq_nonneg tail)
  have affineLower : determinantNorm * tailWeight ≤
      coefficient * affineWeight := by
    have lower := determinant_mul_weight_le_act_weight matrix
      (Proj.affine tail)
    simpa only [determinantNorm, coefficient, affineWeight, tailWeight,
      Proj.weight, Proj.affine, Basic.normSq_one,
      Fraction.Field.add_comm] using lower
  have denominatorOrder :
      omegaWeight * (determinantNorm * tailWeight) ≤
        coefficient * (omegaWeight * affineWeight) := by
    calc
      omegaWeight * (determinantNorm * tailWeight) ≤
          omegaWeight * (coefficient * affineWeight) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          affineLower omegaPositive.le
      _ = coefficient * (omegaWeight * affineWeight) := by ring1
  have smallDenominatorPositive :
      0 < omegaWeight * (determinantNorm * tailWeight) :=
    Arithmetic.mul_pos_direct omegaPositive
      (Arithmetic.mul_pos_direct determinantPositive
        tailPositive)
  have numeratorNonnegative : 0 ≤ coefficient * determinantNorm :=
    Arithmetic.mul_nonneg_direct coefficientPositive.le
      determinantPositive.le
  rw [Mat2.chordalSq_truncation]
  rw [show Basic.normSq (Matrix2.determinant matrix) =
      determinantNorm by rfl]
  rw [show Basic.normSq matrix.a + Basic.normSq matrix.c =
    omegaWeight by
    dsimp only [omegaWeight]
    simp only [Proj.weight, Line.Matrix.act,
      Proj.omega, Data.Gaussian.Basic.mul_one,
      Data.Gaussian.Basic.mul_zero,
      Data.Gaussian.Basic.add_zero, -eq_self, -iff_self]
    rfl]
  rw [show
      Basic.normSq (matrix.a * tail + matrix.b) +
          Basic.normSq (matrix.c * tail + matrix.d) = affineWeight by
    dsimp only [affineWeight, Proj.weight,
      Line.Matrix.act, Proj.affine]
    simp only [Data.Gaussian.Basic.mul_one, -eq_self, -iff_self]
    rfl]
  change determinantNorm / (omegaWeight * affineWeight) ≤
    (coefficient / omegaWeight) / tailWeight
  calc
    determinantNorm / (omegaWeight * affineWeight) =
        (coefficient * determinantNorm) /
          (coefficient * (omegaWeight * affineWeight)) := by
      exact (Fraction.Field.mul_div_mul_left_direct
        coefficient determinantNorm (omegaWeight * affineWeight)
        coefficientPositive.ne').symm
    _ ≤ (coefficient * determinantNorm) /
        (omegaWeight * (determinantNorm * tailWeight)) :=
      Field.div_le_div_of_nonneg_left_direct
        numeratorNonnegative smallDenominatorPositive denominatorOrder
    _ = coefficient / (omegaWeight * tailWeight) := by
      rw [show coefficient * determinantNorm =
          determinantNorm * coefficient by ring1,
        show omegaWeight * (determinantNorm * tailWeight) =
          determinantNorm * (omegaWeight * tailWeight) by ring1]
      exact Fraction.Field.mul_div_mul_left_direct
        determinantNorm coefficient (omegaWeight * tailWeight)
        determinantPositive.ne'
    _ = (coefficient / omegaWeight) / tailWeight := by
      change coefficient / (omegaWeight * tailWeight) =
        (coefficient / omegaWeight) * tailWeight⁻¹
      calc
        coefficient / (omegaWeight * tailWeight) =
            (coefficient * 1) / (omegaWeight * tailWeight) := by
          rw [Fraction.Field.mul_one_direct]
        _ = (coefficient / omegaWeight) * (1 / tailWeight) :=
          (Fraction.Field.div_mul_div_direct
            coefficient omegaWeight 1 tailWeight).symm
        _ = (coefficient / omegaWeight) * tailWeight⁻¹ := by
          have oneDiv : (1 : Fraction.Rational) / tailWeight = tailWeight⁻¹ := by
            rw [Algebra.Field.ExplicitField.div_eq_mul_inv]
            exact Fraction.Field.one_mul _
          rw [oneDiv]
end Purelib.Geometry.Projective.Chordal.Transport

end
