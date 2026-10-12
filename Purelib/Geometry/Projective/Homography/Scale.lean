module
public import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
/-!
# Choice-free completed-block chordal contraction

This file proves the affine two-tail part of the companion paper's completed
CCL block contraction.  The proof is entirely cross-multiplied over explicit
fractions; no square root, limit, supremum, or inherited ordered-field
division theorem is used.
-/

@[expose] public section

namespace Purelib.Geometry.Projective.Homography.Scale

/-- Multiply every entry of a decoder matrix by one Gaussian scalar. -/
def scaleMatrix (scalar : Data.Gaussian.Basic.Canonical) (matrix :
  GaussianMatrix) : GaussianMatrix :=
  ⟨scalar * matrix.a, scalar * matrix.b,
    scalar * matrix.c, scalar * matrix.d⟩

/-- Scaling all matrix entries scales both coordinates of its homogeneous action. -/
theorem act_scaleMatrix (scalar : Data.Gaussian.Basic.Canonical)
  (matrix : GaussianMatrix) (point : GaussianLine) :
    Line.Matrix.act (scaleMatrix scalar matrix) point =
      Proj.scale scalar (Line.Matrix.act matrix point) := by
  apply Proj.ext <;> apply Data.Gaussian.Basic.ext <;>
    simp only [Line.Matrix.act, scaleMatrix, Proj.scale,
      Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;>
    ring1
end Purelib.Geometry.Projective.Homography.Scale

end

end

section
@[expose] public section

/-!
# Constructive invariance under decoder scale folds

Right multiplication by `S_λ` moves a nonzero scale from an affine tail into
the first decoder column.  These finite identities are the formal content of
the scale- and quarter-unit-fold invariance used by the CCL parser.
-/

namespace Purelib.Geometry.Projective.Homography.Scale

/-- Move one displayed tail scale into the first matrix column. -/
def rightScale (matrix : GaussianMatrix) (scale
  : Data.Gaussian.Basic.Canonical) : GaussianMatrix :=
  Coordinates2.Matrix.mul matrix (Line.Matrix.scale scale)

/-- The affine denominator weight `D_M(t)` from the manuscript. -/
def denominatorWeight (matrix : GaussianMatrix)
  (tail : Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (matrix.a * tail + matrix.b) +
    Data.Gaussian.Norm.Basic.normSq (matrix.c * tail + matrix.d)

/-- Right scaling multiplies the upper-left matrix entry by the scale.

The original right product keeps the first-column scale and the zero off-diagonal entry of the retained scale matrix. -/
@[simp] theorem rightScale_a (matrix :
  GaussianMatrix) (scale : Data.Gaussian.Basic.Canonical) :
    (rightScale matrix scale).a = matrix.a * scale := by
  simp only [rightScale, Coordinates2.Matrix.mul,
    Line.Matrix.scale, Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.add_zero, -eq_self, -iff_self]
  rfl

/-- Right scaling preserves the upper-right matrix entry.

The original right product uses the zero upper-right entry and unit lower-right entry of the retained scale matrix. -/
@[simp] theorem rightScale_b (matrix :
  GaussianMatrix) (scale : Data.Gaussian.Basic.Canonical) :
    (rightScale matrix scale).b = matrix.b := by
  simp only [rightScale, Coordinates2.Matrix.mul,
    Line.Matrix.scale, Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.mul_one, Data.Gaussian.Basic.zero_add,
      -eq_self, -iff_self]
  rfl

/-- Right scaling multiplies the lower-left matrix entry by the scale.

The original right product keeps the first-column scale and the zero off-diagonal entry of the retained scale matrix. -/
@[simp] theorem rightScale_c (matrix :
  GaussianMatrix) (scale : Data.Gaussian.Basic.Canonical) :
    (rightScale matrix scale).c = matrix.c * scale := by
  simp only [rightScale, Coordinates2.Matrix.mul,
    Line.Matrix.scale, Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.add_zero, -eq_self, -iff_self]
  rfl

/-- Right scaling preserves the lower-right matrix entry.

The original right product uses the zero upper-right entry and unit lower-right entry of the retained scale matrix. -/
@[simp] theorem rightScale_d (matrix :
  GaussianMatrix) (scale : Data.Gaussian.Basic.Canonical) :
    (rightScale matrix scale).d = matrix.d := by
  simp only [rightScale, Coordinates2.Matrix.mul,
    Line.Matrix.scale, Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.mul_one, Data.Gaussian.Basic.zero_add,
      -eq_self, -iff_self]
  rfl

/-- Folding the scale preserves the displayed affine output exactly. -/
theorem act_affine (matrix : GaussianMatrix)
  (scale tail : Data.Gaussian.Basic.Canonical) :
    Line.Matrix.act (rightScale matrix scale) (Proj.affine tail) =
      Line.Matrix.act matrix (Proj.affine (scale * tail)) := by
  rw [rightScale, Line.Matrix.act_mul, Line.Matrix.scale_action]
  rfl

/-- The two first columns represent the same projective point. -/
theorem act_omega_equivalent (matrix :
  GaussianMatrix) (scale : Data.Gaussian.Basic.Canonical) :
    Proj.Equivalent
      (Line.Matrix.act (rightScale matrix scale) Proj.omega)
      (Line.Matrix.act matrix Proj.omega) := by
  simp only [Proj.Equivalent, Line.Matrix.act, Proj.omega,
    rightScale_a, rightScale_b,
      rightScale_c, rightScale_d,
    _root_.mul_one, Data.Gaussian.Basic.mul_zero, _root_.add_zero]
  ring1

/-- Right scale multiplication multiplies the determinant by `scale`. -/
theorem det_rightScale (matrix :
  GaussianMatrix) (scale : Data.Gaussian.Basic.Canonical) :
    Matrix2.determinant (rightScale matrix scale) =
      Matrix2.determinant matrix * scale := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [Matrix2.determinant,
      rightScale_a, rightScale_b,
        rightScale_c, rightScale_d,
      Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im]
        <;>
    ring1

/-- Determinant norm acquires precisely the norm of the folded scale. -/
theorem normSq_det_rightScale (matrix :
  GaussianMatrix) (scale : Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Matrix2.determinant (rightScale
      matrix scale)) =
      Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq (Matrix2.determinant
        matrix) := by
  rw [det_rightScale, Data.Gaussian.Norm.Basic.normSq_mul]
  ring1

/-- The first-column weight acquires the same scale norm. -/
theorem firstColumnWeight_rightScale (matrix :
  GaussianMatrix) (scale : Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (rightScale matrix scale).a +
        Data.Gaussian.Norm.Basic.normSq (rightScale matrix scale).c =
      Data.Gaussian.Norm.Basic.normSq scale * (Data.Gaussian.Norm.Basic.normSq matrix.a +
        Data.Gaussian.Norm.Basic.normSq matrix.c) := by
  simp only [rightScale_a, rightScale_c,
    Data.Gaussian.Norm.Basic.normSq_mul]
  ring1

/-- Moving the scale between matrix and tail preserves `D_M` exactly. -/
theorem denominatorWeight_rightScale (matrix :
  GaussianMatrix) (scale tail : Data.Gaussian.Basic.Canonical) :
    denominatorWeight (rightScale matrix
      scale) tail =
      denominatorWeight matrix (scale * tail) := by
  simp only [denominatorWeight, rightScale_a,
    rightScale_b,
    rightScale_c, rightScale_d]
  congr 1 <;> congr 1 <;> ring1
end Purelib.Geometry.Projective.Homography.Scale

end
