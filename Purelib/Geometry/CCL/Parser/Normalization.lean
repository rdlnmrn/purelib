module
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
public import Purelib.Geometry.Projective.Homography.Basic
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.Gaussian

open Purelib.Geometry.Projective

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace Purelib.Geometry.CCL.Parser

/-- Matrix for the scale applied before sector selection. -/
def normalizationMatrix (kind : Syntax.BlockKind) (exponent : Nat) :
  GaussianMatrix :=
  match kind with
  | .initialLow => Line.Matrix.scale (Power.natPow Canonical.gamma exponent)
  | .initialHigh | .loop => Line.Matrix.scale (Power.natPow Canonical.gamma exponent)⁻¹

/-- The radial normalization matrix has nonzero determinant. -/
theorem normalizationMatrix_det_ne (kind : Syntax.BlockKind) (exponent : Nat) :
    BoundaryAdjugate.determinant
      (normalizationMatrix kind exponent) ≠ 0 := by
  have gammaNonzero : Canonical.gamma ≠ 0 := by decide
  have powerNonzero : Power.natPow Canonical.gamma exponent ≠ 0 :=
    Power.natPow_ne_zero_direct Canonical.gamma gammaNonzero exponent
  cases kind with
  | initialLow =>
      simpa only [normalizationMatrix, Line.Matrix.scale,
        BoundaryAdjugate.determinant,
        Matrix2.determinant,
        Data.Gaussian.Basic.mul_one,
        Data.Gaussian.Basic.zero_mul,
        Data.Gaussian.Basic.sub_zero] using powerNonzero
  | initialHigh | loop =>
      have inverseNonzero : (Power.natPow Canonical.gamma exponent)⁻¹ ≠ 0 := by
        simpa only [Data.Gaussian.Field.inv_eq] using Data.Gaussian.Field.inv_ne_zero_direct powerNonzero
      simpa only [normalizationMatrix, Line.Matrix.scale,
        BoundaryAdjugate.determinant,
        Matrix2.determinant,
        Data.Gaussian.Basic.mul_one,
        Data.Gaussian.Basic.zero_mul,
        Data.Gaussian.Basic.sub_zero] using inverseNonzero

/-- Compose a homography with the radial normalization matrix.

The block kind chooses multiplication by the retained power of gamma or its inverse. -/
def normalizedMatrix (kind : Syntax.BlockKind) (exponent : Nat)
    (matrix : GaussianMatrix) : GaussianMatrix :=
  Coordinates2.Matrix.mul (normalizationMatrix kind exponent) matrix

/-- Radial normalization leaves the denominator row unchanged.

For either retained block kind, the normalization matrix scales only the numerator row and keeps both denominator
entries exactly. -/
theorem normalizedMatrix_lowerRow
    (kind : Syntax.BlockKind) (exponent : Nat) (matrix : GaussianMatrix) :
    (normalizedMatrix kind exponent matrix).c = matrix.c ∧
      (normalizedMatrix kind exponent matrix).d = matrix.d := by
  cases kind <;> constructor <;>
    (simp only [normalizedMatrix, normalizationMatrix, Coordinates2.Matrix.mul,
      Line.Matrix.scale, Data.Gaussian.Basic.zero_mul,
      Data.Gaussian.Basic.one_mul,
      Data.Gaussian.Basic.zero_add, -eq_self, -iff_self]
     rfl)

/-- The normalized matrix acts by the parser's normalized value.

The equality uses the original nonzero homography denominator. -/
theorem homographic_normalizedMatrix
    (kind : Syntax.BlockKind) (exponent : Nat) (matrix : GaussianMatrix) (value :
      Data.Gaussian.Basic.Canonical) :
    Homography.Basic.homographic (normalizedMatrix kind exponent matrix) value =
      Semantics.Basic.normalizedValue kind exponent (Homography.Basic.homographic matrix value) := by
  cases kind with
  | initialHigh =>
      unfold normalizedMatrix normalizationMatrix
        Semantics.Basic.normalizedValue Homography.Basic.homographic
        Homography.Basic.numerator Homography.Basic.denominator
      simp only [Coordinates2.Matrix.mul, Line.Matrix.scale,
        Data.Gaussian.Basic.zero_mul,
        Data.Gaussian.Basic.one_mul,
        Data.Gaussian.Basic.zero_add,
        Data.Gaussian.Basic.add_zero]
      rw [Data.Gaussian.Basic.mul_assoc
        (Power.natPow Canonical.gamma exponent)⁻¹ matrix.a value]
      calc
        ((Power.natPow Canonical.gamma exponent)⁻¹ * (matrix.a * value) +
            (Power.natPow Canonical.gamma exponent)⁻¹ * matrix.b) *
              (matrix.c * value + matrix.d)⁻¹ =
            ((Power.natPow Canonical.gamma exponent)⁻¹ *
              (matrix.a * value + matrix.b)) *
                (matrix.c * value + matrix.d)⁻¹ := by
              rw [Data.Gaussian.Basic.left_distrib]
        _ = (Power.natPow Canonical.gamma exponent)⁻¹ *
              ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) :=
            Data.Gaussian.Basic.mul_assoc _ _ _
        _ = ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) *
              (Power.natPow Canonical.gamma exponent)⁻¹ :=
            Data.Gaussian.Basic.mul_comm _ _
  | initialLow =>
      unfold normalizedMatrix normalizationMatrix
        Semantics.Basic.normalizedValue Homography.Basic.homographic
        Homography.Basic.numerator Homography.Basic.denominator
      simp only [Coordinates2.Matrix.mul, Line.Matrix.scale,
        Data.Gaussian.Basic.zero_mul,
        Data.Gaussian.Basic.one_mul,
        Data.Gaussian.Basic.zero_add,
        Data.Gaussian.Basic.add_zero]
      rw [Data.Gaussian.Basic.mul_assoc
        (Power.natPow Canonical.gamma exponent) matrix.a value]
      calc
        (Power.natPow Canonical.gamma exponent * (matrix.a * value) +
            Power.natPow Canonical.gamma exponent * matrix.b) *
              (matrix.c * value + matrix.d)⁻¹ =
            (Power.natPow Canonical.gamma exponent *
              (matrix.a * value + matrix.b)) *
                (matrix.c * value + matrix.d)⁻¹ := by
              rw [Data.Gaussian.Basic.left_distrib]
        _ = Power.natPow Canonical.gamma exponent *
              ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) :=
            Data.Gaussian.Basic.mul_assoc _ _ _
  | loop =>
      unfold normalizedMatrix normalizationMatrix
        Semantics.Basic.normalizedValue Homography.Basic.homographic
        Homography.Basic.numerator Homography.Basic.denominator
      simp only [Coordinates2.Matrix.mul, Line.Matrix.scale,
        Data.Gaussian.Basic.zero_mul,
        Data.Gaussian.Basic.one_mul,
        Data.Gaussian.Basic.zero_add,
        Data.Gaussian.Basic.add_zero]
      rw [Data.Gaussian.Basic.mul_assoc
        (Power.natPow Canonical.gamma exponent)⁻¹ matrix.a value]
      calc
        ((Power.natPow Canonical.gamma exponent)⁻¹ * (matrix.a * value) +
            (Power.natPow Canonical.gamma exponent)⁻¹ * matrix.b) *
              (matrix.c * value + matrix.d)⁻¹ =
            ((Power.natPow Canonical.gamma exponent)⁻¹ *
              (matrix.a * value + matrix.b)) *
                (matrix.c * value + matrix.d)⁻¹ := by
              rw [Data.Gaussian.Basic.left_distrib]
        _ = (Power.natPow Canonical.gamma exponent)⁻¹ *
              ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) :=
            Data.Gaussian.Basic.mul_assoc _ _ _
        _ = ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) *
              (Power.natPow Canonical.gamma exponent)⁻¹ :=
            Data.Gaussian.Basic.mul_comm _ _
end Purelib.Geometry.CCL.Parser

end

section
@[expose] public section

/-!
# Boundary provenance for finite CCL formulas

This module follows the syntax tree of each next-bit formula.  Every atom is
paired with a constructive description of its exact zero boundary.  Formula
inspection can therefore hand an unresolved atom directly to the finite
curve-event layer without guessing its geometric origin from coefficients.
-/

namespace Purelib.Geometry.CCL.Parser

/-- Composing with radial normalization preserves a nonzero determinant. -/
private theorem normalizedMatrix_det_ne
    (kind : Syntax.BlockKind) (exponent : Nat) (matrix : GaussianMatrix)
    (matrixNonzero : Matrix2.determinant matrix ≠ 0) :
    Matrix2.determinant
      (normalizedMatrix kind exponent matrix) ≠ 0 := by
  rw [normalizedMatrix, Coordinates2.Matrix.det_mul]
  exact Data.Gaussian.Field.mul_ne_zero_direct (normalizationMatrix_det_ne kind exponent)
    matrixNonzero
end Purelib.Geometry.CCL.Parser

end
