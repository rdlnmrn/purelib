module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Gaussian.Basic
public import Purelib.Data.GaussianInt.Basic
import Purelib.Elab.Deriving.Repr
import Purelib.Tactic.QuotientFreeOmega

import Purelib.Data.Gaussian.Field
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

open Purelib.Algebra.Field

open Purelib

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}

set_option genInjectivity false in
/-- A transparent two-by-two matrix. -/
@[ext]
structure Matrix (K : Type*) where
  /-- The entry in the first row and first column. -/ a : K
  /-- The entry in the first row and second column. -/ b : K
  /-- The entry in the second row and first column. -/ c : K
  /-- The entry in the second row and second column. -/ d : K
deriving @[expose] DecidableEq

constructive_injectivity Matrix

derive_exposed_repr Matrix

end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Exchange the diagonal entries and negate the off-diagonal entries. -/
@[expose] def adjugate [Neg K] (matrix : Matrix2 K) : Matrix2 K :=
  ⟨matrix.d, -matrix.b, -matrix.c, matrix.a⟩

end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Compute the signed two-by-two determinant of the retained matrix. -/
@[expose] def determinant [Mul K] [Sub K] (matrix : Matrix2 K) : K :=
  matrix.a * matrix.d - matrix.b * matrix.c
end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The two-by-two matrix with unit diagonal and zero off-diagonal entries. -/
@[expose] def identity [Zero K] [One K] : Matrix2 K := ⟨1, 0, 0, 1⟩
end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Explicit two-by-two matrix product. -/
@[expose] def mul [Add K] [Mul K] (M N : Matrix2 K) : Matrix2 K :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩
end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix

/-- The trace of a displayed matrix is the sum of its diagonal entries. -/
@[expose] def trace [Add K] (matrix : Matrix K) : K := matrix.a + matrix.d

/-- Apply a supplied coefficient map separately to the four retained matrix entries. -/
@[expose] def map {L : Type*} (coefficientMap : K → L) (matrix : Matrix K) : Matrix L :=
  ⟨coefficientMap matrix.a, coefficientMap matrix.b, coefficientMap matrix.c, coefficientMap matrix.d⟩

/-- Interchange the row and column of each retained matrix entry. -/
@[expose] def transpose (matrix : Matrix K) : Matrix K :=
  ⟨matrix.a, matrix.c, matrix.b, matrix.d⟩

/-- Transpose a matrix after applying the supplied conjugation to each entry. -/
@[expose] def conjugateTranspose (conjugate : K → K) (matrix : Matrix K) : Matrix K :=
  transpose (map conjugate matrix)

/-- Both products of the retained matrix and its conjugate transpose equal the identity. -/
@[expose] def IsUnitary [Zero K] [One K] [Add K] [Mul K]
    (conjugate : K → K) (matrix : Matrix K) : Prop :=
  mul (conjugateTranspose conjugate matrix) matrix = identity ∧
    mul matrix (conjugateTranspose conjugate matrix) = identity

/-- Add corresponding entries of two displayed matrices. -/
@[expose] def add [Add K] (left right : Matrix K) : Matrix K :=
  ⟨left.a + right.a, left.b + right.b, left.c + right.c, left.d + right.d⟩

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Multiply each retained matrix entry by the supplied scalar. -/
@[expose] def scalarScale [Mul K] (factor : K) (matrix : Matrix2 K) : Matrix2 K :=
  ⟨factor * matrix.a, factor * matrix.b,
    factor * matrix.c, factor * matrix.d⟩
end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2.Matrix
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A two-by-two matrix over the retained Gaussian integer coefficient type. -/
abbrev SourceEncodingEncoderIntegralMat2Alias := Matrix2
  Data.GaussianInt.Basic.SourceEncodingEncoderGaussianIntAlias
end Purelib.LinearAlgebra.Coordinates2.Matrix

namespace Purelib.LinearAlgebra.Coordinates2.Matrix
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A two-by-two matrix with Gaussian integer entries. -/
abbrev SourceCCFEncoderIntegralMat2Alias := Matrix2 Data.GaussianInt

end Purelib.LinearAlgebra.Coordinates2.Matrix

namespace Purelib.LinearAlgebra.Coordinates2.Matrix
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A two-by-two matrix with exact Gaussian rational entries. -/
abbrev SourceCCFEncoderMat2Alias := Matrix2
  Data.Gaussian.Basic.Canonical
end Purelib.LinearAlgebra.Coordinates2.Matrix

namespace Purelib.LinearAlgebra.Coordinates2.Matrix
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A two-by-two matrix with exact Gaussian rational entries. -/
abbrev GaussianMatrix := Matrix2
  Data.Gaussian.Basic.Canonical
end Purelib.LinearAlgebra.Coordinates2.Matrix
namespace Purelib.LinearAlgebra.Coordinates2.Matrix
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The retained two-by-two Gaussian rational matrix type. -/
abbrev SourceEncodingEncoderMat2Alias :=
  GaussianMatrix
end Purelib.LinearAlgebra.Coordinates2.Matrix

namespace Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Explicit adjugate of a two-by-two constructive Gaussian matrix. -/
@[expose] def adjugate (matrix :
  GaussianMatrix) : GaussianMatrix :=
  ⟨matrix.d, -matrix.b, -matrix.c, matrix.a⟩
end Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

namespace Purelib.LinearAlgebra.Coordinates2.Matrix.Matrix2
section Mat2

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Determinant of a two-by-two constructive Gaussian matrix. -/
@[expose] def determinant (M :
  GaussianMatrix) : Data.Gaussian.Basic.Canonical := M.a * M.d - M.b * M.c
end Mat2
end Purelib.LinearAlgebra.Coordinates2.Matrix.Matrix2

namespace Purelib.LinearAlgebra.Coordinates2.Matrix.Boundary

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A nonzero determinant constructively forces a nonzero affine lower row. -/
theorem lowerRow_ne_of_determinant_ne (matrix :
  GaussianMatrix)
    (determinantNonzero : Matrix2.Matrix2.determinant matrix ≠ 0) :
    matrix.c ≠ 0 ∨ matrix.d ≠ 0 := by
  by_cases lowerLeftZero : matrix.c = 0
  · by_cases lowerRightZero : matrix.d = 0
    · have determinantZero :
          Matrix2.Matrix2.determinant matrix = 0 := by
        rw [Matrix2.Matrix2.determinant, lowerLeftZero, lowerRightZero]
        simp only [Data.Gaussian.Basic.mul_zero,
          Data.Gaussian.Basic.sub_zero, -eq_self, -iff_self]
        rfl
      exact (determinantNonzero determinantZero).elim
    · exact Or.inr lowerRightZero
  · exact Or.inl lowerLeftZero
end Purelib.LinearAlgebra.Coordinates2.Matrix.Boundary

namespace Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Read the determinant of the retained Gaussian rational matrix. -/
@[expose] def determinant (matrix :
  GaussianMatrix) : Data.Gaussian.Basic.Canonical :=
  Matrix2.Matrix2.determinant matrix
end Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

namespace Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Taking the adjugate preserves the two-by-two Gaussian determinant. -/
@[simp] theorem determinant_adjugate (matrix :
  GaussianMatrix) :
    Matrix2.BoundaryAdjugate.determinant (Matrix2.BoundaryAdjugate.adjugate matrix) =
      Matrix2.BoundaryAdjugate.determinant matrix := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [Matrix2.BoundaryAdjugate.determinant, Matrix2.BoundaryAdjugate.adjugate, Matrix2.Matrix2.determinant,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im, -eq_self, -iff_self] <;>
    ring1
end Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

namespace Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A nonzero determinant remains nonzero after taking the adjugate. -/
private theorem adjugateDeterminantNonzero
    (matrix : GaussianMatrix)
    (determinantNonzero :
      Matrix2.BoundaryAdjugate.determinant matrix ≠ 0) :
    Matrix2.BoundaryAdjugate.determinant
      (Matrix2.BoundaryAdjugate.adjugate matrix) ≠ 0 := by
  rw [Matrix2.BoundaryAdjugate.determinant_adjugate]
  exact determinantNonzero
end Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix
variable [ExplicitField K]

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The adjugate times its matrix is the determinant times the identity. -/
theorem adjugate_mul (matrix : Matrix2 K) :
    mul matrix.adjugate matrix = Matrix2.scalarScale matrix.determinant Matrix2.identity := by
  ext <;> unfold mul adjugate Matrix2.scalarScale determinant Matrix2.identity <;> ring1

end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix
variable [ExplicitField K]

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Taking the adjugate preserves the two-by-two determinant. -/
theorem determinant_adjugate (matrix : Matrix2 K) :
    determinant matrix.adjugate = determinant matrix := by
  unfold determinant adjugate
  ring1
end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix
variable [ExplicitField K]

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The determinant of a product is the product of the two determinants. -/
theorem determinant_mul (left right : Matrix2 K) :
    determinant (mul left right) = determinant left * determinant right := by
  unfold determinant mul
  ring1
end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2.Matrix

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Identity decoder before the first complete block. -/
@[expose] def identityMatrix :
  GaussianMatrix := ⟨1, 0, 0, 1⟩
end Purelib.LinearAlgebra.Coordinates2.Matrix

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix
variable [ExplicitField K]

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The two-by-two identity acts trivially on the left. -/
@[simp] theorem identity_mul (matrix : Matrix2 K) :
    mul Matrix2.identity matrix = matrix := by
  ext <;> unfold mul Matrix2.identity <;> ring1
end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The reverse product gives the same determinant scalar. -/
theorem adjugate_mul (matrix :
  GaussianMatrix) :
    Matrix2.mul (Matrix2.BoundaryAdjugate.adjugate matrix) matrix =
      ⟨Matrix2.BoundaryAdjugate.determinant matrix, 0, 0, Matrix2.BoundaryAdjugate.determinant matrix⟩ := by
  apply Matrix2.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [Matrix2.mul, Matrix2.BoundaryAdjugate.adjugate, Matrix2.BoundaryAdjugate.determinant,
        Matrix2.Matrix2.determinant, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re,
          Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im,
          Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im, -eq_self, -iff_self] <;>
      ring1
end Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

namespace Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Multiplying a decoder by its adjugate gives its determinant scalar. -/
theorem mul_adjugate (matrix :
  GaussianMatrix) :
    Matrix2.mul matrix (Matrix2.BoundaryAdjugate.adjugate matrix) =
      ⟨Matrix2.BoundaryAdjugate.determinant matrix, 0, 0, Matrix2.BoundaryAdjugate.determinant matrix⟩ := by
  apply Matrix2.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [Matrix2.mul, Matrix2.BoundaryAdjugate.adjugate, Matrix2.BoundaryAdjugate.determinant,
        Matrix2.Matrix2.determinant, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re,
          Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im,
          Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im, -eq_self, -iff_self] <;>
      ring1
end Purelib.LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate

namespace Purelib.LinearAlgebra.Coordinates2.Matrix

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The Gaussian determinant of a product is the product of its determinants. -/
theorem det_mul (left right :
  GaussianMatrix) :
    Matrix2.Matrix2.determinant (Matrix2.mul left right) =
      Matrix2.Matrix2.determinant left *
        Matrix2.Matrix2.determinant right := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [Matrix2.Matrix2.determinant, Matrix2.mul,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, -eq_self, -iff_self] <;>
    ring1
end Purelib.LinearAlgebra.Coordinates2.Matrix

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix
variable [ExplicitField K]

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A matrix times its adjugate is the determinant times the identity. -/
theorem mul_adjugate (matrix : Matrix2 K) :
    mul matrix matrix.adjugate = Matrix2.scalarScale matrix.determinant Matrix2.identity := by
  ext <;> unfold mul adjugate Matrix2.scalarScale determinant Matrix2.identity <;> ring1
end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix
variable [ExplicitField K]

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Multiplication of the explicit two-by-two matrices is associative. -/
theorem mul_assoc (first second third : Matrix2 K) :
    mul (mul first second) third = mul first (mul second third) := by
  ext <;> unfold mul <;> ring1
end Matrix
end Purelib.LinearAlgebra.Coordinates2

namespace Purelib.LinearAlgebra.Coordinates2
variable {K : Type*}
namespace Matrix
variable [ExplicitField K]

open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The two-by-two identity acts trivially on the right. -/
@[simp] theorem mul_identity (matrix : Matrix2 K) :
    mul matrix Matrix2.identity = matrix := by
  ext <;> unfold mul Matrix2.identity <;> ring1
end Matrix
end Purelib.LinearAlgebra.Coordinates2

end

section
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace Purelib.LinearAlgebra.Coordinates2.Matrix
/-- Right multiplication by a scalar identity matrix scales the displayed matrix. -/
public theorem
  mul_scale_identity
  (factor : K) (matrix : Matrix K) :
    mul matrix (scalarScale factor
      identity) =
      scalarScale factor matrix := by
  apply Coordinates2.Matrix.ext <;>
    unfold mul scalarScale
      identity <;> ring1

/-- Left multiplication by a scalar identity matrix scales the displayed matrix. -/
public theorem
  scale_identity_mul
  (factor : K) (matrix : Matrix K) :
    mul (scalarScale factor
      identity) matrix =
      scalarScale factor matrix := by
  apply Coordinates2.Matrix.ext <;>
    unfold mul scalarScale
      identity <;> ring1

/-- Multiplication of every matrix entry by minus one is injective. -/
public theorem
  scale_neg_one_injective
  {left right : Matrix K}
    (equal : scalarScale (-1) left =
      scalarScale (-1) right) :
    left = right := by
  apply Coordinates2.Matrix.ext
  · have coordinate := congrArg Coordinates2.Matrix.a equal
    change (-1 : K) * left.a = (-1 : K) * right.a at coordinate
    calc
      left.a = -((-1 : K) * left.a) := by ring1
      _ = -((-1 : K) * right.a) := by rw [coordinate]
      _ = right.a := by ring1
  · have coordinate := congrArg Coordinates2.Matrix.b equal
    change (-1 : K) * left.b = (-1 : K) * right.b at coordinate
    calc
      left.b = -((-1 : K) * left.b) := by ring1
      _ = -((-1 : K) * right.b) := by rw [coordinate]
      _ = right.b := by ring1
  · have coordinate := congrArg Coordinates2.Matrix.c equal
    change (-1 : K) * left.c = (-1 : K) * right.c at coordinate
    calc
      left.c = -((-1 : K) * left.c) := by ring1
      _ = -((-1 : K) * right.c) := by rw [coordinate]
      _ = right.c := by ring1
  · have coordinate := congrArg Coordinates2.Matrix.d equal
    change (-1 : K) * left.d = (-1 : K) * right.d at coordinate
    calc
      left.d = -((-1 : K) * left.d) := by ring1
      _ = -((-1 : K) * right.d) := by rw [coordinate]
      _ = right.d := by ring1

/-- Cancel a displayed right matrix factor with determinant minus one. -/
public theorem
  mul_right_cancel_of_determinant_eq_neg_one
    (basis left right : Matrix K)
    (determinantEq : determinant basis = -1)
    (equal : mul left basis = mul
      right basis) :
    left = right := by
  have scaled : scalarScale (-1) left =
    scalarScale (-1) right := by
    calc
      scalarScale (-1) left =
          mul left
            (scalarScale (-1)
              identity) :=

          (mul_scale_identity
          (-1) left).symm
      _ = mul left
          (mul basis (adjugate
            basis)) := by
        rw [mul_adjugate, determinantEq]
      _ = mul (mul left basis)
          (adjugate basis) := by rw
            [mul_assoc]
      _ = mul (mul right basis)
          (adjugate basis) := by rw [equal]
      _ = mul right
          (mul basis (adjugate
            basis)) := by
        rw [mul_assoc]
      _ = mul right
          (scalarScale (-1)
            identity) := by
        rw [mul_adjugate, determinantEq]
      _ = scalarScale (-1) right :=
        mul_scale_identity
        (-1) right
  exact
    scale_neg_one_injective
    scaled
end Purelib.LinearAlgebra.Coordinates2.Matrix
end
