module
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Dense.Leading
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Leading-triangular polynomial matrices

Column degree certificates retain the upper-triangular top coefficients of
the same finite matrix. The fraction-free Schur recursion retains those
bounds and the displayed diagonal leading products.
-/

public section

namespace Purelib.LinearAlgebra.PolynomialMatrix.Leading.Triangular

open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.Polynomial

/-- A finite dense polynomial over the supplied coefficient type. -/
abbrev Polynomial (K : Type*) :=
  Dense.Basic.DensePolynomial K
/-- A finite square structural matrix of dense coefficient polynomials. -/
abbrev Matrix (K : Type*) (n : Nat) :=
  PolynomialMatrix.Basic.Matrix K n

open Purelib.Polynomial.Dense.Leading
open _root_.Purelib.Polynomial.Dense.Leading renaming CoefficientPolynomial -> Dense

variable {K : Type*} [ExplicitField K] [DecidableEq K] [Nontrivial K]

/-- Column degree bounds with an upper-triangular leading coefficient matrix.

Entries below the diagonal have strictly smaller degree, and each diagonal entry retains its displayed nonzero leading
coefficient. -/
structure UpperTriangularLeading {n : Nat} (matrix : Matrix K n)
    (degrees : Fin n → Nat) (diagonal : Fin n → K) : Prop where
  /-- Every entry is bounded by the degree assigned to its column. -/ atMost : ∀ row column,
    Dense.Leading.DegreeAtMost (matrix row column) (degrees column)
  /-- Each entry below the diagonal has degree strictly below its column bound. -/ below : ∀ row column, column < row →
    Dense.Leading.DegreeBelow (matrix row column) (degrees column)
  /-- Each diagonal polynomial has its retained degree and nonzero leading coefficient. -/ diagonalLeading : ∀ index,
    Dense.Leading.LeadingTerm (matrix index index) (degrees index) (diagonal index)

/-- Add the leading column degree to each remaining column degree.

Each remaining column retains its successor position. The first column
degree is added to that same column degree. -/
@[expose] def schurDegrees (degrees : Fin (n + 1) → Nat) : Fin n → Nat :=
  fun column => degrees 0 + degrees column.succ

/-- Multiply each remaining leading diagonal coefficient by the first one.

Each retained successor diagonal entry is multiplied by the first diagonal
entry of the same matrix. -/
@[expose] def schurDiagonal (diagonal : Fin (n + 1) → K) : Fin n → K :=
  fun index => diagonal 0 * diagonal index.succ

omit [Nontrivial K] in
/-- The fraction-free Schur complement retains upper-triangular leading data.

The output uses the displayed degree sums and leading diagonal products of the original certificate. -/
theorem schur_preserves
    {matrix : Matrix K (n + 1)} {degrees : Fin (n + 1) → Nat}
    {diagonal : Fin (n + 1) → K}
    (leading : UpperTriangularLeading matrix degrees diagonal) :
    UpperTriangularLeading
      (PolynomialMatrix.Basic.schur matrix)
      (schurDegrees degrees) (schurDiagonal
        diagonal) where
  atMost := by
    intro row column
    rw [PolynomialMatrix.Basic.schur_apply,
      PolynomialMatrix.Basic.tail_apply,
      PolynomialMatrix.Basic.leftColumn_apply,
      PolynomialMatrix.Basic.topRow_apply]
    unfold PolynomialMatrix.Basic.head schurDegrees
    apply Dense.Leading.DegreeAtMost.sub
    · exact Dense.Leading.DegreeAtMost.mul
        (leading.diagonalLeading 0).atMost
        (leading.atMost row.succ column.succ)
    · exact Dense.Leading.DegreeAtMost.mul
        (leading.atMost row.succ 0)
        (leading.atMost 0 column.succ)
  below := by
    intro row column belowDiagonal
    rw [PolynomialMatrix.Basic.schur_apply,
      PolynomialMatrix.Basic.tail_apply,
      PolynomialMatrix.Basic.leftColumn_apply,
      PolynomialMatrix.Basic.topRow_apply]
    unfold PolynomialMatrix.Basic.head schurDegrees
    apply Dense.Leading.DegreeBelow.sub
    · exact Dense.Leading.DegreeBelow.atMostMul
        (leading.diagonalLeading 0).atMost
        (leading.below row.succ column.succ
          (Fin.succ_lt_succ_iff.mpr belowDiagonal))
    · exact Dense.Leading.DegreeBelow.mulAtMost
        (leading.below row.succ 0 (by change 0 < row.val + 1; exact Nat.zero_lt_succ row.val))
        (leading.atMost 0 column.succ)
  diagonalLeading := by
    intro index
    rw [PolynomialMatrix.Basic.schur_apply,
      PolynomialMatrix.Basic.tail_apply,
      PolynomialMatrix.Basic.leftColumn_apply,
      PolynomialMatrix.Basic.topRow_apply]
    unfold PolynomialMatrix.Basic.head schurDegrees
      schurDiagonal
    apply Dense.Leading.LeadingTerm.subBelow
    · exact Dense.Leading.LeadingTerm.mul
        (leading.diagonalLeading 0)
        (leading.diagonalLeading index.succ)
    · exact Dense.Leading.DegreeBelow.mulAtMost
        (leading.below index.succ 0 (by change 0 < index.val + 1; exact Nat.zero_lt_succ index.val))
        (leading.atMost 0 index.succ)

/-- Every scalar pivot generated by the fixed fraction-free recursion is a
nonzero dense polynomial when the input top-coefficient matrix is upper
triangular with nonzero diagonal.

The upper-triangular certificate supplies a nonzero leading coefficient
for every diagonal. The fixed Schur recursion retains those same pivots. -/
theorem scaledInverseData_scalar_nonzero :
    ∀ {n : Nat} {matrix : Matrix K n} {degrees : Fin n → Nat}
      {diagonal : Fin n → K},
      UpperTriangularLeading matrix degrees diagonal →
      (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n matrix).scalar.isZero =
        false
  | 0, _, _, _, _ => by
      change (Dense.Basic.DensePolynomial.constant (1 : K)).isZero =
        false
      exact (Dense.Leading.LeadingTerm.constant (K := K) one_ne_zero).nonzero
  | n + 1, matrix, degrees, diagonal, leading => by
      change
        (PolynomialMatrix.Basic.head matrix *
          (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n
            (PolynomialMatrix.Basic.schur matrix)).scalar).isZero =
          false
      apply Purelib.Polynomial.Dense.Basic.DensePolynomial.isZero_mul_eq_false
      · exact (leading.diagonalLeading 0).nonzero
      · exact scaledInverseData_scalar_nonzero
          (schur_preserves leading)

/-- The scalar degree of the fixed Schur recursion from uniform monic column degrees.

Each pivot contributes its current degree, and the remaining Schur columns
double that degree. The structural dimension recursion retains the resulting
finite degree without an infinite sum or asymptotic bound.
-/
@[expose] def scalarDegree : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, degree => degree + scalarDegree count (degree + degree)

/-- A nonempty Schur dimension with positive initial degree gives a positive scalar degree. -/
theorem scalarDegree_pos {count degree : Nat} (nonempty : 0 < count) (positive : 0 < degree) :
    0 < scalarDegree count degree := by
  cases count with
  | zero => exact False.elim (Nat.not_lt_zero _ nonempty)
  | succ count => exact Nat.lt_of_lt_of_le positive (Nat.le_add_right _ _)

/-- Uniform monic leading columns give a monic scalar at the exact recursively computed degree.

The original fixed Schur recursion and every retained polynomial pivot are
used. Its scalar is nonzero even when some scalar specializations or
intermediate evaluated pivots vanish.
-/
theorem scaledInverseData_scalar_leading :
    ∀ (count : Nat) (degree : Nat) (matrix : Matrix K count),
      UpperTriangularLeading matrix (fun _ => degree) (fun _ => 1) →
      LeadingTerm (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData count matrix).scalar
        (scalarDegree count degree) 1
  | 0, _, _, _ => LeadingTerm.constant one_ne_zero
  | count + 1, degree, matrix, leading => by
      have reduced := schur_preserves leading
      have next : UpperTriangularLeading (PolynomialMatrix.Basic.schur matrix)
          (fun _ => degree + degree) (fun _ => 1) := by
        refine ⟨reduced.atMost, reduced.below, ?_⟩
        intro index
        have diagonal := reduced.diagonalLeading index
        change LeadingTerm _ (degree + degree) (1 * 1) at diagonal
        rewrite [mul_one] at diagonal
        exact diagonal
      have tail := scaledInverseData_scalar_leading count (degree + degree)
        (PolynomialMatrix.Basic.schur matrix) next
      have result := LeadingTerm.mul (leading.diagonalLeading 0) tail
      change LeadingTerm _ (scalarDegree (count + 1) degree) (1 * 1) at result
      rewrite [mul_one] at result
      exact result

end Purelib.LinearAlgebra.PolynomialMatrix.Leading.Triangular

end
