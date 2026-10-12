module

import Purelib.Algebra.Field.ExplicitField

public import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Algebra.Group.Negation
import Purelib.Data.Nat.Order
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
@[expose] public section

/-!
# Divine Proportions, Theorem 109: cyclic quadrilaterals

A quadrilateral is kept as four displayed points together with the source's
finite distinctness and noncollinearity certificates.  The cyclic predicate
stores an explicit conic, center, quadrance, circle presentation, and four
incidence proofs.

The printed four-by-four determinant is expanded by `determinantThree`; no
matrix determinant, permutation enumeration, or quotient of cyclic orderings
is introduced.  A translated determinant identity then gives both directions
of Theorem 109 constructively.
-/

namespace Purelib.Geometry

variable {K : Type*} [ExplicitField K]
namespace Quadrilaterals.Basic.Quadrilateral

/-- The three-by-three determinant used to expand the book's displayed
four-by-four determinant. -/
def determinantThree
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : K) : K :=
  a₁₁ * (a₂₂ * a₃₃ - a₂₃ * a₃₂) -
    a₁₂ * (a₂₁ * a₃₃ - a₂₃ * a₃₁) +
    a₁₃ * (a₂₁ * a₃₂ - a₂₂ * a₃₁)
end Quadrilaterals.Basic.Quadrilateral

end Purelib.Geometry

end

section
/-!
# Divine Proportions, Chapter 5 quad-triple exercises

The exercises below are direct finite polynomial consequences of
Archimedes' function.  Exercise 5.11 exposes the same distinct-centre premise
missing from the source's earlier quadratic-compatibility claim; no root is
selected in the degenerate case.
-/

@[expose] public section

namespace Purelib.LinearAlgebra.Coordinates3.Matrix

variable {K : Type*} [ExplicitField K]

/-- A direct three-by-three determinant expansion used only to retain the
source's finite four-by-four determinant literally. -/
def scalarDeterminantThree
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : K) : K :=
  a₁₁ * (a₂₂ * a₃₃ - a₂₃ * a₃₂) -
    a₁₂ * (a₂₁ * a₃₃ - a₂₃ * a₃₁) +
    a₁₃ * (a₂₁ * a₃₂ - a₂₂ * a₃₁)
end Purelib.LinearAlgebra.Coordinates3.Matrix

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: bordered-tridiagonal determinants

The determinant family in Exercise 8.8 is evaluated by its finite continuant
and last-column cofactor expansion.  The first four literal determinants from
the source are also checked independently.
-/

namespace Purelib.LinearAlgebra.Coordinates3.Matrix

variable {K : Type*} [ExplicitField K]

/-- Ordinary three-by-three determinant in its six-term expansion. -/
def determinantThree {R : Type*} [CommRing R]
    (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : R) : R :=
  a₀₀ * a₁₁ * a₂₂ + a₀₁ * a₁₂ * a₂₀ + a₀₂ * a₁₀ * a₂₁ -
    a₀₂ * a₁₁ * a₂₀ - a₀₁ * a₁₀ * a₂₂ - a₀₀ * a₁₂ * a₂₁
end Purelib.LinearAlgebra.Coordinates3.Matrix

end

section
public section

/-!
# Explicit finite three-by-three matrices

The rotation paper uses only three-by-three matrices.  This module stores all
nine entries directly and implements the required operations by fixed
coordinate formulas, avoiding generic dimension, basis, and finite-cardinality
machinery.
-/

namespace Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [ExplicitField K]

@[expose] public section

set_option genInjectivity false in
/-- A displayed three-by-three matrix with rows and columns ordered `t,r,s`.

The nine retained scalar entries follow the original row order and column
order. Constructor certificates identify these same entries individually,
without introducing an additional dimension or changing their carrier. -/
@[ext]
structure Matrix3 (K : Type*) where
  /-- The retained entry in row `t` and column `t`. -/ tt : K
  /-- The retained entry in row `t` and column `r`. -/ tr : K
  /-- The retained entry in row `t` and column `s`. -/ ts : K
  /-- The retained entry in row `r` and column `t`. -/ rt : K
  /-- The retained entry in row `r` and column `r`. -/ rr : K
  /-- The retained entry in row `r` and column `s`. -/ rs : K
  /-- The retained entry in row `s` and column `t`. -/ st : K
  /-- The retained entry in row `s` and column `r`. -/ sr : K
  /-- The retained entry in row `s` and column `s`. -/ ss : K
deriving DecidableEq

constructive_injectivity Matrix3

end

namespace Matrix3

/-- The zero three-by-three matrix. -/
@[expose] def zero : Matrix3 K := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The three-by-three identity matrix. -/
@[expose] def identity : Matrix3 K := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

/-- Coordinatewise matrix addition. -/
@[expose] def add (left right : Matrix3 K) : Matrix3 K :=
  ⟨left.tt + right.tt, left.tr + right.tr, left.ts + right.ts,
    left.rt + right.rt, left.rr + right.rr, left.rs + right.rs,
    left.st + right.st, left.sr + right.sr, left.ss + right.ss⟩

/-- Coordinatewise matrix negation. -/
@[expose] def neg (matrix : Matrix3 K) : Matrix3 K :=
  ⟨-matrix.tt, -matrix.tr, -matrix.ts,
    -matrix.rt, -matrix.rr, -matrix.rs,
    -matrix.st, -matrix.sr, -matrix.ss⟩

/-- Coordinatewise matrix subtraction. -/
@[expose] def sub (left right : Matrix3 K) : Matrix3 K :=
  ⟨left.tt - right.tt, left.tr - right.tr, left.ts - right.ts,
    left.rt - right.rt, left.rr - right.rr, left.rs - right.rs,
    left.st - right.st, left.sr - right.sr, left.ss - right.ss⟩

/-- Coordinatewise scalar multiplication. -/
@[expose] def scale (scalar : K) (matrix : Matrix3 K) : Matrix3 K :=
  ⟨scalar * matrix.tt, scalar * matrix.tr, scalar * matrix.ts,
    scalar * matrix.rt, scalar * matrix.rr, scalar * matrix.rs,
    scalar * matrix.st, scalar * matrix.sr, scalar * matrix.ss⟩

/-- Matrix transpose. -/
@[expose] def transpose (matrix : Matrix3 K) : Matrix3 K :=
  ⟨matrix.tt, matrix.rt, matrix.st,
    matrix.tr, matrix.rr, matrix.sr,
    matrix.ts, matrix.rs, matrix.ss⟩

/-- Fixed-size matrix multiplication. -/
@[expose] def mul (left right : Matrix3 K) : Matrix3 K :=
  ⟨left.tt * right.tt + left.tr * right.rt + left.ts * right.st,
    left.tt * right.tr + left.tr * right.rr + left.ts * right.sr,
    left.tt * right.ts + left.tr * right.rs + left.ts * right.ss,
    left.rt * right.tt + left.rr * right.rt + left.rs * right.st,
    left.rt * right.tr + left.rr * right.rr + left.rs * right.sr,
    left.rt * right.ts + left.rr * right.rs + left.rs * right.ss,
    left.st * right.tt + left.sr * right.rt + left.ss * right.st,
    left.st * right.tr + left.sr * right.rr + left.ss * right.sr,
    left.st * right.ts + left.sr * right.rs + left.ss * right.ss⟩

/-- Right action of a displayed row vector on a matrix. -/
@[expose] def rowMul (vector : Vector K) (matrix : Matrix3 K) : Vector K :=
  ⟨vector.t * matrix.tt + vector.r * matrix.rt + vector.s * matrix.st,
    vector.t * matrix.tr + vector.r * matrix.rr + vector.s * matrix.sr,
    vector.t * matrix.ts + vector.r * matrix.rs + vector.s * matrix.ss⟩

/-- The first displayed row, cached as a vector when finite matrix
constructions need to select a pivot row. -/
@[expose] def rowT (matrix : Matrix3 K) : Vector K :=
  ⟨matrix.tt, matrix.tr, matrix.ts⟩

/-- The second displayed row. -/
@[expose] def rowR (matrix : Matrix3 K) : Vector K :=
  ⟨matrix.rt, matrix.rr, matrix.rs⟩

/-- The third displayed row. -/
@[expose] def rowS (matrix : Matrix3 K) : Vector K :=
  ⟨matrix.st, matrix.sr, matrix.ss⟩

/-- The outer product `columnᵀ row`. -/
@[expose] def outer (column row : Vector K) : Matrix3 K :=
  ⟨column.t * row.t, column.t * row.r, column.t * row.s,
    column.r * row.t, column.r * row.r, column.r * row.s,
    column.s * row.t, column.s * row.r, column.s * row.s⟩

/-- Matrix trace. -/
@[expose] def trace (matrix : Matrix3 K) : K := matrix.tt + matrix.rr + matrix.ss

/-- Classical adjugate, displayed by its nine signed two-by-two minors. -/
@[expose] def adjugate (matrix : Matrix3 K) : Matrix3 K :=
  ⟨matrix.rr * matrix.ss - matrix.rs * matrix.sr,
    matrix.ts * matrix.sr - matrix.tr * matrix.ss,
    matrix.tr * matrix.rs - matrix.ts * matrix.rr,
    matrix.rs * matrix.st - matrix.rt * matrix.ss,
    matrix.tt * matrix.ss - matrix.ts * matrix.st,
    matrix.ts * matrix.rt - matrix.tt * matrix.rs,
    matrix.rt * matrix.sr - matrix.rr * matrix.st,
    matrix.tr * matrix.st - matrix.tt * matrix.sr,
    matrix.tt * matrix.rr - matrix.tr * matrix.rt⟩

/-- The coefficient of `X` in `det(XI-A)`. -/
@[expose] def principalTrace (matrix : Matrix3 K) : K := trace (adjugate matrix)

/-- The displayed three-by-three determinant. -/
@[expose] def determinant (matrix : Matrix3 K) : K :=
  matrix.tt * (matrix.rr * matrix.ss - matrix.rs * matrix.sr) -
    matrix.tr * (matrix.rt * matrix.ss - matrix.rs * matrix.st) +
      matrix.ts * (matrix.rt * matrix.sr - matrix.rr * matrix.st)

/-- Evaluation at `X` of `det(XI-A)`, the characteristic polynomial used in
the paper, without introducing a generic polynomial representation. -/
@[expose] def characteristicValue (matrix : Matrix3 K) (X : K) : K :=
  determinant (sub (scale X identity) matrix)

/-- An explicitly displayed matrix is antisymmetric when transposition is
coordinatewise negation. -/
@[expose] def IsAntisymmetric (matrix : Matrix3 K) : Prop :=
  transpose matrix = neg matrix

/-- A displayed matrix is symmetric when its explicit transpose is itself. -/
@[expose] def IsSymmetric (matrix : Matrix3 K) : Prop :=
  transpose matrix = matrix

omit [ExplicitField K] in
/-- Transposing a displayed matrix twice recovers it. -/
@[simp] theorem transpose_transpose (matrix : Matrix3 K) :
    transpose (transpose matrix) = matrix := by
  ext <;> rfl

/-- The transpose of the zero matrix is zero. -/
@[simp] theorem transpose_zero : transpose (zero : Matrix3 K) = zero := by
  ext <;> rfl

/-- The transpose of the identity matrix is itself. -/
@[simp] theorem transpose_identity :
    transpose (identity : Matrix3 K) = identity := by
  ext <;> rfl

/-- Transposition preserves displayed matrix addition. -/
theorem transpose_add (left right : Matrix3 K) :
    transpose (add left right) = add (transpose left) (transpose right) := by
  ext <;> rfl

/-- Transposition commutes with displayed matrix negation. -/
theorem transpose_neg (matrix : Matrix3 K) :
    transpose (neg matrix) = neg (transpose matrix) := by
  ext <;> rfl

/-- Transposition preserves displayed matrix subtraction. -/
theorem transpose_sub (left right : Matrix3 K) :
    transpose (sub left right) = sub (transpose left) (transpose right) := by
  ext <;> rfl

/-- Transposition commutes with scalar multiplication. -/
theorem transpose_scale (scalar : K) (matrix : Matrix3 K) :
    transpose (scale scalar matrix) = scale scalar (transpose matrix) := by
  ext <;> rfl

/-- Transposition reverses the order of displayed matrix multiplication. -/
theorem transpose_mul (left right : Matrix3 K) :
    transpose (mul left right) = mul (transpose right) (transpose left) := by
  ext <;> unfold transpose mul <;> ring1

/-- The identity matrix is a left multiplicative identity. -/
@[simp] theorem identity_mul (matrix : Matrix3 K) :
    mul identity matrix = matrix := by
  ext <;> unfold mul identity <;> ring1

/-- The identity matrix is a right multiplicative identity. -/
@[simp] theorem mul_identity (matrix : Matrix3 K) :
    mul matrix identity = matrix := by
  ext <;> unfold mul identity <;> ring1

/-- Displayed three-dimensional matrix multiplication is associative. -/
theorem mul_assoc (first second third : Matrix3 K) :
    mul (mul first second) third = mul first (mul second third) := by
  ext <;> unfold mul <;> ring1

/-- Matrix multiplication distributes over addition in its left argument. -/
theorem mul_add_left (first second third : Matrix3 K) :
    mul (add first second) third = add (mul first third) (mul second third) := by
  ext <;> unfold mul add <;> ring1

/-- Matrix multiplication distributes over addition in its right argument. -/
theorem mul_add_right (first second third : Matrix3 K) :
    mul first (add second third) = add (mul first second) (mul first third) := by
  ext <;> unfold mul add <;> ring1

/-- Matrix multiplication distributes over subtraction in its left argument. -/
theorem mul_sub_left (first second third : Matrix3 K) :
    mul (sub first second) third =
      sub (mul first third) (mul second third) := by
  ext <;> unfold mul sub <;> ring1

/-- Matrix multiplication distributes over subtraction in its right argument. -/
theorem mul_sub_right (first second third : Matrix3 K) :
    mul first (sub second third) =
      sub (mul first second) (mul first third) := by
  ext <;> unfold mul sub <;> ring1

/-- Cancellation for the explicit coordinatewise subtraction operation. -/
theorem eq_of_sub_eq_zero {left right : Matrix3 K}
    (differenceZero : sub left right = zero) : left = right := by
  calc
    left = add (sub left right) right := by
      ext <;> unfold add sub <;> ring1
    _ = add zero right := by rw [differenceZero]
    _ = right := by
      ext <;> unfold add zero <;> ring1

/-- Scaling the left factor scales its matrix product. -/
theorem mul_scale_left (scalar : K) (left right : Matrix3 K) :
    mul (scale scalar left) right = scale scalar (mul left right) := by
  ext <;> unfold mul scale <;> ring1

/-- Scaling the right factor scales its matrix product. -/
theorem mul_scale_right (scalar : K) (left right : Matrix3 K) :
    mul left (scale scalar right) = scale scalar (mul left right) := by
  ext <;> unfold mul scale <;> ring1

/-- Successive matrix scalings multiply their scalars. -/
theorem scale_scale (first second : K) (matrix : Matrix3 K) :
    scale first (scale second matrix) = scale (first * second) matrix := by
  ext <;> unfold scale <;> ring1

/-- Scaling a displayed matrix by one preserves it. -/
@[simp] theorem one_scale (matrix : Matrix3 K) : scale 1 matrix = matrix := by
  ext <;> unfold scale <;> ring1

/-- Scaling distributes over displayed matrix addition. -/
theorem scale_add (scalar : K) (left right : Matrix3 K) :
    scale scalar (add left right) =
      add (scale scalar left) (scale scalar right) := by
  ext <;> unfold scale add <;> ring1

/-- An equality of a matrix sum isolates its first summand by subtraction. -/
theorem eq_sub_of_add_eq {left right result : Matrix3 K}
    (equal : add left right = result) : left = sub result right := by
  rw [← equal]
  ext <;> unfold add sub <;> ring1

/-- A nonzero scalar cancels from the left of an equality of scalar products. -/
private theorem scalar_eq_of_mul_eq_mul_left {scalar left right : K}
    (scalarNonzero : scalar ≠ 0) (equal : scalar * left = scalar * right) :
    left = right := by
  have cancel : scalar * scalar⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel scalar scalarNonzero
  calc
    left = (scalar * scalar⁻¹) * left := by rw [cancel, one_mul]
    _ = scalar⁻¹ * (scalar * left) := by ring1
    _ = scalar⁻¹ * (scalar * right) := by rw [equal]
    _ = (scalar * scalar⁻¹) * right := by ring1
    _ = right := by rw [cancel, one_mul]

/-- Cancel an explicitly nonzero scalar from a coordinatewise matrix scale. -/
theorem eq_of_scale_eq_scale {scalar : K} (scalarNonzero : scalar ≠ 0)
    {left right : Matrix3 K} (equal : scale scalar left = scale scalar right) :
    left = right := by
  apply Matrix3.ext
  · exact scalar_eq_of_mul_eq_mul_left scalarNonzero
      (congrArg Matrix3.tt equal)
  · exact scalar_eq_of_mul_eq_mul_left scalarNonzero
      (congrArg Matrix3.tr equal)
  · exact scalar_eq_of_mul_eq_mul_left scalarNonzero
      (congrArg Matrix3.ts equal)
  · exact scalar_eq_of_mul_eq_mul_left scalarNonzero
      (congrArg Matrix3.rt equal)
  · exact scalar_eq_of_mul_eq_mul_left scalarNonzero
      (congrArg Matrix3.rr equal)
  · exact scalar_eq_of_mul_eq_mul_left scalarNonzero
      (congrArg Matrix3.rs equal)
  · exact scalar_eq_of_mul_eq_mul_left scalarNonzero
      (congrArg Matrix3.st equal)
  · exact scalar_eq_of_mul_eq_mul_left scalarNonzero
      (congrArg Matrix3.sr equal)
  · exact scalar_eq_of_mul_eq_mul_left scalarNonzero
      (congrArg Matrix3.ss equal)

/-- Negating both displayed matrix factors preserves their product. -/
theorem mul_neg_neg (left right : Matrix3 K) :
    mul (neg left) (neg right) = mul left right := by
  ext <;> unfold mul neg <;> ring1

/-- The identity matrix preserves every displayed row vector. -/
@[simp] theorem rowMul_identity (vector : Vector K) :
    rowMul vector identity = vector := by
  ext <;> unfold rowMul identity <;> ring1

/-- Equality of displayed matrices is determined by their action on the three
displayed coordinate rows. -/
theorem eq_of_rowMul_eq (left right : Matrix3 K)
    (equal : ∀ vector : Vector K, rowMul vector left = rowMul vector right) :
    left = right := by
  have first := equal (⟨1, 0, 0⟩ : Vector K)
  have second := equal (⟨0, 1, 0⟩ : Vector K)
  have third := equal (⟨0, 0, 1⟩ : Vector K)
  apply Matrix3.ext
  · simpa [rowMul] using congrArg Vector.t first
  · simpa [rowMul] using congrArg Vector.r first
  · simpa [rowMul] using congrArg Vector.s first
  · simpa [rowMul] using congrArg Vector.t second
  · simpa [rowMul] using congrArg Vector.r second
  · simpa [rowMul] using congrArg Vector.s second
  · simpa [rowMul] using congrArg Vector.t third
  · simpa [rowMul] using congrArg Vector.r third
  · simpa [rowMul] using congrArg Vector.s third

/-- Row-vector action respects the order of matrix multiplication. -/
theorem rowMul_mul (vector : Vector K) (left right : Matrix3 K) :
    rowMul (rowMul vector left) right = rowMul vector (mul left right) := by
  ext <;> unfold rowMul mul <;> ring1

/-- Row-vector action distributes over matrix addition. -/
theorem rowMul_add (vector : Vector K) (left right : Matrix3 K) :
    rowMul vector (add left right) =
      Vector.add (rowMul vector left) (rowMul vector right) := by
  ext <;> unfold rowMul add Vector.add <;> ring1

/-- Row-vector action distributes over matrix subtraction. -/
theorem rowMul_sub (vector : Vector K) (left right : Matrix3 K) :
    rowMul vector (sub left right) =
      Vector.sub (rowMul vector left) (rowMul vector right) := by
  ext <;> unfold rowMul sub Vector.sub <;> ring1

/-- Row multiplication preserves addition of its input vectors. -/
theorem rowMul_vector_add (left right : Vector K) (matrix : Matrix3 K) :
    rowMul (Vector.add left right) matrix = Vector.add (rowMul left matrix) (rowMul right matrix) := by
  ext <;> unfold rowMul Vector.add <;> ring1

/-- Row multiplication preserves subtraction of its input vectors. -/
theorem rowMul_vector_sub (left right : Vector K) (matrix : Matrix3 K) :
    rowMul (Vector.sub left right) matrix = Vector.sub (rowMul left matrix) (rowMul right matrix) := by
  ext <;> unfold rowMul Vector.sub <;> ring1

/-- Row multiplication preserves scalar multiplication of its input vector. -/
theorem rowMul_vector_scale (scalar : K) (vector : Vector K) (matrix : Matrix3 K) :
    rowMul (Vector.scale scalar vector) matrix = Vector.scale scalar (rowMul vector matrix) := by
  ext <;> unfold rowMul Vector.scale <;> ring1

/-- Scaling a matrix scales its action on a row vector. -/
theorem rowMul_scale (vector : Vector K) (scalar : K) (matrix : Matrix3 K) :
    rowMul vector (scale scalar matrix) =
      Vector.scale scalar (rowMul vector matrix) := by
  ext <;> unfold rowMul scale Vector.scale <;> ring1

/-- Negating a matrix negates its action on a row vector. -/
theorem rowMul_neg (vector : Vector K) (matrix : Matrix3 K) :
    rowMul vector (neg matrix) = Vector.neg (rowMul vector matrix) := by
  ext <;> unfold rowMul neg Vector.neg <;> ring1

/-- Acting by an outer product scales its second vector by the dot product with its first. -/
theorem rowMul_outer (vector column row : Vector K) :
    rowMul vector (outer column row) =
      Vector.scale (Vector.dot vector column) row := by
  ext <;> unfold rowMul outer Vector.scale Vector.dot <;> ring1

/-- Transposing an outer product exchanges its two vectors. -/
theorem outer_transpose (column row : Vector K) :
    transpose (outer column row) = outer row column := by
  ext <;> unfold transpose outer <;> ring1

/-- Scaling both vectors scales their outer product by the product of their scalars. -/
theorem outer_scale_both (scalar : K) (vector : Vector K) :
    outer (Vector.scale scalar vector) (Vector.scale scalar vector) =
      scale (scalar ^ 2) (outer vector vector) := by
  ext <;> unfold outer Vector.scale scale <;> ring1

/-- Multiplication of two displayed rank-one outer products. -/
theorem mul_outer (firstRow firstColumn secondRow secondColumn : Vector K) :
    mul (outer firstRow firstColumn) (outer secondRow secondColumn) =
      scale (Vector.dot firstColumn secondRow)
        (outer firstRow secondColumn) := by
  ext <;> unfold mul outer scale Vector.dot <;> ring1

/-- The rank-one matrix identity for a cross product, kept entirely in
displayed three-dimensional coordinates. -/
theorem outer_cross_self (left right : Vector K) :
    outer (Vector.cross left right) (Vector.cross left right) =
      add
        (sub
          (sub
            (scale
              (left.quadrance * right.quadrance -
                Vector.dot left right ^ 2)
              identity)
            (scale right.quadrance (outer left left)))
          (scale left.quadrance (outer right right)))
        (scale (Vector.dot left right)
          (add (outer left right) (outer right left))) := by
  ext <;> unfold outer Vector.cross Vector.quadrance Vector.dot add sub
    scale identity <;> ring1

/-- Exchanging the two matrix factors preserves the trace of their product. -/
theorem trace_mul_comm (left right : Matrix3 K) :
    trace (mul left right) = trace (mul right left) := by
  unfold trace mul
  ring1

/-- Transposing a displayed matrix preserves its trace. -/
theorem trace_transpose (matrix : Matrix3 K) :
    trace (transpose matrix) = trace matrix := by
  rfl

/-- The trace of a displayed sum is the sum of the traces. -/
theorem trace_add (left right : Matrix3 K) :
    trace (add left right) = trace left + trace right := by
  unfold trace add
  ring1

/-- Scaling a matrix scales its trace. -/
theorem trace_scale (scalar : K) (matrix : Matrix3 K) :
    trace (scale scalar matrix) = scalar * trace matrix := by
  unfold trace scale
  ring1

/-- The displayed three-dimensional identity has trace three. -/
@[simp] theorem trace_identity : trace (identity : Matrix3 K) = 3 := by
  unfold trace identity
  ring1

/-- The trace of an outer product is the dot product of its two vectors. -/
theorem trace_outer (row column : Vector K) :
    trace (outer row column) = Vector.dot row column := by
  unfold trace outer Vector.dot
  ring1

/-- The finite three-dimensional Newton identity for the trace of a square. -/
theorem trace_square (matrix : Matrix3 K) :
    trace (mul matrix matrix) =
      trace matrix ^ 2 - 2 * principalTrace matrix := by
  unfold principalTrace adjugate trace mul
  ring1

/-- Transposing a displayed matrix preserves its determinant. -/
theorem determinant_transpose (matrix : Matrix3 K) :
    determinant (transpose matrix) = determinant matrix := by
  unfold determinant transpose
  ring1

/-- Negating a three-dimensional matrix negates its determinant. -/
theorem determinant_neg (matrix : Matrix3 K) :
    determinant (neg matrix) = -determinant matrix := by
  unfold determinant neg
  ring1

/-- Scaling a three-dimensional matrix multiplies its determinant by the scalar cubed. -/
theorem determinant_scale (scalar : K) (matrix : Matrix3 K) :
    determinant (scale scalar matrix) =
      scalar ^ 3 * determinant matrix := by
  unfold determinant scale
  ring1

/-- The displayed identity matrix has determinant one. -/
@[simp] theorem determinant_identity :
    determinant (identity : Matrix3 K) = 1 := by
  unfold determinant identity
  ring1

/-- The determinant of a displayed matrix product is the product of the determinants. -/
theorem determinant_mul (left right : Matrix3 K) :
    determinant (mul left right) = determinant left * determinant right := by
  unfold determinant mul
  ring1

/-- Determinant of a quadratic polynomial in one displayed three-by-three
matrix, expressed through its three characteristic coefficients. -/
theorem determinant_quadratic_polynomial (matrix : Matrix3 K)
    (constant linear quadratic : K) :
    determinant
        (add
          (add (scale constant identity) (scale linear matrix))
          (scale quadratic (mul matrix matrix))) =
      constant ^ 3 +
        constant ^ 2 * linear * trace matrix +
        constant ^ 2 * quadratic *
          (trace matrix ^ 2 - 2 * principalTrace matrix) +
        constant * linear ^ 2 * principalTrace matrix +
        constant * linear * quadratic *
          (trace matrix * principalTrace matrix -
            3 * determinant matrix) +
        constant * quadratic ^ 2 *
          (principalTrace matrix ^ 2 -
            2 * trace matrix * determinant matrix) +
        linear ^ 3 * determinant matrix +
        linear ^ 2 * quadratic * trace matrix * determinant matrix +
        linear * quadratic ^ 2 * principalTrace matrix *
          determinant matrix +
        quadratic ^ 3 * determinant matrix ^ 2 := by
  unfold determinant add scale identity mul principalTrace trace adjugate
  ring1

/-- Multiply a skew resolvent by a quadratic polynomial in the same matrix.

The quadratic terms cancel, leaving only the identity, linear and cubic
terms. No spectral or invertibility condition is required.
-/
theorem resolvent_mul_quadratic (matrix : Matrix3 K) (coefficient : K) :
    mul (sub identity matrix)
        (add identity (scale coefficient (add matrix (mul matrix matrix)))) =
      sub (add identity (scale (coefficient - 1) matrix))
        (scale coefficient (mul (mul matrix matrix) matrix)) := by
  ext <;> unfold mul sub add scale identity <;> ring1

/-- Multiply a quadratic polynomial by the resolvent of the same matrix.

The identity, linear and cubic terms agree with the reverse product because
both factors are polynomials in the retained matrix.
-/
theorem quadratic_mul_resolvent (matrix : Matrix3 K) (coefficient : K) :
    mul (add identity (scale coefficient (add matrix (mul matrix matrix))))
        (sub identity matrix) =
      sub (add identity (scale (coefficient - 1) matrix))
        (scale coefficient (mul (mul matrix matrix) matrix)) := by
  ext <;> unfold mul sub add scale identity <;> ring1

/-- The direct adjugate certificate, requiring no matrix inverse operation. -/
theorem mul_adjugate (matrix : Matrix3 K) :
    mul matrix (adjugate matrix) = scale (determinant matrix) identity := by
  ext <;> unfold mul adjugate scale determinant identity <;> ring1

/-- The matching adjugate certificate with the adjugate on the left. -/
theorem adjugate_mul (matrix : Matrix3 K) :
    mul (adjugate matrix) matrix = scale (determinant matrix) identity := by
  ext <;> unfold mul adjugate scale determinant identity <;> ring1

/-- The adjugate as the quadratic coefficient expression used in the
three-dimensional Cayley--Hamilton calculation. -/
theorem adjugate_expansion (matrix : Matrix3 K) :
    adjugate matrix =
      add (sub (mul matrix matrix) (scale (trace matrix) matrix))
        (scale (principalTrace matrix) identity) := by
  ext <;> unfold add sub mul scale principalTrace trace adjugate identity <;>
    ring1

/-- The cube of a displayed matrix satisfies its cubic characteristic relation.

The finite adjugate multiplication and expansion certificates give the
Cayley–Hamilton equality without a generic polynomial or spectral argument.
-/
theorem cubic_characteristic (matrix : Matrix3 K) :
    mul (mul matrix matrix) matrix =
      add (sub (scale (trace matrix) (mul matrix matrix))
        (scale (principalTrace matrix) matrix)) (scale (determinant matrix) identity) := by
  have product : mul matrix (adjugate matrix) =
      add (sub (mul (mul matrix matrix) matrix)
        (scale (trace matrix) (mul matrix matrix))) (scale (principalTrace matrix) matrix) := by
    rw [adjugate_expansion, mul_add_right, mul_sub_right,
      mul_scale_right, mul_scale_right, mul_identity, ← mul_assoc]
  calc
    _ = add (sub (scale (trace matrix) (mul matrix matrix))
        (scale (principalTrace matrix) matrix))
        (add (sub (mul (mul matrix matrix) matrix)
          (scale (trace matrix) (mul matrix matrix))) (scale (principalTrace matrix) matrix)) := by
      ext <;> unfold add sub scale <;> ring1
    _ = _ := by rw [← product, mul_adjugate]

/-- Cubing a displayed matrix minus identity gives its finite binomial expansion. -/
theorem cube_sub_identity (matrix : Matrix3 K) :
    mul (mul (sub matrix identity) (sub matrix identity)) (sub matrix identity) =
      sub (add (sub (mul (mul matrix matrix) matrix) (scale 3 (mul matrix matrix)))
        (scale 3 matrix)) identity := by
  ext <;> unfold mul sub add scale identity <;> ring1

/-- Executable inverse of a displayed matrix with nonzero determinant. -/
@[expose] def inverse (matrix : Matrix3 K) (_determinantNonzero : determinant matrix ≠ 0) :
    Matrix3 K :=
  scale (1 / determinant matrix) (adjugate matrix)

/-- The displayed adjugate inverse is a right inverse when the determinant is nonzero. -/
theorem mul_inverse (matrix : Matrix3 K)
    (determinantNonzero : determinant matrix ≠ 0) :
    mul matrix (inverse matrix determinantNonzero) = identity := by
  have cancel := ExplicitField.mul_inv_cancel
    (determinant matrix) determinantNonzero
  unfold inverse
  rw [mul_scale_right, mul_adjugate, scale_scale]
  have coefficient :
      (1 / determinant matrix) * determinant matrix = (1 : K) := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      1 * (determinant matrix)⁻¹ * determinant matrix =
          determinant matrix * (determinant matrix)⁻¹ := by ring1
      _ = 1 := cancel
  rw [coefficient]
  ext <;> unfold scale identity <;> ring1

/-- The displayed adjugate inverse is a left inverse when the determinant is nonzero. -/
theorem inverse_mul (matrix : Matrix3 K)
    (determinantNonzero : determinant matrix ≠ 0) :
    mul (inverse matrix determinantNonzero) matrix = identity := by
  have cancel := ExplicitField.mul_inv_cancel
    (determinant matrix) determinantNonzero
  unfold inverse
  rw [mul_scale_left, adjugate_mul, scale_scale]
  have coefficient :
      (1 / determinant matrix) * determinant matrix = (1 : K) := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      1 * (determinant matrix)⁻¹ * determinant matrix =
          determinant matrix * (determinant matrix)⁻¹ := by ring1
      _ = 1 := cancel
  rw [coefficient]
  ext <;> unfold scale identity <;> ring1

/-- Over a nontrivial explicit field, a displayed right inverse of a square
matrix is also a left inverse. -/
theorem inverse_mul_of_mul_eq_identity (oneNonzero : (1 : K) ≠ 0)
    {matrix inverseMatrix : Matrix3 K}
    (rightInverse : mul matrix inverseMatrix = identity) :
    mul inverseMatrix matrix = identity := by
  have determinantProduct := congrArg determinant rightInverse
  rw [determinant_mul, determinant_identity] at determinantProduct
  have determinantNonzero : determinant matrix ≠ 0 := by
    intro determinantZero
    apply oneNonzero
    calc
      1 = determinant matrix * determinant inverseMatrix :=
        determinantProduct.symm
      _ = 0 := by rw [determinantZero, zero_mul]
  have inverseValue : inverseMatrix = inverse matrix determinantNonzero := by
    calc
      inverseMatrix = mul identity inverseMatrix := by
        rw [identity_mul]
      _ = mul (mul (inverse matrix determinantNonzero) matrix)
          inverseMatrix := by
        rw [inverse_mul]
      _ = mul (inverse matrix determinantNonzero)
          (mul matrix inverseMatrix) := by
        rw [mul_assoc]
      _ = inverse matrix determinantNonzero := by
        rw [rightInverse, mul_identity]
  rw [inverseValue, inverse_mul]

/-- Finite coefficient expansion of `det(XI-A)`. -/
theorem characteristicValue_expansion (matrix : Matrix3 K) (X : K) :
    characteristicValue matrix X =
      X ^ 3 - trace matrix * X ^ 2 + principalTrace matrix * X -
        determinant matrix := by
  unfold characteristicValue determinant sub scale identity principalTrace trace
    adjugate
  ring1

/-- Orthogonality in the paper's row-vector convention. -/
@[expose] def IsOrthogonal (matrix : Matrix3 K) : Prop :=
  mul matrix (transpose matrix) = identity

/-- The finite coordinate predicate defining `SO(3)`. -/
@[expose] def IsSpecialOrthogonal (matrix : Matrix3 K) : Prop :=
  IsOrthogonal matrix ∧ determinant matrix = 1

/-- Move a displayed matrix action across the dot product by transposing it. -/
theorem dot_rowMul_transpose (first second : Vector K) (matrix : Matrix3 K) :
    Vector.dot (rowMul first matrix) second =
      Vector.dot first (rowMul second (transpose matrix)) := by
  unfold Vector.dot rowMul transpose
  ring1

/-- An explicitly orthogonal matrix preserves the displayed dot product. -/
theorem dot_rowMul_of_isOrthogonal {matrix : Matrix3 K}
    (orthogonal : IsOrthogonal matrix) (first second : Vector K) :
    Vector.dot (rowMul first matrix) (rowMul second matrix) =
      Vector.dot first second := by
  calc
    Vector.dot (rowMul first matrix) (rowMul second matrix) =
        Vector.dot first
          (rowMul (rowMul second matrix) (transpose matrix)) :=
      dot_rowMul_transpose first (rowMul second matrix) matrix
    _ = Vector.dot first
        (rowMul second (mul matrix (transpose matrix))) := by
          rw [rowMul_mul]
    _ = Vector.dot first (rowMul second identity) := by rw [orthogonal]
    _ = Vector.dot first second := by rw [rowMul_identity]

/-- Orthogonal matrix action preserves vector quadrance. -/
theorem quadrance_rowMul_of_isOrthogonal {matrix : Matrix3 K}
    (orthogonal : IsOrthogonal matrix) (vector : Vector K) :
    Vector.quadrance (rowMul vector matrix) = Vector.quadrance vector := by
  unfold Vector.quadrance
  exact dot_rowMul_of_isOrthogonal orthogonal vector vector

/-- A product of two explicitly orthogonal matrices is orthogonal. -/
theorem isOrthogonal_mul {left right : Matrix3 K}
    (leftOrthogonal : IsOrthogonal left)
    (rightOrthogonal : IsOrthogonal right) :
    IsOrthogonal (mul left right) := by
  unfold IsOrthogonal at leftOrthogonal rightOrthogonal ⊢
  rw [transpose_mul]
  calc
    mul (mul left right) (mul (transpose right) (transpose left)) =
        mul left (mul (mul right (transpose right)) (transpose left)) := by
          rw [mul_assoc, mul_assoc]
    _ = mul left (mul identity (transpose left)) := by
      rw [rightOrthogonal]
    _ = mul left (transpose left) := by rw [identity_mul]
    _ = identity := leftOrthogonal

/-- A product of special orthogonal matrices is special orthogonal. -/
theorem isSpecialOrthogonal_mul {left right : Matrix3 K}
    (leftSpecial : IsSpecialOrthogonal left)
    (rightSpecial : IsSpecialOrthogonal right) :
    IsSpecialOrthogonal (mul left right) := by
  constructor
  · exact isOrthogonal_mul leftSpecial.1 rightSpecial.1
  · rw [determinant_mul, leftSpecial.2, rightSpecial.2, one_mul]

end Matrix3

end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3.Matrix3

variable {K : Type*} [ExplicitField K]

/-- Adding a zero scalar multiple of a matrix leaves the identity unchanged. -/
public theorem zero_scale_add_identity (matrix : Matrix3 K) :
    add identity (scale 0 matrix) =
      identity := by
  ext <;> unfold add scale identity <;> ring1

end Purelib.LinearAlgebra.Coordinates3.Matrix3
end

end

section
open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3
namespace Purelib.LinearAlgebra.Coordinates3.Matrix3
variable {K : Type*}

/-- Symmetry identifies the displayed `(r,t)` and `(t,r)` entries. -/
public theorem symmetric_rt_eq_tr (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric) : matrix.rt = matrix.tr := by
  have coordinate := congrArg Coordinates3.Matrix3.tr symmetric
  unfold transpose at coordinate
  exact coordinate

/-- Symmetry identifies the displayed `(s,t)` and `(t,s)` entries. -/
public theorem symmetric_st_eq_ts (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric) : matrix.st = matrix.ts := by
  have coordinate := congrArg Coordinates3.Matrix3.ts symmetric
  unfold transpose at coordinate
  exact coordinate

/-- Symmetry identifies the displayed `(s,r)` and `(r,s)` entries. -/
public theorem symmetric_sr_eq_rs (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric) : matrix.sr = matrix.rs := by
  have coordinate := congrArg Coordinates3.Matrix3.rs symmetric
  unfold transpose at coordinate
  exact coordinate

end Purelib.LinearAlgebra.Coordinates3.Matrix3
end
