module

import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic

universe u
variable {K : Type*} [CommRing K]

set_option genInjectivity false in
/-- A retained matrix inverse up to one common scalar on both sides.

The original square matrix determines the dimension and coefficient ring; both product identities refer to the same
cached inverse and scalar. -/
structure ScaledInverse {n : Nat} (matrix :
  SquareMatrix K n) where
  /-- The common scalar in both inverse product identities. -/ scalar : K
  /-- The retained square inverse matrix with the original dimension. -/ inverse : SquareMatrix K n
  /-- The retained inverse times the original matrix is the scalar identity. -/ left_identity :
    SquareMatrix.Multiplication.mul inverse matrix = SquareMatrix.Multiplication.scaleIdentity scalar
  /-- The original matrix times the retained inverse is the scalar identity. -/ right_identity :
    SquareMatrix.Multiplication.mul matrix inverse = SquareMatrix.Multiplication.scaleIdentity scalar

constructive_injectivity ScaledInverse

end Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic

end

public section

namespace Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic.ScaledInverse

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero)
open Purelib
open Purelib.Data.Vector.Basic (vectorOfFn_apply)

variable {K : Type*} [CommRing K] {n : Nat} {matrix : SquareMatrix K n}

/-- The original scaled inverse transports a matrix action to scalar multiplication of each original vector component.

The left product identity is applied to the same structural vector and bounded
component index. It retains the actual matrix action even when that action is
nonzero, so residual bounds can be transported without scalar division.
-/
theorem action_component (inverse : ScaledInverse matrix) (vector : Data.Vector K n) (row : Fin n) :
    inverse.scalar * vector row = SquareMatrix.Multiplication.matrixVector inverse.inverse
      (SquareMatrix.Multiplication.matrixVector matrix vector) row := by
  calc
    _ = SquareMatrix.Multiplication.matrixVector
        (SquareMatrix.Multiplication.scaleIdentity inverse.scalar) vector row := by
      rw [SquareMatrix.Multiplication.matrixVector_scaleIdentity, vectorOfFn_apply]
    _ = SquareMatrix.Multiplication.matrixVector
        (SquareMatrix.Multiplication.mul inverse.inverse matrix) vector row :=
      congrArg (fun operator => SquareMatrix.Multiplication.matrixVector operator vector row)
        inverse.left_identity.symm
    _ = _ := congrArg (fun result => result row)
      (SquareMatrix.Multiplication.matrixVector_mul inverse.inverse matrix vector)

/-- A scaled inverse annihilates each component of an original kernel vector after multiplication by its scalar.

The left scaled-inverse identity is applied to the same original vector. Each
component of its original matrix action is zero; no scalar division or
nonvanishing hypothesis is required.
-/
theorem kernel_component (inverse : ScaledInverse matrix) (vector : Data.Vector K n)
    (kernel : ∀ row, SquareMatrix.Multiplication.matrixVector matrix vector row = 0) (row : Fin n) :
    inverse.scalar * vector row = 0 := by
  calc
    _ = SquareMatrix.Multiplication.matrixVector inverse.inverse
        (SquareMatrix.Multiplication.matrixVector matrix vector) row := inverse.action_component vector row
    _ = sumFin (fun column => inverse.inverse row column *
        SquareMatrix.Multiplication.matrixVector matrix vector column) :=
      SquareMatrix.Multiplication.matrixVector_apply _ _ _
    _ = sumFin (fun _ : Fin n => (0 : K)) :=
      sumFin_congr fun column =>
        (congrArg (fun entry => inverse.inverse row column * entry) (kernel column)).trans (mul_zero _)
    _ = 0 := sumFin_zero

/-- A kernel vector with a displayed unit component forces the same scaled-inverse scalar to be zero.

The original bounded index and unit reading supply the exact nonzero component.
The conclusion uses multiplication by one, without a field inverse or a
choice of a normalization index.
-/
theorem scalar_zero_of_kernel_unit (inverse : ScaledInverse matrix) (vector : Data.Vector K n)
    (kernel : ∀ row, SquareMatrix.Multiplication.matrixVector matrix vector row = 0)
    (index : Fin n) (unit : vector index = 1) : inverse.scalar = 0 := by
  have product := inverse.kernel_component vector kernel index
  rewrite [unit, mul_one] at product
  exact product

end Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic.ScaledInverse

end
