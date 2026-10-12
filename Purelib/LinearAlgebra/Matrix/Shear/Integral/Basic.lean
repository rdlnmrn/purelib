module

import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Data.Int.Arithmetic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Tactic.Linter.Lint
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Integral unit-pivot changes of basis

The rows are executable finite data. A two-column shear has an explicit
inverse, and its congruence is computed by a quadratic entry formula rather
than by repeated matrix multiplication. No nondegeneracy is assumed for the
remaining matrix.
-/

namespace Purelib.LinearAlgebra.Matrix.Integral

variable {n : Nat}

set_option genInjectivity false in
/-- A shear fixes its two distinguished coordinates. -/
structure Shear (first last : Fin n) where
  /-- The retained integral correction coefficients for the first pivot. -/ left : Data.Vector Int n
  /-- The retained integral correction coefficients for the last pivot. -/ right : Data.Vector Int n
  /-- The first correction coefficient vanishes at the first pivot. -/ left_first : left first = 0
  /-- The first correction coefficient vanishes at the last pivot. -/ left_last : left last = 0
  /-- The second correction coefficient vanishes at the first pivot. -/ right_first : right first = 0
  /-- The second correction coefficient vanishes at the last pivot. -/ right_last : right last = 0

constructive_injectivity Shear

namespace Shear

variable {first last : Fin n}

/-- Apply the retained two-pivot integral shear to a structural vector.

Each output coordinate adds its two stored integer coefficients times the unchanged pivot coordinates. -/
def apply (shear :
  SquareMatrix.Integral.Shear first last) (values : Data.Vector Int n) :
    Data.Vector Int n :=
  Data.Vector.Basic.vectorOfFn fun index => values index + shear.left index * values first + shear.right index * values
    last

/-- Undo the retained two-pivot integral shear by subtracting its coordinate corrections. -/
def unapply (shear :
  SquareMatrix.Integral.Shear first last) (values : Data.Vector Int n) :
    Data.Vector Int n :=
  Data.Vector.Basic.vectorOfFn fun index => values index - shear.left index * values first - shear.right index * values
    last

/-- The shear fixes its first pivot coordinate. -/
theorem apply_first (shear :
  SquareMatrix.Integral.Shear first last) (values : Data.Vector Int n) :
    shear.apply values first = values first := by
  rw [SquareMatrix.Integral.Shear.apply, Data.Vector.Basic.vectorOfFn_apply, shear.left_first,
    shear.right_first, zero_mul, zero_mul, add_zero, add_zero]

/-- The shear fixes its last pivot coordinate. -/
theorem apply_last (shear :
  SquareMatrix.Integral.Shear first last) (values : Data.Vector Int n) :
    shear.apply values last = values last := by
  rw [SquareMatrix.Integral.Shear.apply, Data.Vector.Basic.vectorOfFn_apply, shear.left_last,
    shear.right_last, zero_mul, zero_mul, add_zero, add_zero]

/-- The inverse shear fixes its first pivot coordinate. -/
theorem unapply_first (shear :
  SquareMatrix.Integral.Shear first last) (values : Data.Vector Int n) :
    shear.unapply values first = values first := by
  rw [SquareMatrix.Integral.Shear.unapply, Data.Vector.Basic.vectorOfFn_apply, shear.left_first,
    shear.right_first, zero_mul, zero_mul, Data.Int.Arithmetic.sub_zero, Data.Int.Arithmetic.sub_zero]

/-- The inverse shear fixes its last pivot coordinate. -/
theorem unapply_last (shear :
  SquareMatrix.Integral.Shear first last) (values : Data.Vector Int n) :
    shear.unapply values last = values last := by
  rw [SquareMatrix.Integral.Shear.unapply, Data.Vector.Basic.vectorOfFn_apply, shear.left_last,
    shear.right_last, zero_mul, zero_mul, Data.Int.Arithmetic.sub_zero, Data.Int.Arithmetic.sub_zero]

/-- Applying a retained shear and then its inverse restores the original vector. -/
theorem unapply_apply (shear :
  SquareMatrix.Integral.Shear first last) (values : Data.Vector Int n) :
    shear.unapply (shear.apply values) = values := by
  apply Data.Vector.Basic.vector_ext; intro index
  rw [SquareMatrix.Integral.Shear.unapply, Data.Vector.Basic.vectorOfFn_apply, shear.apply_first,
    shear.apply_last, SquareMatrix.Integral.Shear.apply, Data.Vector.Basic.vectorOfFn_apply]
  ring1

/-- Applying the inverse shear and then the shear restores the original vector. -/
theorem apply_unapply (shear :
  SquareMatrix.Integral.Shear first last) (values : Data.Vector Int n) :
    shear.apply (shear.unapply values) = values := by
  apply Data.Vector.Basic.vector_ext; intro index
  rw [SquareMatrix.Integral.Shear.apply, Data.Vector.Basic.vectorOfFn_apply, shear.unapply_first,
    shear.unapply_last, SquareMatrix.Integral.Shear.unapply, Data.Vector.Basic.vectorOfFn_apply]
  ring1

/-- Materialize the integral basis matrix for the retained shear.

Each row is its coordinate unit plus the two cached pivot coefficients. -/
def basis (shear :
  SquareMatrix.Integral.Shear first last) : SquareMatrix.IntegralMatrix n :=
  SquareMatrix.matrixOfFn fun row column => (if column = row then 1 else 0) +
    (if column = first then shear.left row else 0) + (if column = last then shear.right row else 0)

/-- A coordinate-equality indicator selects the corresponding finite weighted term. -/
private theorem indicator_mul (target
  : Fin n) (coefficient : Int) (values : Fin n → Int) :
    FiniteSum.Fin.sumFin (fun index => (if index = target then coefficient else 0) * values index) =
      coefficient * values target := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index => if index = target then coefficient * values index else 0) := by
      apply FiniteSum.Fin.sumFin_congr; intro index
      by_cases equal : index = target
      · rw [if_pos equal, if_pos equal]
      · rw [if_neg equal, if_neg equal, zero_mul]
    _ = _ := FiniteSum.Fin.sumFin_ite_eq target _

/-- The weighted sum of one shear-basis row is its explicit two-pivot update. -/
theorem basis_sum (shear :
  SquareMatrix.Integral.Shear first last) (row : Fin n) (values : Fin n → Int) :
    FiniteSum.Fin.sumFin (fun index => shear.basis row index * values index) =
      values row + shear.left row * values first + shear.right row * values last := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index =>
        (if index = row then 1 else 0) * values index +
        (if index = first then shear.left row else 0) * values index +
        (if index = last then shear.right row else 0) * values index) := by
      apply FiniteSum.Fin.sumFin_congr; intro index
      rw [SquareMatrix.Integral.Shear.basis, SquareMatrix.matrixOfFn_apply, add_mul, add_mul]
    _ = _ := by
      rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_add,
        LinearAlgebra.Matrix.Integral.Shear.indicator_mul,
        LinearAlgebra.Matrix.Integral.Shear.indicator_mul,
        LinearAlgebra.Matrix.Integral.Shear.indicator_mul, one_mul]

/-- Multiplication by the retained basis matrix computes the shear action. -/
theorem matrixVector_basis (shear :
  SquareMatrix.Integral.Shear first last) (values : Data.Vector Int n) :
    SquareMatrix.Multiplication.matrixVector shear.basis values = shear.apply values := by
  apply Data.Vector.Basic.vector_ext; intro row
  rw [SquareMatrix.Multiplication.matrixVector_apply, shear.basis_sum, SquareMatrix.Integral.Shear.apply,
    Data.Vector.Basic.vectorOfFn_apply]

/-- Cached congruence entries; the double finite sum is a proof specification
only, never the executable implementation of a reduction step. -/
def transform (shear :
  SquareMatrix.Integral.Shear first last) (matrix : SquareMatrix.IntegralMatrix n) :
  SquareMatrix.IntegralMatrix n :=
  SquareMatrix.matrixOfFn fun row column =>
    matrix row column + shear.left row * matrix first column + shear.right row * matrix last column +
    shear.left column * (matrix row first + shear.left row * matrix first first + shear.right row * matrix last first) +
    shear.right column * (matrix row last + shear.left row * matrix first last + shear.right row * matrix last last)

/-- Read a transformed matrix entry by the cached two-pivot congruence formula. -/
theorem transform_apply (shear :
  SquareMatrix.Integral.Shear first last) (matrix : SquareMatrix.IntegralMatrix n) (row column : Fin
  n) :
    shear.transform matrix row column =
      matrix row column + shear.left row * matrix first column + shear.right row * matrix last column +
      shear.left column * (matrix row first + shear.left row * matrix first first + shear.right row * matrix last first)
        +
      shear.right column * (matrix row last + shear.left row * matrix first last + shear.right row * matrix last last)
        :=
  SquareMatrix.matrixOfFn_apply _ row column

/-- The cached matrix transformation equals the double finite sum for basis congruence.

Both factors use the same retained shear basis; the expanded formula certifies the cached entry computation. -/
theorem transform_eq (shear :
  SquareMatrix.Integral.Shear first last) (matrix : SquareMatrix.IntegralMatrix n) (row column : Fin
  n) :
    shear.transform matrix row column =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => shear.basis row i * matrix i j * shear.basis column
        j)) := by
  have inner (i : Fin n) :
      FiniteSum.Fin.sumFin (fun j => shear.basis row i * matrix i j * shear.basis column j) =
        shear.basis row i * (matrix i column + shear.left column * matrix i first + shear.right column * matrix i last)
          := by
    calc
      _ = shear.basis row i * FiniteSum.Fin.sumFin (fun j => shear.basis column j * matrix i j) := by
        rw [← FiniteSum.Fin.sumFin_mul_left]
        apply FiniteSum.Fin.sumFin_congr; intro j; ring1
      _ = _ := by rw [shear.basis_sum]
  rw [FiniteSum.Fin.sumFin_congr inner, shear.basis_sum, SquareMatrix.Integral.Shear.transform,
    SquareMatrix.matrixOfFn_apply]
  ring1

end Shear

end Purelib.LinearAlgebra.Matrix.Integral

end

public section
namespace Purelib.LinearAlgebra.Matrix.Integral.Shear
open Purelib

end Purelib.LinearAlgebra.Matrix.Integral.Shear
end
