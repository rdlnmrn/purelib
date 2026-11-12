module

import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.Matrix.Triangular.Inverse

/-!
# Triangular inverse construction over a ring with zero divisors

The original square-zero quadratic coordinate gives distinct diagonal units.
Both triangular constructors retain the exact expected finite inverse table.
-/

namespace TestPurelib.LinearAlgebra.Matrix.Triangular

open Purelib.Algebra.Quadratic
open Purelib.Data.Vector.Basic
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

/-- The original quadratic coefficient ring with a square-zero generator. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- The original nonzero nilpotent coordinate. -/
private def epsilon : Dual := Pair.generator

/-- A triangular matrix with different diagonal units in the same zero-divisor ring. -/
private def matrix : SquareMatrix Dual 2 := matrixOfFn fun row column =>
  if row.val = 0 then if column.val = 0 then 1 + epsilon else 2
  else if column.val = 0 then 0 else 1 - epsilon

/-- The retained inverses of its two distinct original diagonal entries. -/
private def diagonalInverses : Purelib.Data.Vector Dual 2 :=
  .cons (1 - epsilon) (.cons (1 + epsilon) .nil)

/-- The displayed matrix is upper triangular at both original finite coordinates. -/
private theorem upper : Triangular.IsUpper matrix := by
  unfold Triangular.IsUpper
  decide +kernel

/-- Both retained diagonal inverses multiply their original entries to one. -/
private theorem units : ∀ index : Fin 2, matrix index index * diagonalInverses index = 1 := by decide +kernel

/-- The actual upper builder retains the independently calculated inverse entries. -/
private theorem upper_entries : ∀ row column : Fin 2,
    (Triangular.inverseUpper matrix upper diagonalInverses units).val.inverse row column =
      if row.val = 0 then if column.val = 0 then 1 - epsilon else -2
      else if column.val = 0 then 0 else 1 + epsilon := by decide +kernel

/-- The original transposed matrix is lower triangular at the same finite coordinates. -/
private theorem lower : Triangular.IsLower (Rectangular.transpose matrix) := by
  unfold Triangular.IsLower
  decide +kernel

/-- Its original transposed diagonal has those same retained scalar units. -/
private theorem transpose_units : ∀ index : Fin 2,
    Rectangular.transpose matrix index index * diagonalInverses index = 1 := by decide +kernel

/-- The actual lower builder retains the independently calculated transposed inverse entries. -/
private theorem lower_entries : ∀ row column : Fin 2,
    (Triangular.inverseLower (Rectangular.transpose matrix) lower diagonalInverses transpose_units).val.inverse
      row column =
      if column.val = 0 then if row.val = 0 then 1 - epsilon else -2
      else if row.val = 0 then 0 else 1 + epsilon := by decide +kernel

end TestPurelib.LinearAlgebra.Matrix.Triangular
