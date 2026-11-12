module

public import Purelib.LinearAlgebra.Matrix.Schur
public import Purelib.LinearAlgebra.Matrix.Triangular
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Tactic.Ring

/-!
# One retained unit-pivot reduction

A specific inverse of the original leading coefficient produces actual source
and target changes with retained inverse certificates. Their transformed matrix
is one leading identity coordinate followed by the cached original Schur tail.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Schur

open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Inverse.Scaled.Basic

variable {K : Type*} [CommRing K] {rows columns : Nat}

/-- The actual lower and transposed lower factors reduce the original leading unit.

Both off-diagonal columns come from the original matrix. The complete matrix
identity retains the same specific leading inverse and fraction-free Schur
rectangle, including both independent tail dimensions.
-/
theorem unit_factor (matrix : Rectangular K (rows + 1) (columns + 1))
    (inverse : K) (unit : Blocks.head matrix * inverse = 1) :
    Blocks.diagonal 1 (schur matrix) =
      Rectangular.mul
        (Rectangular.mul
          (Triangular.lower inverse (Vec.map Neg.neg (Blocks.leftColumn matrix)) (Blocks.head matrix))
          matrix)
        (Rectangular.transpose (Triangular.lower 1
          (vectorOfFn fun column => -inverse * Blocks.topRow matrix column) 1)) := by
  have reverseUnit : inverse * matrix 0 0 = 1 := (mul_comm _ _).trans unit
  apply Blocks.ext
  · rw [Blocks.diagonal_zero_zero, Triangular.mul_transpose_lower_zero,
      Triangular.lower_mul_zero, one_mul]
    exact reverseUnit.symm
  · intro column
    rw [Blocks.diagonal_zero_succ, Triangular.mul_transpose_lower_succ,
      Triangular.lower_mul_zero, Triangular.lower_mul_zero, vectorOfFn_apply,
      Blocks.topRow_apply, reverseUnit]
    ring0
  · intro row
    rw [Blocks.diagonal_succ_zero, Triangular.mul_transpose_lower_zero,
      Triangular.lower_mul_succ, map_apply, Blocks.leftColumn_apply, one_mul]
    change 0 = -matrix row.succ 0 * matrix 0 0 + matrix 0 0 * matrix row.succ 0
    ring0
  · intro row column
    rw [Blocks.diagonal_succ_succ, Triangular.mul_transpose_lower_succ,
      Triangular.lower_mul_succ, Triangular.lower_mul_succ,
      vectorOfFn_apply, map_apply, Blocks.leftColumn_apply,
      schur_apply, Blocks.leftColumn_apply, Blocks.topRow_apply, Blocks.tail_apply]
    change matrix 0 0 * matrix row.succ column.succ - matrix row.succ 0 * matrix 0 column.succ =
      (-inverse * matrix 0 column.succ) *
        (-matrix row.succ 0 * matrix 0 0 + matrix 0 0 * matrix row.succ 0) +
      1 * (-matrix row.succ 0 * matrix 0 column.succ + matrix 0 0 * matrix row.succ column.succ)
    ring0

set_option genInjectivity false in
/-- One unit pivot with its actual coordinate changes and retained original residual.

The original nonempty rectangle indexes every certificate. Both coordinate
changes retain the original scaled-inverse owner at scalar one, and the same
cached Schur rectangle is the next finite reduction problem.
-/
structure UnitReduction (matrix : Rectangular K (rows + 1) (columns + 1)) where
  /-- The retained specific inverse of the original leading coefficient. -/
  leadingInverse : K
  /-- Multiplication of that original leading coefficient and this inverse is one. -/
  leading_unit : Blocks.head matrix * leadingInverse = 1
  /-- The actual retained source change. -/
  source : SquareMatrix K (columns + 1)
  /-- The original inverse certificate of the retained source change. -/
  sourceInverse : ScaledInverse source
  /-- The retained source certificate has scalar one. -/
  source_scalar : sourceInverse.scalar = 1
  /-- The actual retained target change. -/
  target : SquareMatrix K (rows + 1)
  /-- The original inverse certificate of the retained target change. -/
  targetInverse : ScaledInverse target
  /-- The retained target certificate has scalar one. -/
  target_scalar : targetInverse.scalar = 1
  /-- The retained next rectangle after removing the leading identity coordinate. -/
  residual : Rectangular K rows columns
  /-- The retained residual is the original fraction-free Schur rectangle. -/
  residual_eq : residual = schur matrix
  /-- The actual original coordinate product has this leading identity and retained residual. -/
  reduction : Blocks.diagonal 1 residual = Rectangular.mul (Rectangular.mul target matrix) source

constructive_injectivity UnitReduction

namespace UnitReduction

/-- Construct one actual unit-pivot reduction using its specific leading inverse.

The original top row and left column are materialized once. Their transformed
columns feed the same retained triangular factors and their inverse builders;
the original Schur rectangle is computed and cached once.
-/
@[expose] def build (matrix : Rectangular K (rows + 1) (columns + 1))
    (inverse : K) (unit : Blocks.head matrix * inverse = 1) : UnitReduction matrix :=
  let leading := Blocks.head matrix
  let top := Blocks.topRow matrix
  let left := Blocks.leftColumn matrix
  let sourceColumn := vectorOfFn fun column => -inverse * top column
  let targetColumn := Vec.map Neg.neg left
  let sourceBase := Triangular.lower 1 sourceColumn 1
  let target := Triangular.lower inverse targetColumn leading
  let sourceBaseInverse := Triangular.lowerInverse 1 1 sourceColumn 1 (one_mul 1) 1 (one_mul 1)
  let targetInverse := Triangular.lowerInverse inverse leading targetColumn leading
    ((mul_comm _ _).trans unit) inverse unit
  let source := Rectangular.transpose sourceBase
  let sourceInverse := ScaledInverse.transpose sourceBaseInverse
  let residual := schur matrix
  { leadingInverse := inverse
    leading_unit := unit
    source := source
    sourceInverse := sourceInverse
    source_scalar := rfl
    target := target
    targetInverse := targetInverse
    target_scalar := rfl
    residual := residual
    residual_eq := rfl
    reduction := unit_factor matrix inverse unit }

end UnitReduction

end Purelib.LinearAlgebra.Matrix.Schur

end
