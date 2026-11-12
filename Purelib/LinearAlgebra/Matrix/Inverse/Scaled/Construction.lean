module

public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
public import Purelib.LinearAlgebra.Matrix.Blocks.Border
public import Purelib.LinearAlgebra.Matrix.Arithmetic

/-!
# Construction of retained inverses at scalar one

The original inverse record retains both multiplication identities. Identity,
composition and diagonal extension preserve those same original caches.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic

open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K]

namespace ScaledInverse

/-- Reverse the same retained inverse relation at scalar one.

The original source matrix becomes the retained inverse of the original
cached inverse matrix. Both product identities exchange without recomputing
either original matrix.
-/
@[expose] def symm {dimension : Nat} {matrix : SquareMatrix K dimension}
    (inverse : ScaledInverse matrix) (unit : inverse.scalar = 1) : ScaledInverse inverse.inverse where
  scalar := 1
  inverse := matrix
  left_identity := inverse.right_identity.trans (congrArg Multiplication.scaleIdentity unit)
  right_identity := inverse.left_identity.trans (congrArg Multiplication.scaleIdentity unit)

/-- The original scalar identity at one is its own retained inverse. -/
@[expose] def identity (dimension : Nat) :
    ScaledInverse (SquareMatrix.Multiplication.scaleIdentity (n := dimension) (1 : K)) where
  scalar := 1
  inverse := SquareMatrix.Multiplication.scaleIdentity 1
  left_identity := SquareMatrix.Multiplication.unit_mul _
  right_identity := SquareMatrix.Multiplication.unit_mul _

/-- Compose two retained actual inverses in reverse order.

Both inputs have scalar one. The original matrix product indexes the result,
and its retained inverse uses the same two cached inverse matrices.
-/
@[expose] def mul {dimension : Nat} {left right : SquareMatrix K dimension}
    (leftInverse : ScaledInverse left) (leftUnit : leftInverse.scalar = 1)
    (rightInverse : ScaledInverse right) (rightUnit : rightInverse.scalar = 1) :
    ScaledInverse (SquareMatrix.Multiplication.mul left right) where
  scalar := 1
  inverse := SquareMatrix.Multiplication.mul rightInverse.inverse leftInverse.inverse
  left_identity := by
    rw [SquareMatrix.Multiplication.mul_assoc,
      ← SquareMatrix.Multiplication.mul_assoc leftInverse.inverse left right,
      leftInverse.left_identity, leftUnit, SquareMatrix.Multiplication.unit_mul,
      rightInverse.left_identity, rightUnit]
  right_identity := by
    rw [← SquareMatrix.Multiplication.mul_assoc,
      SquareMatrix.Multiplication.mul_assoc left right rightInverse.inverse,
      rightInverse.right_identity, rightUnit, SquareMatrix.Multiplication.mul_unit,
      leftInverse.right_identity, leftUnit]

/-- Original finite powers of two mutually inverse matrices remain mutually inverse. -/
private theorem power_product_unit {dimension : Nat} (left right : SquareMatrix K dimension)
    (leftRight : Multiplication.mul left right = Multiplication.scaleIdentity 1)
    (rightLeft : Multiplication.mul right left = Multiplication.scaleIdentity 1) (count : Nat) :
    Multiplication.mul (Arithmetic.power left count) (Arithmetic.power right count) =
      Multiplication.scaleIdentity 1 := by
  induction count with
  | zero => rw [Arithmetic.power_zero, Arithmetic.power_zero, Multiplication.unit_mul]
  | succ count previous =>
      rw [Arithmetic.power_succ, Arithmetic.power_succ,
        Multiplication.mul_assoc (Arithmetic.power left count) left,
        ← Multiplication.mul_assoc left (Arithmetic.power right count) right,
        Arithmetic.commute_power left right (leftRight.trans rightLeft.symm) count,
        Multiplication.mul_assoc (Arithmetic.power right count) left right,
        ← Multiplication.mul_assoc (Arithmetic.power left count) (Arithmetic.power right count),
        previous, leftRight, Multiplication.unit_mul]

/-- Powers of the same retained inverse multiply the original matrix powers to the original unit on the left. -/
theorem power_left_identity {dimension : Nat} {matrix : SquareMatrix K dimension}
    (inverse : ScaledInverse matrix) (unit : inverse.scalar = 1) (count : Nat) :
    Multiplication.mul (Arithmetic.power inverse.inverse count) (Arithmetic.power matrix count) =
      Multiplication.scaleIdentity 1 :=
  power_product_unit inverse.inverse matrix
    (inverse.left_identity.trans (congrArg Multiplication.scaleIdentity unit))
    (inverse.right_identity.trans (congrArg Multiplication.scaleIdentity unit)) count

/-- Original matrix powers multiply the powers of their same retained inverse to the original unit on the right. -/
theorem power_right_identity {dimension : Nat} {matrix : SquareMatrix K dimension}
    (inverse : ScaledInverse matrix) (unit : inverse.scalar = 1) (count : Nat) :
    Multiplication.mul (Arithmetic.power matrix count) (Arithmetic.power inverse.inverse count) =
      Multiplication.scaleIdentity 1 :=
  power_product_unit matrix inverse.inverse
    (inverse.right_identity.trans (congrArg Multiplication.scaleIdentity unit))
    (inverse.left_identity.trans (congrArg Multiplication.scaleIdentity unit)) count

/-- Retain the original finite power of a matrix's same cached inverse.

Both powers use the original successive matrix-product traversal. The same
retained two-sided inverse identities certify their products at scalar one;
no field or recomputed scalar inverse is used.
-/
@[expose] def power {dimension : Nat} {matrix : SquareMatrix K dimension}
    (inverse : ScaledInverse matrix) (unit : inverse.scalar = 1) (count : Nat) :
    ScaledInverse (Arithmetic.power matrix count) where
  scalar := 1
  inverse := Arithmetic.power inverse.inverse count
  left_identity := inverse.power_left_identity unit count
  right_identity := inverse.power_right_identity unit count

/-- Extend an actual retained inverse by a leading identity coordinate.

The original tail matrix and its cached inverse are reused by the diagonal
extensions. Both successor-dimensional identities retain scalar one.
-/
@[expose] def diagonal {dimension : Nat} {matrix : SquareMatrix K dimension}
    (inverse : ScaledInverse matrix) (unit : inverse.scalar = 1) :
    ScaledInverse (Blocks.diagonal 1 matrix) where
  scalar := 1
  inverse := Blocks.diagonal 1 inverse.inverse
  left_identity := by
    change Rectangular.mul (Blocks.diagonal 1 inverse.inverse) (Blocks.diagonal 1 matrix) = _
    rw [Blocks.diagonal_mul, one_mul]
    have tailIdentity : Rectangular.mul inverse.inverse matrix = Multiplication.scaleIdentity 1 :=
      inverse.left_identity.trans (congrArg Multiplication.scaleIdentity unit)
    rw [tailIdentity]
    exact Blocks.diagonal_unit dimension
  right_identity := by
    change Rectangular.mul (Blocks.diagonal 1 matrix) (Blocks.diagonal 1 inverse.inverse) = _
    rw [Blocks.diagonal_mul, one_mul]
    have tailIdentity : Rectangular.mul matrix inverse.inverse = Multiplication.scaleIdentity 1 :=
      inverse.right_identity.trans (congrArg Multiplication.scaleIdentity unit)
    rw [tailIdentity]
    exact Blocks.diagonal_unit dimension

/-- Transpose the same original matrix and its retained scaled inverse together.

The common scalar is preserved. The original left and right identities exchange
under the shared finite transposed-product law.
-/
@[expose] def transpose {dimension : Nat} {matrix : SquareMatrix K dimension}
    (inverse : ScaledInverse matrix) : ScaledInverse (Rectangular.transpose matrix) where
  scalar := inverse.scalar
  inverse := Rectangular.transpose inverse.inverse
  left_identity := by
    change Rectangular.mul (Rectangular.transpose inverse.inverse) (Rectangular.transpose matrix) = _
    rw [← Rectangular.transpose_mul]
    exact (congrArg Rectangular.transpose inverse.right_identity).trans
      (Rectangular.transpose_scaleIdentity inverse.scalar)
  right_identity := by
    change Rectangular.mul (Rectangular.transpose matrix) (Rectangular.transpose inverse.inverse) = _
    rw [← Rectangular.transpose_mul]
    exact (congrArg Rectangular.transpose inverse.left_identity).trans
      (Rectangular.transpose_scaleIdentity inverse.scalar)

end ScaledInverse

end Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic

end
