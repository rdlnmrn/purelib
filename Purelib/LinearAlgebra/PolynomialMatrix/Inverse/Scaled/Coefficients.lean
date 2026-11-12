module

public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Evaluation
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Mathlib.Algebra.Group.Defs
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Checked polynomial coefficients of two-sided scaled matrix products -/

public section

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Coefficients

open Purelib
open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic (ScaledInverseData)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

variable {K : Type*} [ExplicitField K] [DecidableEq K] {n : Nat}

/-- Every original bounded entry difference has the zero normalized coefficient table. -/
abbrev PolynomialMatrixIdentity (left right : PolynomialMatrix.Basic.Matrix K n) : Prop :=
  ∀ row column, (left row column - right row column).isZero = true

/-- The same retained inverse data satisfies both scaled product identities at every scalar argument. -/
abbrev Specializations (matrix : PolynomialMatrix.Basic.Matrix K n) (data : ScaledInverseData K n) : Prop :=
  ∀ point, SquareMatrix.Multiplication.mul (PolynomialMatrix.Evaluation.evalMatrix point data.inverse)
      (PolynomialMatrix.Evaluation.evalMatrix point matrix) =
      SquareMatrix.Multiplication.scaleIdentity (data.scalar.eval point) ∧
    SquareMatrix.Multiplication.mul (PolynomialMatrix.Evaluation.evalMatrix point matrix)
      (PolynomialMatrix.Evaluation.evalMatrix point data.inverse) =
      SquareMatrix.Multiplication.scaleIdentity (data.scalar.eval point)

/-- A finite zero-coefficient comparison implies equality of the same evaluated structural matrices. -/
private theorem evaluateIdentity {left right : PolynomialMatrix.Basic.Matrix K n}
    (identity : PolynomialMatrixIdentity left right) (point : K) :
    PolynomialMatrix.Evaluation.evalMatrix point left = PolynomialMatrix.Evaluation.evalMatrix point right := by
  apply SquareMatrix.matrix_ext
  intro row column
  rewrite [PolynomialMatrix.Evaluation.evalMatrix_apply, PolynomialMatrix.Evaluation.evalMatrix_apply]
  have zero := DensePolynomial.eval_eq_zero_of_isZero (identity row column) point
  rewrite [DensePolynomial.eval_sub] at zero
  have reconstruction :
      ((left row column).eval point - (right row column).eval point) +
        (right row column).eval point = (left row column).eval point := by
    rewrite [SubNegMonoid.sub_eq_add_neg, add_assoc, AddGroup.neg_add_cancel,
      AddZeroClass.add_zero]
    rfl
  exact reconstruction.symm.trans
    ((congrArg (· + (right row column).eval point) zero).trans
      (AddZeroClass.zero_add _))

set_option genInjectivity false in
/-- The actual cached left/right products and scalar identity of one original polynomial matrix and retained inverse.

Both finite coefficient comparisons concern these same cached products. Their
readback laws identify the complete original multiplication records, so the
specialized inverse laws do not rebuild a polynomial inverse producer.
-/
structure Products (matrix : PolynomialMatrix.Basic.Matrix K n) (data : ScaledInverseData K n) where
  /-- The actual retained inverse-times-input polynomial product. -/ left : PolynomialMatrix.Basic.Matrix K n
  /-- This cache uses the same retained inverse and original matrix. -/ left_eq :
    left = PolynomialMatrix.Basic.mul data.inverse matrix
  /-- The actual retained input-times-inverse polynomial product. -/ right : PolynomialMatrix.Basic.Matrix K n
  /-- This cache uses the same original matrix and retained inverse. -/ right_eq :
    right = PolynomialMatrix.Basic.mul matrix data.inverse
  /-- The actual retained polynomial identity scaled by this same scalar. -/ identity :
    PolynomialMatrix.Basic.Matrix K n
  /-- The identity cache is scaled by the same retained scalar polynomial. -/ identity_eq :
    identity = PolynomialMatrix.Basic.scaleIdentity data.scalar
  /-- Every left product coefficient difference is zero. -/ left_identity : PolynomialMatrixIdentity left identity
  /-- Every right product coefficient difference is zero. -/ right_identity : PolynomialMatrixIdentity right identity

constructive_injectivity Products

namespace Products

/-- Both checked original coefficient products specialize to the same retained two-sided inverse identities. -/
theorem specializations {matrix : PolynomialMatrix.Basic.Matrix K n} {data : ScaledInverseData K n}
    (products : Products matrix data) : Specializations matrix data := by
  intro point
  constructor
  · have equal := evaluateIdentity products.left_identity point
    rewrite [products.left_eq, products.identity_eq, PolynomialMatrix.Evaluation.eval_matrixMul,
      PolynomialMatrix.Evaluation.eval_scaleIdentity] at equal
    exact equal
  · have equal := evaluateIdentity products.right_identity point
    rewrite [products.right_eq, products.identity_eq, PolynomialMatrix.Evaluation.eval_matrixMul,
      PolynomialMatrix.Evaluation.eval_scaleIdentity] at equal
    exact equal

end Products

set_option genInjectivity false in
/-- A proved failed coefficient product of the same original matrix and proposed inverse data.

The failure retains both actual product records and their defining equations.
It identifies the violated left or right coefficient identity; it asserts no
invalidity of the original matrix and no global pole or divergence.
-/
inductive Invalid (matrix : PolynomialMatrix.Basic.Matrix K n) (data : ScaledInverseData K n) where
  /-- The actual inverse-times-input product fails the same retained scalar identity. -/
  | left (product identity : PolynomialMatrix.Basic.Matrix K n)
      (product_eq : product = PolynomialMatrix.Basic.mul data.inverse matrix)
      (identity_eq : identity = PolynomialMatrix.Basic.scaleIdentity data.scalar)
      (failed : ¬ PolynomialMatrixIdentity product identity)
  /-- The actual input-times-inverse product fails the same retained scalar identity. -/
  | right (product identity : PolynomialMatrix.Basic.Matrix K n)
      (product_eq : product = PolynomialMatrix.Basic.mul matrix data.inverse)
      (identity_eq : identity = PolynomialMatrix.Basic.scaleIdentity data.scalar)
      (failed : ¬ PolynomialMatrixIdentity product identity)

constructive_injectivity Invalid

/-- Compute each original product once and return its complete coefficient certificates or retained failure.

No determinant, recursive inverse or root producer is called by this checker.
All comparisons range over the original bounded row and column indices.
-/
def check (matrix : PolynomialMatrix.Basic.Matrix K n) (data : ScaledInverseData K n) :
    Except (Invalid matrix data) (Products matrix data) :=
  let left := PolynomialMatrix.Basic.mul data.inverse matrix
  let identity := PolynomialMatrix.Basic.scaleIdentity data.scalar
  if first : PolynomialMatrixIdentity left identity then
    let right := PolynomialMatrix.Basic.mul matrix data.inverse
    if second : PolynomialMatrixIdentity right identity then
      .ok ⟨left, rfl, right, rfl, identity, rfl, first, second⟩
    else .error (.right right identity rfl rfl second)
  else .error (.left left identity rfl rfl first)

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Coefficients

end
