module

public import Purelib.Polynomial.Dense.Companion
public import Purelib.LinearAlgebra.Matrix.Tensor
import Purelib.Data.Fin
import Purelib.LinearAlgebra.PolynomialMatrix.Pencil
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained polynomial evidence for sums and products of original roots

Each operation retains both original polynomial companions, its actual tensor
matrix and the same computed pencil data. The input polynomial equations
derive the output equation; no desired result polynomial or successful branch
selection is supplied. Original-channel residual bounds and branch selection
are separate consumers of this finite algebraic construction.
-/

public section

namespace Purelib.Polynomial.Dense.Companion

open Purelib
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext)

set_option genInjectivity false in
/-- The scalar operation represented by the corresponding original tensor operator. -/
inductive Operation where
  /-- The tensor sum represents addition of the original eigenvalues. -/
  | add
  /-- The tensor product represents multiplication of the original eigenvalues. -/
  | mul

constructive_injectivity Operation

namespace Operation

/-- Compute the selected scalar operation on its two original scalar inputs. -/
@[expose] def value {K : Type*} [CommRing K] (operation : Operation) (first second : K) : K :=
  match operation with
  | .add => first + second
  | .mul => first * second

/-- Build the selected tensor operator from the same two original structural matrices. -/
def matrix {K : Type*} [CommRing K] {leftSize rightSize : Nat} (operation : Operation)
    (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize) :
    SquareMatrix K (leftSize * rightSize) :=
  match operation with
  | .add => SquareMatrix.Tensor.sum first second
  | .mul => SquareMatrix.Tensor.product first second

/-- The actual original eigenvector inputs give an eigenvector for their selected scalar operation. -/
theorem eigenvector {K : Type*} [CommRing K] {leftSize rightSize : Nat} (operation : Operation)
    (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize)
    (left : Data.Vector K leftSize) (right : Data.Vector K rightSize) (leftValue rightValue : K)
    (leftEigen : ∀ row, SquareMatrix.Multiplication.matrixVector first left row = leftValue * left row)
    (rightEigen : ∀ row, SquareMatrix.Multiplication.matrixVector second right row = rightValue * right row)
    (row : Fin (leftSize * rightSize)) :
    SquareMatrix.Multiplication.matrixVector (operation.matrix first second)
      (SquareMatrix.Tensor.vector left right) row =
      operation.value leftValue rightValue * SquareMatrix.Tensor.vector left right row := by
  cases operation with
  | add =>
      exact SquareMatrix.Tensor.sum_eigenvector first second left right leftValue rightValue
        leftEigen rightEigen row
  | mul =>
      exact SquareMatrix.Tensor.product_eigenvector first second left right leftValue rightValue
        leftEigen rightEigen row

/-- Combine both original scalar-vector residuals for the selected sum or product. -/
@[expose] def residual {K : Type*} [CommRing K] (operation : Operation)
    (firstValue secondValue firstVector secondVector firstResidual secondResidual : K) : K :=
  match operation with
  | .add => firstResidual * secondVector + firstVector * secondResidual
  | .mul => firstResidual * secondValue * secondVector + firstValue * firstVector * secondResidual -
      firstResidual * secondResidual

/-- The selected tensor action transports both original residuals at their actual bounded row pair. -/
theorem action_residual {K : Type*} [CommRing K] {leftSize rightSize : Nat} (operation : Operation)
    (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize)
    (left : Data.Vector K leftSize) (right : Data.Vector K rightSize) (leftValue rightValue : K)
    (row : Fin (leftSize * rightSize)) :
    operation.value leftValue rightValue * SquareMatrix.Tensor.vector left right row -
        SquareMatrix.Multiplication.matrixVector (operation.matrix first second)
          (SquareMatrix.Tensor.vector left right) row =
      operation.residual leftValue rightValue (left (Data.Fin.divNat row)) (right (Data.Fin.modNat row))
        (leftValue * left (Data.Fin.divNat row) -
          SquareMatrix.Multiplication.matrixVector first left (Data.Fin.divNat row))
        (rightValue * right (Data.Fin.modNat row) -
          SquareMatrix.Multiplication.matrixVector second right (Data.Fin.modNat row)) := by
  cases operation with
  | add =>
      change _ - SquareMatrix.Multiplication.matrixVector (SquareMatrix.Tensor.sum first second) _ _ = _
      rewrite [SquareMatrix.Tensor.sum_action, SquareMatrix.Tensor.vector_apply]
      dsimp only [value, residual]
      ring0
  | mul =>
      change _ - SquareMatrix.Multiplication.matrixVector (SquareMatrix.Tensor.product first second) _ _ = _
      rewrite [SquareMatrix.Tensor.product_action, SquareMatrix.Tensor.vector_apply]
      dsimp only [value, residual]
      ring0

end Operation

variable {K : Type*} [ExplicitField K] [DecidableEq K]
variable {firstPolynomial secondPolynomial : DensePolynomial K}

set_option genInjectivity false in
/-- Both original polynomial companions with one actual computed arithmetic operator and its cached polynomial evidence.

Each retained input is the same original complete companion, including its
source, coefficient table, feedback and matrix. The operator and pencil caches
refer to those same original matrices; they do not replace either input owner.
-/
structure Elimination (operation : Operation) (originalFirst : Companion firstPolynomial)
    (originalSecond : Companion secondPolynomial)
    where
  /-- The complete retained original first companion. -/
  first : Companion firstPolynomial
  /-- The first cache is the original nominal input. -/
  first_eq : first = originalFirst
  /-- The complete retained original second companion. -/
  second : Companion secondPolynomial
  /-- The second cache is the original nominal input. -/
  second_eq : second = originalSecond
  /-- The actual cached selected tensor operator at the original product dimension. -/
  matrix : SquareMatrix K (firstPolynomial.natDegree * secondPolynomial.natDegree)
  /-- The cached operator was built from the retained original input matrices. -/
  matrix_eq : matrix = operation.matrix first.matrix second.matrix
  /-- The actual computed pencil coefficients and inverse data of this same cached operator. -/
  pencil : Pencil.Certificate matrix

constructive_injectivity Elimination

namespace Elimination

/-- Compute the selected original tensor operator and its polynomial evidence once, retaining both input companions. -/
def ofCompanions [Nontrivial K] (operation : Operation)
    (first : Companion firstPolynomial) (second : Companion secondPolynomial) : Elimination operation first second :=
  let matrix := operation.matrix first.matrix second.matrix
  let pencil := Pencil.prepare matrix
  ⟨first, rfl, second, rfl, matrix, rfl, pencil⟩

/-- Read the same cached arithmetic pencil polynomial. -/
@[expose] def polynomial {operation : Operation} {first : Companion firstPolynomial}
    {second : Companion secondPolynomial}
    (elimination : Elimination operation first second) : DensePolynomial K := elimination.pencil.polynomial

/-- The actual computed arithmetic polynomial is nonzero. -/
theorem nonzero {operation : Operation} {first : Companion firstPolynomial} {second : Companion secondPolynomial}
    (elimination : Elimination operation first second) : elimination.polynomial.isZero = false :=
  elimination.pencil.nonzero

/-- The actual computed arithmetic polynomial has positive degree at its original product dimension. -/
theorem degree_pos {operation : Operation} {first : Companion firstPolynomial} {second : Companion secondPolynomial}
    (elimination : Elimination operation first second) : 0 < elimination.polynomial.natDegree :=
  elimination.pencil.degree_pos (Nat.mul_pos first.positive second.positive)

/-- The cached arithmetic pencil residual is the selected combination of both original polynomial residuals.

The two original power vectors and actual tensor row pair are retained. This
identity holds at every pair of scalar readings without assuming either input
is an exact root, so later quantitative bounds can consume the actual errors.
-/
theorem source_residual {operation : Operation} {first : Companion firstPolynomial}
    {second : Companion secondPolynomial} (elimination : Elimination operation first second)
    (firstPoint secondPoint : K) (row : Fin (firstPolynomial.natDegree * secondPolynomial.natDegree)) :
    operation.value firstPoint secondPoint *
        SquareMatrix.Tensor.vector (elimination.first.powers firstPoint) (elimination.second.powers secondPoint) row -
        SquareMatrix.Multiplication.matrixVector elimination.matrix
          (SquareMatrix.Tensor.vector (elimination.first.powers firstPoint)
            (elimination.second.powers secondPoint)) row =
      operation.residual firstPoint secondPoint
        (elimination.first.powers firstPoint (Data.Fin.divNat row))
        (elimination.second.powers secondPoint (Data.Fin.modNat row))
        (elimination.first.residual firstPoint (Data.Fin.divNat row))
        (elimination.second.residual secondPoint (Data.Fin.modNat row)) := by
  rewrite [elimination.matrix_eq, operation.action_residual,
    elimination.first.action firstPoint (Data.Fin.divNat row),
    elimination.second.action secondPoint (Data.Fin.modNat row)]
  dsimp only [Companion.residual]
  have firstError : firstPoint * elimination.first.powers firstPoint (Data.Fin.divNat row) -
      (firstPoint * elimination.first.powers firstPoint (Data.Fin.divNat row) -
        (if (Data.Fin.divNat row).val + 1 = firstPolynomial.natDegree then
          firstPolynomial.eval firstPoint * elimination.first.leadingInverse else 0)) =
      (if (Data.Fin.divNat row).val + 1 = firstPolynomial.natDegree then
        firstPolynomial.eval firstPoint * elimination.first.leadingInverse else 0) := by ring0
  have secondError : secondPoint * elimination.second.powers secondPoint (Data.Fin.modNat row) -
      (secondPoint * elimination.second.powers secondPoint (Data.Fin.modNat row) -
        (if (Data.Fin.modNat row).val + 1 = secondPolynomial.natDegree then
          secondPolynomial.eval secondPoint * elimination.second.leadingInverse else 0)) =
      (if (Data.Fin.modNat row).val + 1 = secondPolynomial.natDegree then
        secondPolynomial.eval secondPoint * elimination.second.leadingInverse else 0) := by ring0
  rewrite [firstError, secondError]
  rfl

/-- The actual arithmetic polynomial reading is the cached inverse action on both original source residuals.

The same bounded first pair supplies the retained tensor unit component. Each
inverse coefficient is read from the stored pencil data at the actual result
reading. The original polynomial errors and power readings remain explicit,
so quantitative consumers need no supplied output-zero equation.
-/
theorem polynomial_residual {operation : Operation} {first : Companion firstPolynomial}
    {second : Companion secondPolynomial} (elimination : Elimination operation first second)
    (firstPoint secondPoint : K) :
    elimination.polynomial.eval (operation.value firstPoint secondPoint) =
      SquareMatrix.Multiplication.matrixVector
        (Evaluation.evalMatrix (operation.value firstPoint secondPoint) elimination.pencil.data.inverse)
        (vectorOfFn fun row : Fin (firstPolynomial.natDegree * secondPolynomial.natDegree) =>
          operation.residual firstPoint secondPoint
            (elimination.first.powers firstPoint (Data.Fin.divNat row))
            (elimination.second.powers secondPoint (Data.Fin.modNat row))
            (elimination.first.residual firstPoint (Data.Fin.divNat row))
            (elimination.second.residual secondPoint (Data.Fin.modNat row)))
        (Fin.mkDivMod elimination.first.firstIndex elimination.second.firstIndex) := by
  let powers := SquareMatrix.Tensor.vector (elimination.first.powers firstPoint)
    (elimination.second.powers secondPoint)
  let index := Fin.mkDivMod elimination.first.firstIndex elimination.second.firstIndex
  have unit : powers index = 1 := by
    rewrite [SquareMatrix.Tensor.vector_pair, powers_first, powers_first, mul_one]
    rfl
  have scalar := elimination.pencil.residual_component (operation.value firstPoint secondPoint) powers index
  rewrite [unit, mul_one] at scalar
  have originalResidual :
      vectorOfFn (fun row => operation.value firstPoint secondPoint * powers row -
        SquareMatrix.Multiplication.matrixVector elimination.matrix powers row) =
      vectorOfFn (fun row : Fin (firstPolynomial.natDegree * secondPolynomial.natDegree) =>
        operation.residual firstPoint secondPoint
          (elimination.first.powers firstPoint (Data.Fin.divNat row))
          (elimination.second.powers secondPoint (Data.Fin.modNat row))
          (elimination.first.residual firstPoint (Data.Fin.divNat row))
          (elimination.second.residual secondPoint (Data.Fin.modNat row))) := by
    apply vector_ext
    intro row
    rewrite [vectorOfFn_apply, vectorOfFn_apply]
    exact elimination.source_residual firstPoint secondPoint row
  exact scalar.trans (congrArg (fun residual => SquareMatrix.Multiplication.matrixVector
    (Evaluation.evalMatrix (operation.value firstPoint secondPoint) elimination.pencil.data.inverse) residual index)
      originalResidual)

/-- The original input equations derive the cached polynomial equation for their selected scalar sum or product.

The actual tensor vector retains both original power-vector inputs and their
bounded first coordinates. Its unit component and the selected original
operator provide the cached pencil's eigenvalue-zero certificate.
-/
theorem source_zero {operation : Operation} {first : Companion firstPolynomial} {second : Companion secondPolynomial}
    (elimination : Elimination operation first second) (firstPoint secondPoint : K)
    (firstRoot : firstPolynomial.eval firstPoint = 0) (secondRoot : secondPolynomial.eval secondPoint = 0) :
    elimination.polynomial.eval (operation.value firstPoint secondPoint) = 0 := by
  let left := elimination.first.powers firstPoint
  let right := elimination.second.powers secondPoint
  let index := Fin.mkDivMod elimination.first.firstIndex elimination.second.firstIndex
  have unit : SquareMatrix.Tensor.vector left right index = 1 := by
    rewrite [SquareMatrix.Tensor.vector_pair, powers_first, powers_first, mul_one]
    rfl
  apply elimination.pencil.eigenvalue_zero (operation.value firstPoint secondPoint)
    (SquareMatrix.Tensor.vector left right) index unit
  intro row
  rewrite [elimination.matrix_eq]
  exact operation.eigenvector elimination.first.matrix elimination.second.matrix left right firstPoint secondPoint
    (elimination.first.eigenvector firstPoint firstRoot) (elimination.second.eigenvector secondPoint secondRoot) row

end Elimination

end Purelib.Polynomial.Dense.Companion

end
