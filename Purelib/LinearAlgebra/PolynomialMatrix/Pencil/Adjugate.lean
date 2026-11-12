module

public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Polynomial.Dense.Arithmetic

/-!
# Retained characteristic and adjugate coefficient proposals

A finite trace recurrence computes one scalar coefficient and one structural
matrix at each original dimension step. Every matrix is retained before its
entries are assembled into dense polynomials. Exact original pencil product
and monic-degree checks certify the result separately, including fields where
one of the integer denominators vanishes.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Pencil.Adjugate

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic (ScaledInverseData)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

variable {K : Type*} [ExplicitField K] [DecidableEq K] {n : Nat}

/-- Retain the remaining scalar coefficients and successive adjugate matrices of one original input.

The structural remaining-step count controls termination. The current matrix
is reused in the actual product, and the computed product is shared by its
trace and next matrix; neither is recomputed per polynomial entry.
-/
private def collect (matrix : SquareMatrix K n) :
    Nat → Nat → SquareMatrix K n → List K × List (SquareMatrix K n)
  | 0, _, _ => ([], [])
  | remaining + 1, completed, current =>
      let product := SquareMatrix.Multiplication.mul matrix current
      let coefficient := -(sumFin fun index => product index index) / ((Int.ofNat (completed + 1) : Int) : K)
      let next := SquareMatrix.add product (SquareMatrix.Multiplication.scaleIdentity coefficient)
      let tail := collect matrix remaining (completed + 1) next
      (coefficient :: tail.1, current :: tail.2)

/-- Compute a degree-generic characteristic scalar and polynomial adjugate proposal from the original matrix.

The original dimension determines exactly how many cached trace steps are
performed. The output is executable proposed data, without a successful
producer assumption; original coefficient checks and typed rejection certify
or reject it separately. All supplied field characteristics remain admitted.
-/
public def compute (matrix : SquareMatrix K n) : ScaledInverseData K n :=
  let retained := collect matrix n 0 SquareMatrix.Multiplication.identity
  let scalar : DensePolynomial K := ⟨1 :: retained.1⟩
  let inverse := SquareMatrix.matrixOfFn fun row column =>
    (⟨retained.2.map fun coefficient => coefficient row column⟩ : DensePolynomial K).normalize
  ⟨scalar.normalize, inverse⟩

end Purelib.LinearAlgebra.PolynomialMatrix.Pencil.Adjugate
