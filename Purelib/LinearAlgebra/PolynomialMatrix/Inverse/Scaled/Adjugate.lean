module

public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.Polynomial.Dense.Arithmetic

/-! # Trace proposals for scaled inverses of finite polynomial matrices -/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Adjugate

open Purelib
open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic (ScaledInverseData)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

variable {K : Type*} [ExplicitField K] [DecidableEq K] {n : Nat}

/-- Retain successive polynomial matrix products in a structurally bounded trace recurrence.

The scalar division uses only the displayed integer in the coefficient field.
The last current matrix and negated trace coefficient form proposed scaled
inverse data; exact coefficient checks certify or reject that proposal.
-/
private def collect (matrix : PolynomialMatrix.Basic.Matrix K n) :
    Nat → Nat → PolynomialMatrix.Basic.Matrix K n → ScaledInverseData K n
  | 0, _, current => ⟨DensePolynomial.constant 1, current⟩
  | remaining + 1, completed, current =>
      let product := PolynomialMatrix.Basic.mul matrix current
      let reciprocal := ((Int.ofNat (completed + 1) : Int) : K)⁻¹
      let coefficient := DensePolynomial.scale (-reciprocal)
        (PolynomialMatrix.Basic.sumFin fun index => product index index)
      match remaining with
      | 0 => ⟨-coefficient, current⟩
      | count + 1 =>
          let next := SquareMatrix.matrixOfFn fun row column =>
            product row column + if row = column then coefficient else 0
          collect matrix (count + 1) (completed + 1) next

/-- Compute a finite trace proposal for the original polynomial matrix's scaled inverse.

The original dimension bounds the recurrence. Every product is retained before
its trace and next matrix are read, and no inverse polynomial is used as a
divisor. This executable proposal carries no unchecked success assertion;
the complete original coefficient-product checker supplies its certificate.
-/
public def compute (matrix : PolynomialMatrix.Basic.Matrix K n) : ScaledInverseData K n :=
  collect matrix n 0 (PolynomialMatrix.Basic.scaleIdentity (DensePolynomial.constant 1))

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Adjugate
