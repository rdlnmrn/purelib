module
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
import Purelib.Polynomial.Dense.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Polynomial.Dense.Multiplication

open Purelib.Algebra.Field

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Total fraction-free recursion.  Nonvanishing of its scalar is proved
separately from leading-term data for the particular Sylvester matrix. -/
def Inverse.Scaled.Compute.scaledInverseData : (n : Nat) →
  PolynomialMatrix.Basic.Matrix K n → PolynomialMatrix.Inverse.Scaled.Basic.ScaledInverseData K n
  | 0, _ =>
      { scalar := Dense.Basic.DensePolynomial.constant 1
        inverse := SquareMatrix.matrixOfFn fun index =>
          Fin.elim0 index }
  | n + 1, matrix =>
      let smaller := Inverse.Scaled.Compute.scaledInverseData n
        (PolynomialMatrix.Basic.schur matrix)
      { scalar := PolynomialMatrix.Basic.head matrix * smaller.scalar
        inverse := PolynomialMatrix.Inverse.Scaled.Block.blockInverse matrix smaller }
end Purelib.LinearAlgebra.PolynomialMatrix

end
