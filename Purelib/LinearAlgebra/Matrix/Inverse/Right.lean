module

import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Tactic.Linter.Lint
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
-/

namespace Purelib.LinearAlgebra.Matrix.Inverse.Right

/-- An explicitly right-invertible matrix has a nonzero first row. -/
theorem row_nonzero_of_inverse (matrix inverse :
  LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (identity : SquareMatrix.Multiplication.mul matrix inverse =
      SquareMatrix.Multiplication.identity) :
    matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0 := open Purelib.Algebra in by
  by_cases first : matrix 0 0 = 0
  · right
    intro second
    have entry := congrArg (fun value : LinearAlgebra.Matrix.Basic.IntegralMatrix => value 0 0) identity
    simp only [SquareMatrix.Multiplication.mul_apply,
      FiniteSum.Fin.sumFin_two_int, first, second,
      MulZeroClass.zero_mul, _root_.add_zero] at entry
    exact (by decide : (0 : Int) ≠ 1) entry
  · exact Or.inl first
end Purelib.LinearAlgebra.Matrix.Inverse.Right

end

section
@[expose] public section

/-!
# Denominator preparation survives fractional composition

A preparation provider for all invertible integral matrices can be carried
through a prepared fractional action. An outer denominator is represented as
the quotient of the combined and inner denominators. Both are already apart;
one retained base state supplies a uniform upper bound for the divisor.
-/

namespace Purelib.LinearAlgebra.Matrix.Inverse.Right

set_option genInjectivity false in
/-- An executable right inverse is sufficient throughout. -/
structure RightInverse (matrix :
  LinearAlgebra.Matrix.Basic.IntegralMatrix) where
  /-- The retained integral matrix that multiplies on the right. -/ inverse :
    LinearAlgebra.Matrix.Basic.IntegralMatrix
  /-- The original matrix times the retained right inverse is the identity. -/ identity :
    SquareMatrix.Multiplication.mul matrix inverse =
    SquareMatrix.Multiplication.identity

constructive_injectivity RightInverse

/-- Retain the identity matrix as its own certified right inverse. -/
def identityInverse :
  SquareMatrix.Inverse.Right.RightInverse SquareMatrix.Multiplication.identity :=
  ⟨SquareMatrix.Multiplication.identity,
    SquareMatrix.Multiplication.identity_mul_int _⟩

/-- Compose retained right inverses in reverse order.

The result certifies a right inverse of the original matrix product using the two supplied multiplication identities. -/
def mulInverse {left right :
  LinearAlgebra.Matrix.Basic.IntegralMatrix}
    (leftInverse : SquareMatrix.Inverse.Right.RightInverse left) (rightInverse : SquareMatrix.Inverse.Right.RightInverse
      right) :
    SquareMatrix.Inverse.Right.RightInverse (SquareMatrix.Multiplication.mul left right) where
  inverse := SquareMatrix.Multiplication.mul rightInverse.inverse leftInverse.inverse
  identity := by
    rw [SquareMatrix.Multiplication.mul_assoc,
      ← SquareMatrix.Multiplication.mul_assoc right,
      rightInverse.identity, SquareMatrix.Multiplication.identity_mul_int,
      leftInverse.identity]
end Purelib.LinearAlgebra.Matrix.Inverse.Right

end
