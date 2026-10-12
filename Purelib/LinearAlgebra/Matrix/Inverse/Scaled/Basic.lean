module

import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic

universe u
variable {K : Type*} [CommRing K]

set_option genInjectivity false in
/-- A retained matrix inverse up to one common scalar on both sides.

The original square matrix determines the dimension and coefficient ring; both product identities refer to the same
cached inverse and scalar. -/
structure ScaledInverse {n : Nat} (matrix :
  SquareMatrix K n) where
  /-- The common scalar in both inverse product identities. -/ scalar : K
  /-- The retained square inverse matrix with the original dimension. -/ inverse : SquareMatrix K n
  /-- The retained inverse times the original matrix is the scalar identity. -/ left_identity :
    SquareMatrix.Multiplication.mul inverse matrix = SquareMatrix.Multiplication.scaleIdentity scalar
  /-- The original matrix times the retained inverse is the scalar identity. -/ right_identity :
    SquareMatrix.Multiplication.mul matrix inverse = SquareMatrix.Multiplication.scaleIdentity scalar

constructive_injectivity ScaledInverse

end Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic

end
