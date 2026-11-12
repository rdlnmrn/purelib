module

public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Rectangular
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained rectangular normal forms

Both coordinate changes retain their original square inverse certificates at
scalar one. The cached reduced rectangle is their actual product with the
original matrix, with an initial identity block and zero remaining entries.
-/

@[expose] public section

namespace Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Inverse.Scaled.Basic

variable {K : Type*} [CommRing K] {rows columns : Nat}

set_option genInjectivity false in
/-- An original rectangle with certified invertible coordinates and a diagonal reduction.

The initial identity block is bounded by both original dimensions. Its size
records this specific coordinate reduction over the coefficient ring; no field
or intrinsic rank classification is assumed. Both inverse records refer to the
same retained coordinate matrices, and the reduced rectangle is cached once.
-/
structure NormalForm (matrix : Rectangular K rows columns) where
  /-- The size of the initial identity block of the retained reduction. -/
  rank : Nat
  /-- The identity block fits the original target coordinates. -/
  rank_le_rows : rank ≤ rows
  /-- The identity block fits the original source coordinates. -/
  rank_le_columns : rank ≤ columns
  /-- The retained change from reduced to original source coordinates. -/
  source : SquareMatrix K columns
  /-- Both inverse identities for the same retained source change. -/
  sourceInverse : ScaledInverse source
  /-- The retained source inverse is an actual inverse at scalar one. -/
  source_scalar : sourceInverse.scalar = 1
  /-- The retained change from original to reduced target coordinates. -/
  target : SquareMatrix K rows
  /-- Both inverse identities for the same retained target change. -/
  targetInverse : ScaledInverse target
  /-- The retained target inverse is an actual inverse at scalar one. -/
  target_scalar : targetInverse.scalar = 1
  /-- The original rectangle after both retained coordinate changes. -/
  reduced : Rectangular K rows columns
  /-- The cached reduction is the actual product of the original retained data. -/
  reduced_eq : reduced = Rectangular.mul (Rectangular.mul target matrix) source
  /-- The cached entries are precisely the bounded initial identity block. -/
  reduced_apply : ∀ row column, reduced row column =
    if row.val = column.val ∧ row.val < rank then 1 else 0

constructive_injectivity NormalForm

end Purelib.LinearAlgebra.Matrix

end
