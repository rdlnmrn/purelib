module

public import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Shear.Integral.Basic
import Mathlib.Tactic.Linter.Lint
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Retaining an orthogonal block through an integral reduction

A cached extra matrix with zero rows and columns at the selected pivots is
unchanged by the corresponding shears. Lifting reuses each existing shear;
only the full output matrix is computed anew.
-/

namespace Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra

variable {n : Nat}

namespace Shear.Integral.Lift

/-- The extra block has no row or column at either pivot coordinate. -/
structure ClearAt (extra :
  SquareMatrix.IntegralMatrix n) (first last : Fin n) : Prop where
  /-- The extra matrix vanishes along the first pivot row. -/ row_first : ∀ index, extra first index = 0
  /-- The extra matrix vanishes along the last pivot row. -/ row_last : ∀ index, extra last index = 0
  /-- The extra matrix vanishes along the first pivot column. -/ column_first : ∀ index, extra index first = 0
  /-- The extra matrix vanishes along the last pivot column. -/ column_last : ∀ index, extra index last = 0

end Shear.Integral.Lift
namespace Integral.Shear

/-- A block clear at both pivot rows and columns passes unchanged through the shear transformation.

The supplied entrywise split retains the same original, extra and augmented matrices. -/
theorem transform_extra {first last :
  Fin n} (shear : SquareMatrix.Integral.Shear first last)
    (matrix extra augmented : SquareMatrix.IntegralMatrix n)
    (split : ∀ row column, augmented row column = extra row column + matrix row column)
    (clear : SquareMatrix.Shear.Integral.Lift.ClearAt extra first last) (row column : Fin n) :
    shear.transform augmented row column = extra row column + shear.transform matrix row column := by
  rw [shear.transform_apply, shear.transform_apply]
  simp only [split, clear.row_first, clear.row_last, clear.column_first, clear.column_last, zero_add]
  ring1

end Integral.Shear
namespace UnitPivot

variable {matrix : SquareMatrix.IntegralMatrix n}
end UnitPivot

namespace Step

variable {matrix : SquareMatrix.IntegralMatrix n} {indices : Handle.Basic.PivotIndices n}
end Step

end Purelib.LinearAlgebra.Matrix

end
