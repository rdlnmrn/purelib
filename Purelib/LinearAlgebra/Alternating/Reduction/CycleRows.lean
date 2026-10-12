module
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Alternating.Reduction.Dual
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Vector.Unit
import Mathlib.Algebra.Ring.Int.Defs

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra.Vector

section
@[expose] public section

/-!
# Integer weights of the actual transformed cycle rows

The inverse of the dual coordinate map is the transpose of the ordinary
basis change. Applying it to coordinate unit vectors therefore constructs
integer rows for linear combinations of cycles. Pairing those rows with the
original values evaluates the corresponding row of the final handle form.
-/

namespace Purelib.LinearAlgebra.Alternating.Reduction

variable {K : Type*} [CommRing K] {n : Nat}

/-- All integer rows are materialized once, ready for cached cycle sums. -/
def cycleRows {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}
    (reduction : Reduction matrix raw) : SquareMatrix.IntegralMatrix n :=
  Data.Vector.Basic.vectorOfFn fun row => reduction.dualBackward (Unit.unitVector row)

/-- Read a retained cycle row as the inverse dual image of its coordinate unit. -/
theorem cycleRows_apply {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}
    (reduction : Reduction matrix raw) (row : Fin n) :
    reduction.cycleRows row = reduction.dualBackward (Unit.unitVector row) := Data.Vector.Basic.vectorOfFn_apply _ row
end Purelib.LinearAlgebra.Alternating.Reduction

end
