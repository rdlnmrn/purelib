module

import Purelib.LinearAlgebra.Alternating.UnitPivot
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Reduction.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Alternating.UnitPivot.Lift
import Purelib.LinearAlgebra.Matrix.Shear.Integral.Lift
import Mathlib.Tactic.Linter.Lint
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Shear.Integral.Basic

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

namespace Purelib.LinearAlgebra.Alternating.Reduction.Lift.Step

open Purelib.LinearAlgebra

variable {n : Nat}
section UnitPivot

variable {matrix : SquareMatrix.IntegralMatrix n}
end UnitPivot

section Step

variable {matrix : SquareMatrix.IntegralMatrix n} {indices : Handle.Basic.PivotIndices n}

/-- Lift a retained step across an extra matrix block clear at its pivot coordinates.

The construction reuses the original shear and materializes the augmented output as the extra block plus the retained
output. -/
def withExtra (step : Reduction.Basic.Step
  matrix indices) (extra augmented : SquareMatrix.IntegralMatrix n)
    (split : ∀ row column, augmented row column = extra row column + matrix row column)
    (clear : SquareMatrix.Shear.Integral.Lift.ClearAt extra indices.1 indices.2) : Reduction.Basic.Step augmented
      indices :=
  let actual : SquareMatrix.Shear.Integral.Lift.ClearAt extra step.pivot.first step.pivot.last := by
    rw [step.first_eq, step.last_eq]; exact clear
  { pivot := UnitPivot.withExtra step.pivot extra augmented split actual
    first_eq := step.first_eq
    last_eq := step.last_eq
    change := step.change
    change_eq := step.change_eq.trans (UnitPivot.withExtra_shear step.pivot extra augmented
      split actual).symm
    output := SquareMatrix.matrixOfFn fun row column => extra row column + step.output row column
    output_eq := by
      apply SquareMatrix.matrix_ext; intro row column
      rw [SquareMatrix.matrixOfFn_apply, step.output_eq]
      exact (SquareMatrix.Integral.Shear.transform_extra step.change matrix extra augmented split actual row
        column).symm }

open Purelib.LinearAlgebra.Alternating in
/-- The lifted step output is entrywise the extra block plus the original output. -/
theorem withExtra_output (step :
  Reduction.Basic.Step matrix indices) (extra augmented : SquareMatrix.IntegralMatrix n)
    (split : ∀ row column, augmented row column = extra row column + matrix row column)
    (clear : SquareMatrix.Shear.Integral.Lift.ClearAt extra indices.1 indices.2) (row column : Fin n) :
    (withExtra step extra augmented split clear).output row column = extra row
      column + step.output row column :=
  SquareMatrix.matrixOfFn_apply _ row column

end Step

end Purelib.LinearAlgebra.Alternating.Reduction.Lift.Step

end
