module
public import Purelib.Data.Gaussian.Basic
import Mathlib.Tactic.Linter.Lint
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.LinearAlgebra.Vector.Dot
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

namespace Purelib.LinearAlgebra.Matrix.Gaussian.WeightedSum
/-- Transport a weighted Gaussian matrix-vector sum to a weighted sum of its columns.

Both finite index sums retain their original dimension; the coefficient products are rearranged by commutativity. -/
public theorem
  weighted_matrixVector {n
  : Nat}
    (matrix : SquareMatrix Data.Gaussian.Basic.Canonical n)
    (vector weights : Data.Vector Data.Gaussian.Basic.Canonical n) :
    FiniteSum.Fin.sumFin
        (fun row =>
          SquareMatrix.Multiplication.matrixVector matrix vector row *
            weights row) =
      FiniteSum.Fin.sumFin
        (fun column =>
          FiniteSum.Fin.sumFin
              (fun row => matrix row column * weights row) *
            vector column) := by
  calc
    FiniteSum.Fin.sumFin
        (fun row =>
          SquareMatrix.Multiplication.matrixVector matrix vector row *
            weights row) =
        FiniteSum.Fin.sumFin
        (fun row =>
          FiniteSum.Fin.sumFin
              (fun column => matrix row column * vector column) *
            weights row) := by
        apply FiniteSum.Fin.sumFin_congr
        intro row
        rw [SquareMatrix.Multiplication.matrixVector,
          Data.Vector.Basic.vectorOfFn_apply]
        rfl
    _ =
        FiniteSum.Fin.sumFin
          (fun row => FiniteSum.Fin.sumFin
            (fun column =>
              (matrix row column * vector column) * weights row)) := by
                apply FiniteSum.Fin.sumFin_congr
                intro row
                rw [FiniteSum.Fin.sumFin_mul_right]
    _ = FiniteSum.Fin.sumFin
          (fun column => FiniteSum.Fin.sumFin
            (fun row =>
              (matrix row column * vector column) * weights row)) :=
      FiniteSum.Fin.sumFin_swap _
    _ = FiniteSum.Fin.sumFin
          (fun column =>
            FiniteSum.Fin.sumFin
                (fun row => matrix row column * weights row) *
              vector column) := by
                apply FiniteSum.Fin.sumFin_congr
                intro column
                rw [FiniteSum.Fin.sumFin_congr
                  (right := fun row =>
                    (matrix row column * weights row) * vector column)
                  (fun _ => by ring1)]
                rw [FiniteSum.Fin.sumFin_mul_right]
end Purelib.LinearAlgebra.Matrix.Gaussian.WeightedSum

end

end
