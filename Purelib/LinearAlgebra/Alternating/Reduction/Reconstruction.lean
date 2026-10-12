module
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Vector.Unit
import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.LinearAlgebra.Alternating.Reduction.Dual

section
public section

/-! Exact reconstruction from the complete finite normal-form cycle rows. -/
namespace Purelib.LinearAlgebra.Alternating.Reduction

open Purelib.Algebra
open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {n : Nat} {matrix : SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}

/-- A cycle-row entry is the corresponding forward image of a coordinate unit. -/
theorem cycleRows_entry_forward (reduction : Reduction matrix raw) (row column : Fin n) :
    reduction.cycleRows row column = reduction.forward (Unit.unitVector column) row := open Purelib.LinearAlgebra.Vector
      in by
  rw [reduction.cycleRows_apply]
  calc
    _ = Weighted.weighted (Unit.unitVector column) (reduction.dualBackward (Unit.unitVector row)) :=
      (Unit.weighted_left_unit column _).symm
    _ = Weighted.weighted (reduction.forward (Unit.unitVector column)) (Unit.unitVector row) :=
      reduction.weighted_dualBackward _ _
    _ = _ := Unit.weighted_right_unit _ row

/-- Reconstruct each backward dual coordinate as an integral combination of the retained cycle rows.

The supplied vector gives the coefficients in the original finite row order. -/
theorem dualBackward_eq_cycleRows (reduction : Reduction matrix raw)
    (values : Data.Vector Int n) (column : Fin n) :
    reduction.dualBackward values column =
      FiniteSum.Fin.sumFin (fun row => values row * reduction.cycleRows row column) := open Purelib.LinearAlgebra.Vector
        in by
  calc
    _ = Weighted.weighted (Unit.unitVector column) (reduction.dualBackward values) :=
      (Unit.weighted_left_unit column _).symm
    _ = Weighted.weighted (reduction.forward (Unit.unitVector column)) values :=
      reduction.weighted_dualBackward _ _
    _ = _ := by
      apply FiniteSum.Fin.sumFin_congr
      intro row
      rw [reduction.cycleRows_entry_forward]
      exact mul_comm _ _

end Purelib.LinearAlgebra.Alternating.Reduction

end
