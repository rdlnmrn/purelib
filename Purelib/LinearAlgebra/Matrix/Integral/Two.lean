module
import Purelib.Data.Fin.Two

import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Tactic.Linter.Lint
import Mathlib.Algebra.Ring.Int.Defs

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

namespace Purelib.LinearAlgebra.Matrix.Integral.Two

/-- A structural two-by-two matrix in row-major order. -/
def matrix₂ (topLeft topRight bottomLeft
  bottomRight : Int) :
    LinearAlgebra.Matrix.Basic.IntegralMatrix :=
  SquareMatrix.matrixOfFn fun row column =>
    if row = 0 then
      if column = 0 then topLeft else topRight
    else if column = 0 then bottomLeft else bottomRight

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix in
/-- Multiply two displayed two-by-two integral matrices by the explicit four entry formulas. -/
theorem mul_matrix₂ (a b c d e f g h : Int) :
    SquareMatrix.Multiplication.mul (SquareMatrix.Integral.Two.matrix₂ a b c d) (SquareMatrix.Integral.Two.matrix₂ e f g
      h) =
      SquareMatrix.Integral.Two.matrix₂ (a * e + b * g) (a * f + b * h)
        (c * e + d * g) (c * f + d * h) := open Purelib.Algebra in open Purelib in by
  apply SquareMatrix.matrix_ext
  intro row column
  rcases Data.Fin.Two.finTwo_cases row with rowZero | rowOne
  · subst row
    rcases Data.Fin.Two.finTwo_cases column with columnZero | columnOne
    · subst column
      rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_two_int]
      rfl
    · subst column
      rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_two_int]
      rfl
  · subst row
    rcases Data.Fin.Two.finTwo_cases column with columnZero | columnOne
    · subst column
      rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_two_int]
      rfl
    · subst column
      rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_two_int]
      rfl
end Purelib.LinearAlgebra.Matrix.Integral.Two

end
