module

public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Matrix.Basic
import Mathlib.Tactic.Linter.Lint
import Mathlib.Algebra.Ring.Int.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Constructive integral row spanning from a retained unit normal form

Only the finitely many unused-coordinate kernel tests are required.
Transform the requested row, solve each disjoint unit handle, and apply
the retained transpose changes backwards. All coefficients are integers;
there is no field division, search, quotient, or choice of a preimage.
-/

namespace Purelib.LinearAlgebra.Matrix.Integral

variable {n : Nat}

set_option genInjectivity false in
/-- A materialized integral linear combination of the original rows. -/
structure RowSpan (matrix :
  SquareMatrix.IntegralMatrix n) (row : Data.Vector Int n) where
  /-- The retained integer coefficients of the original rows. -/ coefficients : Data.Vector Int n
  /-- Each requested row entry is the finite combination using those exact retained coefficients. -/ equation : ∀
    column, row column = FiniteSum.Fin.sumFin (fun index => coefficients index * matrix index column)

constructive_injectivity RowSpan

end Purelib.LinearAlgebra.Matrix.Integral

end
