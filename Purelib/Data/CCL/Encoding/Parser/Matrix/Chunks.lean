module
import Purelib.Data.CCL.Encoding.Block.Matrix
public import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.Gaussian.Basic

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.CCL.Encoding.Parser.Matrix.Chunks

section
open Purelib.Data.CCL.Encoding
/-- Reading the initial true bit preserves the exact parser matrix. -/
public theorem fold_initial_high_matrix
    (parser : State)
    (phase : parser.phase = .initial) :
    ([true].foldl Parser.State.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      rfl

/-- Reading the initial false-true pair preserves the exact parser matrix. -/
public theorem fold_initial_low_entry_matrix
    (parser : State)
    (phase : parser.phase = .initial) :
    ([false, true].foldl Parser.State.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      rfl

/-- Reading a true bit in a retained low-unary phase preserves its exact parser matrix. -/
public theorem fold_low_unary_matrix
    (parser : State) (count : Nat)
    (phase : parser.phase = .lowUnary count) :
    ([true].foldl Parser.State.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      rfl

/-- Reading a true bit in a retained loop-unary phase preserves its exact parser matrix. -/
public theorem fold_residual_unary_matrix
    (parser : State) (count : Nat)
    (phase : parser.phase = .loopUnary count) :
    ([true].foldl Parser.State.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      rfl

end

open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
/-- Reading the initial zero-exponent low block right-multiplies the retained parser matrix by that exact block matrix.
-/
public theorem fold_initial_low_sector_matrix
    (parser : State)
    (phase : parser.phase = .initial)
    (sector : ComplexContinuedFraction.Encoding.Sector) :
    ((false :: false :: sector.code).foldl
      Parser.State.step parser).matrix =
        Matrix2.mul parser.matrix
          (Block.Matrix.blockMatrix .initialLow 0 sector) := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      cases sector <;> rfl

/-- Completing a retained low-unary exponent and sector right-multiplies the original parser matrix by that exact block
matrix. -/
public theorem fold_low_sector_matrix
    (parser : State) (count : Nat)
    (phase : parser.phase = .lowUnary count)
    (sector : ComplexContinuedFraction.Encoding.Sector) :
    ((false :: sector.code).foldl Parser.State.step parser).matrix =
      Matrix2.mul parser.matrix
        (Block.Matrix.blockMatrix .initialLow count sector) := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      cases sector <;> rfl

end Purelib.Data.CCL.Encoding.Parser.Matrix.Chunks

end
