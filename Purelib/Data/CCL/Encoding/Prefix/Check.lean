module

public import Purelib.Data.CCL.Encoding.Prefix.Cursor
import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Exact checking of canonical affine cursor data

Checking retains the supplied word, parser, inverse matrix and local tail.
Success proves the same complete affine representation; rejection identifies
the actual violated parser, cache, denominator, reading or phase condition.
-/

public section

namespace Purelib.Data.CCL.Encoding.Prefix.Cursor

open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

set_option genInjectivity false in
/-- A supplied canonical cursor violates one identified original affine representation condition. -/
inductive Invalid (cursor : Cursor) where
  /-- The supplied parser cache does not belong to the exact supplied word. -/ | parser
      (failed : cursor.state ≠ Parser.State.parse cursor.word)
  /-- The supplied inverse cache does not belong to the exact supplied parser matrix. -/ | inverse
      (failed : cursor.inverseMatrix ≠ Matrix2.BoundaryAdjugate.adjugate cursor.state.matrix)
  /-- The exact supplied parser matrix is singular. -/ | singular
      (equal : Matrix2.Matrix2.determinant cursor.state.matrix = 0)
  /-- The supplied local tail does not consume the same cached inverse chart and input. -/ | tail
      (failed : cursor.tail ≠ Homography.Basic.homographic cursor.inverseMatrix cursor.point)
  /-- The supplied affine parser denominator vanishes at that same local tail. -/ | denominator
      (equal : Homography.Basic.denominator cursor.state.matrix cursor.tail = 0)
  /-- The supplied chart and tail do not read the same original input. -/ | reading
      (failed : cursor.point ≠ Homography.Basic.homographic cursor.state.matrix cursor.tail)
  /-- The complete original history or active-phase conditions fail at the supplied local tail. -/ | conditions
      (failed : cursor.state.holdsBool cursor.tail ≠ true)

namespace Invalid

/-- Every identified canonical-cursor defect refutes validity of that exact supplied affine cursor. -/
theorem refutes {cursor : Cursor} (invalid : Invalid cursor) : ¬ cursor.Valid := by
  intro valid
  cases invalid with
  | parser failed => exact failed valid.stateSpec
  | inverse failed => exact failed valid.inverseSpec
  | singular equal => exact valid.determinant equal
  | tail failed => exact failed valid.tailSpec
  | denominator equal => exact valid.represents.1 equal
  | reading failed => exact failed valid.represents.2.1
  | conditions failed => exact failed ((Parser.State.holdsBool_eq_true _ _).mpr valid.represents.2.2)

end Invalid

/-- Check exact canonical cursor data without rebuilding any supplied parser, inverse chart or local tail. -/
def check (cursor : Cursor) : Except (Invalid cursor) (PLift cursor.Valid) :=
  if parser : cursor.state = Parser.State.parse cursor.word then
    if inverse : cursor.inverseMatrix = Matrix2.BoundaryAdjugate.adjugate cursor.state.matrix then
      if singular : Matrix2.Matrix2.determinant cursor.state.matrix = 0 then .error (.singular singular)
      else if tail : cursor.tail = Homography.Basic.homographic cursor.inverseMatrix cursor.point then
        if denominator : Homography.Basic.denominator cursor.state.matrix cursor.tail = 0 then
          .error (.denominator denominator)
        else if reading : cursor.point = Homography.Basic.homographic cursor.state.matrix cursor.tail then
          if conditions : cursor.state.holdsBool cursor.tail = true then
            .ok ⟨⟨parser, singular, inverse, tail, denominator, reading,
              (Parser.State.holdsBool_eq_true _ _).mp conditions⟩⟩
          else .error (.conditions conditions)
        else .error (.reading reading)
      else .error (.tail tail)
    else .error (.inverse inverse)
  else .error (.parser parser)

/-- Checking any already valid canonical cursor succeeds for that same exact retained word and chart data. -/
theorem check_valid (cursor : Cursor) (valid : cursor.Valid) :
    ∃ certificate, check cursor = .ok certificate := by
  cases result : check cursor with
  | ok certificate => exact ⟨certificate, rfl⟩
  | error invalid => exact (invalid.refutes valid).elim

end Purelib.Data.CCL.Encoding.Prefix.Cursor

end
