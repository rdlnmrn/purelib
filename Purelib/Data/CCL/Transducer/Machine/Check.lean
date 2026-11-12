module

public import Purelib.Data.CCL.Transducer.Machine.Code
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Mode.Grammar

/-!
# Exact checking of finite cursor descriptions

Checking validates the supplied phase payments, words and every cached chart
field. Success preserves the original code and caches; rejection identifies
and proves the particular condition violated by that same description.
-/

public section

namespace Purelib.Data.CCL.Transducer.Machine.Code

open Purelib
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Encoding
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

set_option genInjectivity false in
/-- A finite cursor description violates one identified phase, grammar or cache condition. -/
inductive Invalid (code : Code) where
  /-- The proposed local tail fails a retained numerical phase payment. -/ | mode (failed : ¬ code.mode.Valid)
  /-- The parser cache does not belong to the exact supplied committed word. -/ | parser
      (failed : code.parser ≠ Parser.State.parse (code.emitted ++ code.pending))
  /-- The normalization cache does not belong to the same interpreted paid mode. -/ | normalization
      (paid : code.mode.Valid)
      (failed : code.normalization ≠ Cursor.Image.Mode.tailMatrix (code.mode.interpret paid))
  /-- The combined matrix does not multiply the exact supplied two factors. -/ | factors
      (failed : code.matrix ≠ Matrix2.mul code.parser.matrix code.normalization)
  /-- The adjugate cache does not belong to the exact supplied combined matrix. -/ | adjugate
      (failed : code.adjugate ≠ Matrix2.BoundaryAdjugate.adjugate code.matrix)
  /-- The exact supplied chart is singular. -/ | singular (equal : Matrix2.Matrix2.determinant code.matrix = 0)
  /-- The supplied parser phase does not belong to the same interpreted paid mode. -/ | grammar
      (paid : code.mode.Valid) (failed : code.parser.phase ≠ Mode.Grammar.modeRawPhase (code.mode.interpret paid))

namespace Invalid

/-- Every identified finite description violation refutes validity of that exact supplied code. -/
theorem refutes {code : Code} (invalid : Invalid code) : ¬ Valid code := by
  intro valid
  cases invalid with
  | mode failed => exact failed valid.modeValid
  | parser failed => exact failed valid.parserEq
  | normalization paid failed => exact failed valid.normalizationEq
  | factors failed => exact failed valid.factorsEq
  | adjugate failed => exact failed valid.adjugateEq
  | singular equal => exact valid.determinantNonzero equal
  | grammar paid failed => exact failed valid.grammar

end Invalid

/-- Check finite cursor data, retaining its original validity or its proved violated condition. -/
def check (code : Code) : Except (Invalid code) (PLift (Valid code)) :=
  if paid : code.mode.Valid then
    if parser : code.parser = Parser.State.parse (code.emitted ++ code.pending) then
      if normalization : code.normalization = Cursor.Image.Mode.tailMatrix (code.mode.interpret paid) then
        if factors : code.matrix = Matrix2.mul code.parser.matrix code.normalization then
          if adjugate : code.adjugate = Matrix2.BoundaryAdjugate.adjugate code.matrix then
            if singular : Matrix2.Matrix2.determinant code.matrix = 0 then .error (.singular singular)
            else
              if grammar : code.parser.phase = Mode.Grammar.modeRawPhase (code.mode.interpret paid) then
                .ok ⟨⟨paid, parser, normalization, factors, adjugate, singular, grammar⟩⟩
              else .error (.grammar paid grammar)
          else .error (.adjugate adjugate)
        else .error (.factors factors)
      else .error (.normalization paid normalization)
    else .error (.parser parser)
  else .error (.mode paid)

/-- Checking any already valid finite cursor description succeeds with a certificate for those exact retained data. -/
theorem check_valid (code : Code) (valid : Valid code) :
    ∃ certificate, check code = .ok certificate := by
  cases result : check code with
  | ok certificate => exact ⟨certificate, rfl⟩
  | error invalid => exact (invalid.refutes valid).elim

end Purelib.Data.CCL.Transducer.Machine.Code

end
