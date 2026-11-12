module

public import Purelib.Data.CCL.Transducer.Mode.Code
public import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.CCL.Transducer.Mode.Grammar

/-!
# Exact rational realization of a retained transducer mode

A selected possible rational tail replaces only the quantitative process.
The original kind, normalization count, residual upper bound and loop-domain
payments are retained. The raw phase and exact projective parser tail remain
unchanged, including the residual-zero homogeneous infinity convention.
-/

public section

namespace Purelib.Data.CCL.Transducer.Mode.Exact

open Purelib
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.Gaussian

/-- The interpreted finite original description retains the same normalization matrix at every phase. -/
private theorem encoded_normalization (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) :
    Cursor.Image.Mode.tailMatrix
        ((Code.ofPossible original value possible).val.interpret
          (Code.ofPossible original value possible).property) =
      Cursor.Image.Mode.tailMatrix original := by
  cases original <;> rfl

set_option genInjectivity false in
/-- Retain an original mode, its selected possible rational tail and the exact replacement mode.

The replacement process contains only that finite rational reading. Its
phase and parser-tail certificates retain the original interpretation,
rather than substituting canonical affine syntax for productive padding.
-/
structure Realization (original : Mode) where
  /-- The actual selected rational tail. -/ value : Basic.Canonical
  /-- That reading is possible at the original retained mode state. -/ possible :
    Semantics.SemanticMode.possible original value
  /-- The exact replacement with the original phase data and retained quantitative payments. -/ mode : Mode
  /-- The replacement has exactly this one rational reading at its current state. -/ possibleEq :
    ∀ candidate, Semantics.SemanticMode.possible mode candidate ↔ candidate = value
  /-- The replacement retains the original raw parser phase. -/ phaseEq :
    Grammar.modeRawPhase mode = Grammar.modeRawPhase original
  /-- The exact projective parser tail is the original tail at the selected rational reading. -/ tailEq :
    Semantics.SemanticMode.parserTail mode value = Semantics.SemanticMode.parserTail original value
  /-- The exact finite numerical mode description, with no original source callback. -/ code : Code
  /-- The code's retained quantitative payments are valid. -/ valid : code.Valid
  /-- The code uses the same selected original rational tail. -/ codeValueEq : code.value = value
  /-- The counterpart is interpreted from this exact finite description. -/ modeEq : mode = code.interpret valid
  /-- The counterpart keeps the original normalization matrix for cached chart transport. -/ normalizationEq :
    Cursor.Image.Mode.tailMatrix mode = Cursor.Image.Mode.tailMatrix original

/-- Construct the exact counterpart from an explicitly supplied tail possible at the original state. -/
def ofPossible (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) : Realization original := by
  let encoded := Code.ofPossible original value possible
  let mode := encoded.val.interpret encoded.property
  have valueEq := Code.ofPossible_value original value possible
  have possibleEq : ∀ candidate, Semantics.SemanticMode.possible mode candidate ↔ candidate = value := by
    intro candidate
    constructor
    · intro admitted
      exact ((encoded.val.interpret_possible encoded.property candidate).mp admitted).trans valueEq
    · intro equal
      exact (encoded.val.interpret_possible encoded.property candidate).mpr (equal.trans valueEq.symm)
  exact
    { value := value
      possible := possible
      mode := mode
      possibleEq := possibleEq
      phaseEq := Code.ofPossible_phase original value possible
      tailEq := Code.ofPossible_tail original value possible value
      code := encoded.val
      valid := encoded.property
      codeValueEq := valueEq
      modeEq := rfl
      normalizationEq := encoded_normalization original value possible }

/-- The realized original mode retains the exact supplied rational tail. -/
private theorem ofPossible_specification (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) :
    (ofPossible original value possible).value = value ∧
      (ofPossible original value possible).code = Code.data original value := ⟨rfl, rfl⟩

/-- The exact mode constructor uses the same original supplied rational reading. -/
theorem ofPossible_value (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) :
    (ofPossible original value possible).value = value := (ofPossible_specification original value possible).1

/-- The exact mode constructor retains the original numerical phase description at its supplied possible tail. -/
theorem ofPossible_code (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) :
    (ofPossible original value possible).code = Code.data original value :=
  (ofPossible_specification original value possible).2

/-- Construct a mode's exact counterpart by consuming its actual retained process witness once. -/
def ofMode (original : Mode) : Realization original :=
  let selected := Semantics.SemanticMode.witness original
  ofPossible original selected.val selected.property

namespace Realization

/-- The selected rational tail is a possible reading of the exact replacement mode. -/
theorem value_possible {original : Mode} (realization : Realization original) :
    Semantics.SemanticMode.possible realization.mode realization.value :=
  (realization.possibleEq realization.value).mpr rfl

/-- Every exact replacement reading was possible at the same original retained mode state. -/
theorem original_possible {original : Mode} (realization : Realization original) {candidate : Basic.Canonical}
    (possible : Semantics.SemanticMode.possible realization.mode candidate) :
    Semantics.SemanticMode.possible original candidate :=
  ((realization.possibleEq candidate).mp possible).symm ▸ realization.possible

end Realization

end Purelib.Data.CCL.Transducer.Mode.Exact

end
