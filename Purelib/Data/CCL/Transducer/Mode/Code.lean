module

public import Purelib.Data.CCL.Transducer.Mode.Semantics
public import Purelib.Data.CCL.Transducer.Mode.Grammar
import Purelib.Approximation.Gaussian.Process.Basic

/-!
# Finite descriptions of exact rational cursor modes

Code retains only a rational tail, its phase and counters, and the finite
quantitative data needed by that phase. Its fixed interpreter constructs
the singleton process at that same tail. No original state type, source
procedure or function-valued callback is a code field.
-/

public section

namespace Purelib.Data.CCL.Transducer.Mode

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.Rat

set_option genInjectivity false in
/-- A finite numerical description of one exact rational mode, retaining its original phase data and payments. -/
inductive Code where
  /-- An exact initial tail before normalization. -/ | initial (value : Basic.Canonical)
  /-- A low tail at the retained unary count. -/ | low (count : Nat) (value : Basic.Canonical)
  /-- A regular tail with its original kind, count, lower quadrance and weight. -/ | loop
      (kind : Basic.RegularKind) (count : Nat) (value : Basic.Canonical)
      (lowerSq weight : Fraction.Rational)
  /-- A residual tail with its original padding count and squared upper bound. -/ | residual
      (count : Nat) (value : Basic.Canonical) (upper : Fraction.Rational)
deriving @[expose] DecidableEq

namespace Code

/-- Read the exact rational tail retained by this same code. -/
@[expose] def value : Code → Basic.Canonical
  | .initial value | .low _ value | .loop _ _ value _ _ | .residual _ value _ => value

/-- Check the exact numerical bounds required by the retained phase.

The low phase has its strict fixed norm bound. The loop retains a positive
weight and lower quadrance above its weighted coefficient. The residual
retains its original strict padding payment, including at the zero tail.
-/
@[expose] def Valid : Code → Prop
  | .initial _ => True
  | .low _ value => Norm.Basic.normSq value < 43 / 20
  | .loop _ _ value lowerSq weight =>
      0 < weight ∧ (weight + 1) / weight < lowerSq ∧ lowerSq ≤ Norm.Basic.normSq value
  | .residual count value upper => Norm.Basic.normSq value ≤ upper ∧ upper < Padding.Residual.paddingTarget count

/-- Decide the retained phase's exact rational payments using only finite numerical comparisons. -/
instance (code : Code) : Decidable code.Valid := by
  cases code <;> unfold Valid <;> infer_instance

/-- Interpret finite valid mode code using only its retained rational data and the fixed exact-process constructor. -/
@[expose] def interpret (code : Code) (valid : Valid code) : Mode :=
  match code with
  | .initial value => .initial ⟨Process.exact value, ()⟩
  | .low count value => .low
      { count := count
        process := Process.exact value
        state := ()
        upperBound := by
          intro candidate equal
          change candidate = value at equal
          cases equal
          exact valid }
  | .loop kind count value lowerSq weight => .loop
      { kind := kind
        count := count
        process := Process.exact value
        state := ()
        domain :=
          { lowerSq := lowerSq
            weight := weight
            weightPositive := valid.1
            coefficient_lt := valid.2.1
            lower := by
              intro _ candidate equal
              change candidate = value at equal
              cases equal
              exact valid.2.2 } }
  | .residual count value upper => .residual
      { count := count
        process := Process.exact value
        state := ()
        upper := upper
        upperStrict := valid.2
        upperBound := by
          intro candidate equal
          change candidate = value at equal
          cases equal
          exact valid.1 }

/-- The interpreted code's current possibilities are exactly its retained rational tail. -/
theorem interpret_possible (code : Code) (valid : Valid code) (candidate : Basic.Canonical) :
    Semantics.SemanticMode.possible (code.interpret valid) candidate ↔ candidate = code.value := by
  cases code <;> exact Iff.rfl

/-- Describe original numerical phase data at a supplied coordinate without assuming that coordinate possible. -/
@[expose] def data (original : Mode) (value : Basic.Canonical) : Code :=
  match original with
  | .initial _ => .initial value
  | .low current => .low current.count value
  | .loop current => .loop current.kind current.count value current.domain.lowerSq current.domain.weight
  | .residual current => .residual current.count value current.upper

/-- Replace only the proposed rational tail while retaining the exact finite phase data and payments. -/
@[expose] def replaceValue (code : Code) (value : Basic.Canonical) : Code :=
  match code with
  | .initial _ => .initial value
  | .low count _ => .low count value
  | .loop kind count _ lowerSq weight => .loop kind count value lowerSq weight
  | .residual count _ upper => .residual count value upper

/-- Replacing the proposed coordinate retains that exact supplied new rational tail. -/
theorem replaceValue_value (code : Code) (value : Basic.Canonical) : (code.replaceValue value).value = value := by
  cases code <;> rfl

/-- Changing a coordinate in original mode data preserves all original phase fields exactly. -/
theorem data_replaceValue (original : Mode) (earlier later : Basic.Canonical) :
    (data original earlier).replaceValue later = data original later := by
  cases original <;> rfl

/-- An actual original possible tail validates the numerical description at that same rational coordinate. -/
theorem data_valid (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) : (data original value).Valid := by
  cases original with
  | initial current => exact True.intro
  | low current => exact current.upperBound possible
  | loop current =>
      exact ⟨current.domain.weightPositive, current.domain.coefficient_lt, current.domain.lower current.state possible⟩
  | residual current => exact ⟨current.upperBound possible, current.upperStrict⟩

/-- Encode an original possible tail with its actual kind, counters and quantitative data. -/
@[expose] def ofPossible (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) : {code : Code // Valid code} :=
  ⟨data original value, data_valid original value possible⟩

/-- Encoding an original possible tail retains that exact supplied rational reading. -/
theorem ofPossible_value (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) :
    (ofPossible original value possible).1.value = value := by
  cases original <;> rfl

/-- Interpreting the original finite mode description preserves its exact raw parser phase. -/
theorem ofPossible_phase (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) :
    Grammar.modeRawPhase
        ((ofPossible original value possible).1.interpret (ofPossible original value possible).2) =
      Grammar.modeRawPhase original := by
  cases original <;> rfl

/-- The interpreted original mode description preserves its parser-tail formula at every supplied coordinate. -/
theorem ofPossible_tail (original : Mode) (value : Basic.Canonical)
    (possible : Semantics.SemanticMode.possible original value) (candidate : Basic.Canonical) :
    Semantics.SemanticMode.parserTail
        ((ofPossible original value possible).1.interpret (ofPossible original value possible).2) candidate =
      Semantics.SemanticMode.parserTail original candidate := by
  cases original <;> rfl

end Code

end Purelib.Data.CCL.Transducer.Mode

end
