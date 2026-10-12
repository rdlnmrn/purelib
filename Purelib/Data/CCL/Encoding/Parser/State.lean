module

public import Purelib.Data.CCL.Encoding.Block.Matrix
public import Purelib.Data.CCL.Encoding.Parser.Constraint
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.Fold
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
public import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Order.RelClasses
meta import Purelib.Elab.ConstructiveInjectivity

-- Retain the established public nominal State.State name.

/-!
# Finite raw-prefix parser over constructive Gaussian fractions

The completed-block encoder is not enough for a persistent root name: a
request may stop inside a unary header or after only one or two sector bits.
This module records exactly that unfinished syntax, the finite decoder
product, and the finite list of already completed block constraints.  It is
the state needed by the box/CCL next-bit controller; no stream, completion,
or collection of compatible points is formed.
-/

namespace Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

@[expose] public section

set_option genInjectivity false in
/-- Retain a parser phase, exact accumulated decoder matrix and ordered completed-block constraints.

The phase records unfinished syntax. Completing a block right-multiplies the matrix and pulls the retained history back
through that same block, preserving its order and nominal constraints. -/
structure State where
  /-- The exact unfinished syntax phase and retained unary counter or sector bits. -/ phase : Parser.Syntax.Phase
  /-- The accumulated decoder matrix for the completed blocks. -/
  matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix
  /-- The ordered completed-block constraints pulled back to the current tail. -/ history : List
    Constraint
deriving DecidableEq

constructive_injectivity State

end

namespace State

/-- The initial syntax phase with identity decoder matrix and empty constraint history.

The identity matrix and empty ordered history are retained directly. No completed block or sector is selected. -/
@[expose] public def initialState : State := ⟨.initial, Matrix2.identityMatrix, []⟩

/-- Complete the retained three-bit sector, multiply by its block matrix and precompose every original history
constraint.

The new history starts with the exact emitted block constraint, followed by the original constraints pulled back through
that same matrix. The phase resets to loop-unary zero. -/
@[expose] public def completeSector (state : State) (kind : Parser.Syntax.BlockKind) (exponent : Nat)
    (first second third : Bool) : State :=
  let sector := Sector.Code.sectorOfBits first second third
  let block := Block.Matrix.blockMatrix kind exponent sector
  let newest : Constraint := ⟨block, kind, exponent, sector⟩
  { phase := .loopUnary 0
    matrix := Matrix2.mul state.matrix block
    history := newest :: state.history.map (fun item => item.precompose block) }

/-- Consume one Boolean parser bit, preserving the retained matrix and history until a sector completes.

Unary phases update their exact counters and sector phases retain the bits already read. The third sector bit calls
completeSector with the same kind, exponent and three bits. -/
@[expose] public def step (state : State) (bit : Bool) : State :=
  match state.phase with
  | .initial =>
      if bit then { state with phase := .highUnary 1 }
      else { state with phase := .lowUnary 0 }
  | .highUnary count =>
      if bit then { state with phase := .highUnary (count + 1) }
      else { state with phase := .sector .initialHigh count .zero }
  | .lowUnary count =>
      if bit then { state with phase := .lowUnary (count + 1) }
      else { state with phase := .sector .initialLow count .zero }
  | .loopUnary count =>
      if bit then { state with phase := .loopUnary (count + 1) }
      else { state with phase := .sector .loop count .zero }
  | .sector kind exponent .zero =>
      { state with phase := .sector kind exponent (.one bit) }
  | .sector kind exponent (.one first) =>
      { state with phase := .sector kind exponent (.two first bit) }
  | .sector kind exponent (.two first second) =>
      completeSector state kind exponent first second bit

/-- The full parser step's phase equals the exact syntax-only next phase.

The same phase, retained unary count or sector bits and supplied Boolean determine both transitions. Completing a sector
resets their phase to the same loop-unary zero. -/
@[simp] public theorem step_phase (state : State) (bit : Bool) :
    (step state bit).phase = state.phase.next bit := by
  cases state with
  | mk phase matrix history =>
      cases phase with
      | initial => cases bit <;> rfl
      | highUnary count => cases bit <;> rfl
      | lowUnary count => cases bit <;> rfl
      | loopUnary count => cases bit <;> rfl
      | sector kind exponent bits =>
          cases bits with
          | zero => rfl
          | one first => rfl
          | two first second => rfl

/-- Folding full parser steps has the same phase as consuming the exact word in the syntax machine.

The structural fold retains the original starting phase and consumes each Boolean in order. The phase projection
commutes with every full parser step. -/
public theorem foldl_step_phase (state : State) : ∀ word :
  BinaryPrefix.Basic.SourceEncodingRawParserWordAlias,
    (word.foldl step state).phase = state.phase.consume word
  | [] => rfl
  | bit :: remaining => by
      simp only [List.foldl_cons, Parser.Syntax.Phase.consume]
      rw [foldl_step_phase (step state bit), step_phase]
      rfl

end State
namespace Syntax.Phase

/-- Reading a complete retained sector code resets the phase to loop-unary zero.

The sector is one entry of the original eight-sector table. Its three retained bits complete the current sector phase
without changing the supplied block kind or exponent. -/
@[simp] public theorem consume_sector_code
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : ComplexContinuedFraction.Encoding.Sector) :
    Parser.Syntax.Phase.consume (.sector kind exponent .zero) sector.code =
      .loopUnary 0 := by
  cases sector <;> rfl

end Syntax.Phase
namespace State

/-- Fold the exact Boolean word through parser steps starting from the retained initial state.

The ordered finite fold retains the original matrix and history updates. Unary and unfinished-sector prefixes remain
represented by the same syntax phases. -/
@[expose] public def parse (word : BinaryPrefix.Basic.SourceEncodingRawParserWordAlias) : State :=
  word.foldl step initialState

/-- The empty word parses as the exact initial state. -/
@[simp] public theorem parse_nil : parse [] = initialState := rfl

/-- Parsing an appended word continues folding from the exact state retained after its prefix.

The same parser transition first consumes the original prefix and then the suffix. The retained matrix, phase and
ordered constraints are carried directly between the two folds. -/
public theorem parse_append (word suffix : BinaryPrefix.Basic.SourceEncodingRawParserWordAlias) :
    parse (word ++ suffix) = suffix.foldl step (parse word) := by
  unfold parse
  rw [Fold.foldl_append]

/-- The phase after an appended word consumes its suffix from the exact parsed prefix phase.

Projection of the full fold agrees with syntax-only consumption from that retained phase. Both words retain their
original Boolean order. -/
public theorem parse_append_phase (word suffix : BinaryPrefix.Basic.SourceEncodingRawParserWordAlias) :
    (parse (word ++ suffix)).phase =
      (parse word).phase.consume suffix := by
  rw [parse_append, foldl_step_phase]

/-- Appending one Boolean bit performs exactly one step from the parsed prefix state. -/
@[simp] public theorem parse_append_singleton (word : BinaryPrefix.Basic.SourceEncodingRawParserWordAlias) (bit : Bool)
  :
    parse (word ++ [bit]) = step (parse word) bit := by
  rw [parse_append]
  rfl

/-- One parser bit increases the retained phase counter by at most one.

Unary branches retain or increment their natural counter. Sector branches retain their exponent until completion, which
resets the loop counter to zero. -/
public theorem step_counter_le (state : State) (bit : Bool) :
    (step state bit).phase.counter ≤ state.phase.counter + 1 := by
  cases state with
  | mk phase matrix history =>
      cases phase with
      | initial =>
          cases bit
          · exact Nat.zero_le 1
          · exact Nat.le_refl 1
      | highUnary count =>
          cases bit
          · exact Nat.le_succ count
          · exact Nat.le_refl (count + 1)
      | lowUnary count =>
          cases bit
          · exact Nat.le_succ count
          · exact Nat.le_refl (count + 1)
      | loopUnary count =>
          cases bit
          · exact Nat.le_succ count
          · exact Nat.le_refl (count + 1)
      | sector kind exponent bits =>
          cases bits with
          | zero => exact Nat.le_succ exponent
          | one first => exact Nat.le_succ exponent
          | two first second => exact Nat.zero_le (exponent + 1)

/-- Folding a word increases the retained phase counter by at most that word's length.

Structural induction adds the same single-bit bound at each retained transition. The starting phase counter and original
Boolean word determine the finite total. -/
private theorem foldl_counter_le (state : State) :
    ∀ word : BinaryPrefix.Basic.SourceEncodingRawParserWordAlias,
      (word.foldl step state).phase.counter ≤
        state.phase.counter + word.length
  | [] => Nat.le_refl state.phase.counter
  | bit :: remaining => by
      simp only [List.foldl_cons, List.length_cons]
      have rest := foldl_counter_le (step state bit) remaining
      have one := step_counter_le state bit
      omega

/-- The phase counter of a parsed word is at most its exact bit length.

The original initial phase has counter zero. The structural single-bit bound therefore controls the retained counter
after the ordered word fold. -/
public theorem parse_counter_le (word : BinaryPrefix.Basic.SourceEncodingRawParserWordAlias) :
    (parse word).phase.counter ≤ word.length := by
  have bound := foldl_counter_le initialState word
  simpa only [parse, initialState, Parser.Syntax.Phase.counter, Nat.zero_add] using bound

/-- A parser step preserves nonzero determinant of the exact retained decoder matrix.

Every incomplete syntax transition retains the same matrix. Sector completion multiplies it by the supplied block
matrix, whose determinant is also nonzero. -/
public theorem step_det_ne (state : State) (bit : Bool)
    (determinant : Matrix2.Matrix2.determinant state.matrix ≠ 0) :
    Matrix2.Matrix2.determinant (step state bit).matrix ≠ 0 := by
  cases state with
  | mk phase matrix history =>
      cases phase with
      | initial => cases bit <;> exact determinant
      | highUnary count => cases bit <;> exact determinant
      | lowUnary count => cases bit <;> exact determinant
      | loopUnary count => cases bit <;> exact determinant
      | sector kind exponent bits =>
          cases bits with
          | zero => exact determinant
          | one first => exact determinant
          | two first second =>
              change Matrix2.Matrix2.determinant
                (Matrix2.mul matrix
                  (Block.Matrix.blockMatrix kind exponent
                    (Sector.Code.sectorOfBits first second bit))) ≠ 0
              rw [Matrix2.det_mul]
              exact Field.mul_ne_zero_direct determinant
                (Block.Matrix.blockMatrix_det_ne kind exponent
                  (Sector.Code.sectorOfBits first second bit))

/-- Folding parser steps preserves a nonzero determinant for the exact retained matrix.

Each Boolean preserves the same invariant under its original transition. The ordered word fold therefore carries the
supplied nonzero determinant certificate to its retained final state. -/
private theorem foldl_det_ne (state : State) :
    ∀ word : BinaryPrefix.Basic.SourceEncodingRawParserWordAlias,
      Matrix2.Matrix2.determinant state.matrix ≠ 0 →
        Matrix2.Matrix2.determinant
          (word.foldl step state).matrix ≠ 0
  | [], determinant => determinant
  | bit :: remaining, determinant =>
      foldl_det_ne (step state bit) remaining
        (step_det_ne state bit determinant)

/-- Every parsed finite word has a decoder matrix with nonzero determinant.

The retained initial matrix is the identity. Folding the original Boolean word preserves its determinant nonvanishing
through every completed block. -/
public theorem parse_det_ne (word : BinaryPrefix.Basic.SourceEncodingRawParserWordAlias) :
    Matrix2.Matrix2.determinant (parse word).matrix ≠ 0 := by
  apply foldl_det_ne initialState word
  decide

/-- At least one entry in the parsed decoder matrix's lower row is nonzero.

Two zero lower-row entries would make the same retained matrix determinant zero. Its parser determinant certificate
excludes that simultaneous vanishing. -/
public theorem parse_lowerRow_ne (word : BinaryPrefix.Basic.SourceEncodingRawParserWordAlias) :
    (parse word).matrix.c ≠ 0 ∨ (parse word).matrix.d ≠ 0 := by
  by_cases cZero : (parse word).matrix.c = 0
  · by_cases dZero : (parse word).matrix.d = 0
    · have determinantZero :
          Matrix2.Matrix2.determinant (parse word).matrix = 0 := by
        rw [Matrix2.Matrix2.determinant, cZero, dZero,
          Basic.mul_zero, Basic.mul_zero]
        exact Basic.sub_zero 0
      exact (parse_det_ne word determinantZero).elim
    · exact Or.inr dZero
  · exact Or.inl cZero

end State
end Purelib.Data.CCL.Encoding.Parser
