module

public import Purelib.Data.CCL.Encoding.Prefix.Cursor
public import Purelib.Data.CCL.Encoding.Encoder.Canonical
public import Purelib.Data.CCL.Encoding.Parser.Terminal.Input
import Purelib.Geometry.Projective.Homography.Semantics
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.Data.List.Append

/-!
# Canonical terminal completion from the exact retained prefix

The terminal phase retains two actual sector bits and its original chart.
The existing annulus encoder supplies the third bit at the same terminal
representative. Appending that bit keeps the exposed word and completes its
actual parser matrix. Infinity is the final projective tail; the extended
word does not acquire a false affine parser certificate or residual padding.
-/

public section

namespace Purelib.Data.CCL.Encoding.Prefix.Cursor

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

set_option genInjectivity false in
/-- Retain a canonical terminal word extending its exact original cursor and the original tail encoder's sector bits. -/
structure Completion (cursor : Cursor) where
  /-- The original cursor has its complete cached affine validity. -/ valid : cursor.Valid
  /-- The final bit completing the retained two-bit sector fragment. -/ bit : Bool
  /-- The original terminal sector selected for this same affine tail. -/ sector : Sector
  /-- The exact original annulus encoding of that terminal sector, computed once. -/ encoding :
    Encoder.Integral.TailEncoding (Encoder.Annulus.ofSector sector)
  /-- The retained encoding is the original executable encoder output. -/ encodingEq :
    encoding = Encoder.Integral.encodeTail (Encoder.Annulus.ofSector sector)
  /-- The already exposed two sector bits retained from the original parser phase. -/ first : Bool
  /-- The already exposed second sector bit. -/ second : Bool
  /-- The old and returned bits are exactly the same original encoder's complete three-bit word. -/ sectorWord :
    encoding.word = [first, second, bit]
  /-- The exact extended raw word, retaining every previously exposed bit. -/ word : List Bool
  /-- The returned word appends only that same original final sector bit. -/ wordEq : word = cursor.word ++ [bit]
  /-- The actual parser state after consuming that same final bit. -/ state : Parser.State
  /-- The completed state belongs to the original parser's same actual next transition. -/ stateEq :
    state = Parser.State.step cursor.state bit
  /-- The completed state parses this same exact extended word. -/ stateSpec : state = Parser.State.parse word
  /-- The actual completed matrix reads the same original rational point at its final projective infinity tail. -/
  reconstruct : (Line.Matrix.act state.matrix Line.Proj.omega).Equivalent (Line.Proj.affine cursor.point)
  /-- The complete word has the same original parser terminal-sector semantics. -/ terminalSpec :
    Parser.Terminal.Word.Represents word cursor.point
  /-- The original terminal excludes both further affine next bits at this same input. -/ stopped :
    ∀ next, ¬ Parser.Semantics.Prefix.CanStep cursor.state cursor.point next

namespace Completion

/-- The canonical terminal word retains the exact previously exposed raw prefix. -/
theorem wordPrefix {cursor : Cursor} (completion : Completion cursor) : cursor.word.IsPrefix completion.word :=
  ⟨[completion.bit], completion.wordEq.symm⟩

/-- The completed word retains a nonsingular decoder matrix belonging to its actual original parser transition. -/
theorem determinant {cursor : Cursor} (completion : Completion cursor) :
    Matrix2.Matrix2.determinant completion.state.matrix ≠ 0 :=
  completion.stateEq.symm ▸ Parser.State.step_det_ne cursor.state completion.bit completion.valid.determinant

/-- The completed decoder's projective infinity image has a nonzero affine denominator at this same rational reading. -/
theorem denominator {cursor : Cursor} (completion : Completion cursor) :
    (Line.Matrix.act completion.state.matrix Line.Proj.omega).q ≠ 0 :=
  Line.Gaussian.Proj.denominator_ne_zero_of_equivalent_affine
    (Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate completion.determinant
      Line.Gaussian.Proj.omega_hasNonzeroCoordinate)
    completion.reconstruct

/-- Explicit quotient readback of the retained terminal matrix is the same original rational point. -/
theorem reading {cursor : Cursor} (completion : Completion cursor) :
    Line.Gaussian.Proj.affineReading (Line.Matrix.act completion.state.matrix Line.Proj.omega) = cursor.point :=
  Line.Gaussian.Proj.affineReading_eq_of_equivalent completion.denominator completion.reconstruct

/-- The completed terminal word has a projective final tail and cannot be asserted affine under the old convention. -/
theorem not_affine {cursor : Cursor} (completion : Completion cursor) :
    ¬ Parser.Semantics.Prefix.Represented completion.word cursor.point := by
  intro represented
  rcases represented with ⟨tail, represents⟩
  have next : Parser.Semantics.Prefix.CanStep cursor.state cursor.point completion.bit :=
    ⟨tail, completion.stateEq ▸ (completion.stateSpec.symm ▸ represents)⟩
  exact completion.stopped completion.bit next

end Completion

/-- Complete an actual terminal sector phase using its cached original affine tail and exact annulus encoder. -/
private def completeSector (cursor : Cursor) (valid : cursor.Valid)
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (first second : Bool)
    (phase : cursor.state.phase = .sector kind exponent (.two first second))
    (stopped : ∀ bit, ¬Parser.Semantics.Prefix.CanStep cursor.state cursor.point bit) : Completion cursor := by
  have noAdvance : ∀ bit, ¬Parser.Next.CanAdvanceAt cursor.state bit cursor.tail := by
    intro bit possible
    exact stopped bit ((Parser.Next.canStep_iff_canAdvanceAt cursor.state cursor.point cursor.tail
      valid.determinant valid.represents bit).mpr possible)
  have candidates := Parser.Terminal.before_eq_candidate_of_sectorTwo_terminal cursor.state cursor.point cursor.tail
    kind exponent first second phase valid.represents noAdvance
  let bit := if cursor.tail = Parser.Terminal.candidateBefore kind exponent first second false then false else true
  let sector := Sector.Code.sectorOfBits first second bit
  have tailEq : cursor.tail = Parser.Terminal.terminalBefore kind exponent sector := by
    unfold sector bit
    split
    · assumption
    · rename_i different
      cases candidates with
      | inl equal => exact (different equal).elim
      | inr equal => exact equal
  let encoding := Encoder.Integral.encodeTail (Encoder.Annulus.ofSector sector)
  let word := cursor.word ++ [bit]
  let state := Parser.State.step cursor.state bit
  have stateSpec : state = Parser.State.parse word :=
    (congrArg (fun previous => Parser.State.step previous bit) valid.stateSpec).trans
      (Parser.State.parse_append_singleton cursor.word bit).symm
  have matrixEq : state.matrix = Matrix2.mul cursor.state.matrix (Block.Matrix.blockMatrix kind exponent sector) := by
    unfold state Parser.State.step
    rewrite [phase]
    rfl
  have block := Parser.Terminal.block_terminal kind exponent sector
  have sameTail : (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) Line.Proj.omega).Equivalent
      (Line.Proj.affine cursor.tail) := tailEq.symm ▸ block
  have acted := Line.Matrix.act_respects_equivalent cursor.state.matrix sameTail
  have old := Homography.Semantics.actAffine_equivalent_homographic cursor.state.matrix cursor.tail cursor.point
    valid.represents.1 valid.represents.2.1.symm
  have middleDenominator : (Line.Matrix.act cursor.state.matrix (Line.Proj.affine cursor.tail)).q ≠ 0 := by
    change cursor.state.matrix.c * cursor.tail + cursor.state.matrix.d * 1 ≠ 0
    rewrite [Basic.mul_one]
    exact valid.represents.1
  have reconstruct : (Line.Matrix.act state.matrix Line.Proj.omega).Equivalent (Line.Proj.affine cursor.point) := by
    rewrite [matrixEq, Line.Matrix.act_mul]
    exact Line.Gaussian.equivalent_trans_of_mid_q acted old middleDenominator
  exact
    { valid := valid
      bit := bit
      sector := sector
      encoding := encoding
      encodingEq := rfl
      first := first
      second := second
      sectorWord := (Encoder.Integral.encodeTail_sector_word sector).trans (Sector.Code.sectorOfBits_code _ _ _)
      word := word
      wordEq := rfl
      state := state
      stateEq := rfl
      stateSpec := stateSpec
      reconstruct := reconstruct
      terminalSpec := ⟨cursor.word, kind, exponent, first, second, bit, cursor.tail,
        rfl, valid.stateSpec ▸ phase, valid.stateSpec ▸ valid.represents,
        tailEq.symm ▸ Parser.Terminal.normalizedValue_terminalBefore kind exponent sector⟩
      stopped := stopped }

/-- Finish a terminal original cursor without changing any exposed bit or asserting affine infinity.

The builder reads the original cached phase and tail. The existing finite
annulus encoder provides the final sector bit; its retained matrix and the
original decoder prove exact projective reconstruction of the same input.
-/
def complete (cursor : Cursor) (valid : cursor.Valid)
    (stopped : ∀ bit, ¬Parser.Semantics.Prefix.CanStep cursor.state cursor.point bit) : Completion cursor := by
  have noAdvance : ∀ bit, ¬Parser.Next.CanAdvanceAt cursor.state bit cursor.tail := by
    intro bit possible
    exact stopped bit ((Parser.Next.canStep_iff_canAdvanceAt cursor.state cursor.point cursor.tail
      valid.determinant valid.represents bit).mpr possible)
  have terminalPhase := Parser.Terminal.phase_eq_sectorTwo_of_no_advance cursor.state cursor.point cursor.tail
    valid.represents noAdvance
  cases phase : cursor.state.phase with
  | sector kind exponent bits =>
      cases bits with
      | two first second => exact completeSector cursor valid kind exponent first second phase stopped
      | zero => exact False.elim (by
          rcases terminalPhase with ⟨_, _, _, _, impossible⟩
          rewrite [phase] at impossible
          nomatch impossible)
      | one _ => exact False.elim (by
          rcases terminalPhase with ⟨_, _, _, _, impossible⟩
          rewrite [phase] at impossible
          nomatch impossible)
  | initial => exact False.elim (by
          rcases terminalPhase with ⟨_, _, _, _, impossible⟩
          rewrite [phase] at impossible
          nomatch impossible)
  | highUnary _ => exact False.elim (by
          rcases terminalPhase with ⟨_, _, _, _, impossible⟩
          rewrite [phase] at impossible
          nomatch impossible)
  | lowUnary _ => exact False.elim (by
          rcases terminalPhase with ⟨_, _, _, _, impossible⟩
          rewrite [phase] at impossible
          nomatch impossible)
  | loopUnary _ => exact False.elim (by
          rcases terminalPhase with ⟨_, _, _, _, impossible⟩
          rewrite [phase] at impossible
          nomatch impossible)

set_option genInjectivity false in
/-- Retain automatic completion of the same original cursor against one cached full integral encoding.

The bound is the number of remaining canonical word bits. Canonical affine
stepping emits every remaining bit except the final projective sector bit;
the last budget unit detects that stop. The returned original completion
appends that same final bit and agrees literally with the cached encoder word.
-/
structure FinishedEncoding (cursor : Cursor) (fraction : GaussianInt.Fraction)
    (numeratorNonzero : fraction.numerator ≠ 0) where
  /-- The same original cursor has its full affine validity. -/ valid : cursor.Valid
  /-- The displayed fraction reads this exact original rational point. -/ fractionValue : fraction.value = cursor.point
  /-- The original full encoding computed once for this exact displayed fraction. -/ encoding :
    Encoder.Integral.CompleteEncoding fraction
  /-- The retained encoding is the same original executable encoder output. -/ encodingEq :
    encoding = Encoder.Integral.encodeResult fraction numeratorNonzero
  /-- The computed additional bit budget, including the stop-detection unit. -/ bound : Nat
  /-- The bound belongs to this exact cached encoder word and original exposed prefix. -/ boundEq :
    bound = encoding.word.length - cursor.word.length
  /-- The actual original canonical request result within that computed bound. -/ request : Result cursor bound
  /-- The retained request is the original executable cursor procedure on the same owner and validity. -/ requestEq :
    request = cursor.request valid bound
  /-- The returned affine cursor has no admissible next bit. -/ stopped :
    ∀ bit, ¬Parser.Semantics.Prefix.CanStep request.next.state request.next.point bit
  /-- The original terminal completion of that actual returned cursor. -/ completion : Completion request.next
  /-- The retained completion is the original executable terminal constructor. -/ completionEq :
    completion = request.next.complete request.valid stopped
  /-- The complete terminal word is literally the same cached full encoder word. -/ wordEqual :
    completion.word = encoding.word

/-- The cached canonical word length forces the actual affine request to reach its terminal precursor. -/
private theorem request_encoding_stopped (cursor : Cursor) (valid : cursor.Valid) (word : List Bool)
    (canonical : Parser.Terminal.Word.Represents word cursor.point) :
    ∀ bit, ¬Parser.Semantics.Prefix.CanStep
      (cursor.request valid (word.length - cursor.word.length)).next.state
      (cursor.request valid (word.length - cursor.word.length)).next.point bit := by
  let result := cursor.request valid (word.length - cursor.word.length)
  have short := Parser.Terminal.Word.affine_length_lt canonical (cursor.represented valid)
  have rebuilt : cursor.word.length + (word.length - cursor.word.length) = word.length :=
    Nat.add_sub_of_le (Nat.le_of_lt short)
  cases result.completion with
  | inr stopped => exact stopped
  | inl paid =>
      have actualLength : result.next.word.length = word.length := by
        rewrite [result.wordEq, Data.List.Append.length_append, paid]
        exact rebuilt
      have actualShort := Parser.Terminal.Word.affine_length_lt canonical result.represented
      rewrite [actualLength] at actualShort
      exact (Nat.lt_irrefl _ actualShort).elim

/-- Compute the remaining bound, actual terminal request and full-word comparison without a supplied stop or fuel.

The original full encoder runs once on the retained fraction. Its canonical
parser certificate proves the original request's computed length budget
sufficient, including the detection step. The returned cursor is then completed
by the original projective terminal constructor, preserving every exposed bit.
-/
def finishEncoding (cursor : Cursor) (valid : cursor.Valid) (fraction : GaussianInt.Fraction)
    (numeratorNonzero : fraction.numerator ≠ 0) (fractionValue : fraction.value = cursor.point) :
    FinishedEncoding cursor fraction numeratorNonzero := by
  let encoding := Encoder.Integral.encodeResult fraction numeratorNonzero
  have canonical : Parser.Terminal.Word.Represents encoding.word cursor.point :=
    fractionValue ▸ Encoder.Integral.encodeResult_terminal fraction numeratorNonzero
  let bound := encoding.word.length - cursor.word.length
  let requested := cursor.request valid bound
  have stopped : ∀ bit, ¬Parser.Semantics.Prefix.CanStep requested.next.state requested.next.point bit :=
    request_encoding_stopped cursor valid encoding.word canonical
  let completion := requested.next.complete requested.valid stopped
  have returnedCanonical : Parser.Terminal.Word.Represents completion.word cursor.point :=
    requested.pointEq ▸ completion.terminalSpec
  exact
    { valid := valid
      fractionValue := fractionValue
      encoding := encoding
      encodingEq := rfl
      bound := bound
      boundEq := rfl
      request := requested
      requestEq := rfl
      stopped := stopped
      completion := completion
      completionEq := rfl
      wordEqual := Parser.Terminal.Word.unique returnedCanonical canonical }

namespace FinishedEncoding

/-- The automatically completed word preserves every bit exposed at the original cursor. -/
theorem wordPrefix {cursor : Cursor} {fraction : GaussianInt.Fraction} {numeratorNonzero : fraction.numerator ≠ 0}
    (result : FinishedEncoding cursor fraction numeratorNonzero) : cursor.word.IsPrefix result.completion.word := by
  refine ⟨result.request.suffix ++ [result.completion.bit], ?_⟩
  exact (Data.List.Append.append_assoc cursor.word result.request.suffix [result.completion.bit]).symm.trans
    ((congrArg (fun retained => retained ++ [result.completion.bit]) result.request.wordEq.symm).trans
      result.completion.wordEq.symm)

/-- The retained projective terminal matrix reads the exact original cursor point. -/
theorem reading {cursor : Cursor} {fraction : GaussianInt.Fraction} {numeratorNonzero : fraction.numerator ≠ 0}
    (result : FinishedEncoding cursor fraction numeratorNonzero) :
    Line.Gaussian.Proj.affineReading (Line.Matrix.act result.completion.state.matrix Line.Proj.omega) = cursor.point :=
  result.completion.reading.trans result.request.pointEq

/-- The computed budget is exactly the emitted affine suffix length plus its one stop-detection unit. -/
theorem bound_exact {cursor : Cursor} {fraction : GaussianInt.Fraction} {numeratorNonzero : fraction.numerator ≠ 0}
    (result : FinishedEncoding cursor fraction numeratorNonzero) : result.request.suffix.length + 1 = result.bound := by
  have completeLength := congrArg List.length result.wordEqual
  rewrite [result.completion.wordEq, result.request.wordEq,
    Data.List.Append.length_append, Data.List.Append.length_append] at completeLength
  change (cursor.word.length + result.request.suffix.length) + 1 = result.encoding.word.length at completeLength
  have exactLength : result.encoding.word.length = cursor.word.length + (result.request.suffix.length + 1) :=
    completeLength.symm.trans (Nat.add_assoc cursor.word.length result.request.suffix.length 1)
  apply Eq.trans _ result.boundEq.symm
  rewrite [exactLength, Nat.add_sub_cancel_left]
  rfl

end FinishedEncoding

end Purelib.Data.CCL.Encoding.Prefix.Cursor

end
