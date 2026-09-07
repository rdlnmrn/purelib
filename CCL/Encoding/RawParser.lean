import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.Cylinder

/-!
# Finite raw-prefix parser over constructive Gaussian fractions

The completed-block encoder is not enough for a persistent root name: a
request may stop inside a unary header or after only one or two sector bits.
This module records exactly that unfinished syntax, the finite decoder
product, and the finite list of already completed block constraints.  It is
the state needed by the box/CCL next-bit controller; no stream, completion,
or collection of compatible points is formed.
-/

namespace CCL.RawParser

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Word := List Bool

/-- Executable prefix test for displayed Boolean words.  It is defined by
direct finite recursion, avoiding the generic proposition-valued prefix
decision instance. -/
def isWordPrefix : Word → Word → Bool
  | [], _ => true
  | _ :: _, [] => false
  | false :: earlier, false :: later => isWordPrefix earlier later
  | true :: earlier, true :: later => isWordPrefix earlier later
  | false :: _, true :: _ => false
  | true :: _, false :: _ => false

theorem isWordPrefix_trans {first second third : Word}
    (firstSecond : isWordPrefix first second = true)
    (secondThird : isWordPrefix second third = true) :
    isWordPrefix first third = true := by
  induction first generalizing second third with
  | nil => rfl
  | cons firstBit firstTail inductionHypothesis =>
      cases second with
      | nil =>
          cases firstBit <;> exact Bool.noConfusion firstSecond
      | cons secondBit secondTail =>
          cases third with
          | nil =>
              cases secondBit <;> exact Bool.noConfusion secondThird
          | cons thirdBit thirdTail =>
              cases firstBit <;> cases secondBit <;> cases thirdBit
              · exact inductionHypothesis firstSecond secondThird
              · exact Bool.noConfusion secondThird
              · exact Bool.noConfusion firstSecond
              · exact Bool.noConfusion firstSecond
              · exact Bool.noConfusion firstSecond
              · exact Bool.noConfusion firstSecond
              · exact Bool.noConfusion secondThird
              · exact inductionHypothesis firstSecond secondThird

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors

/-- Which radial bracket precedes the sector code currently being read. -/
inductive BlockKind where
  | initialHigh
  | initialLow
  | loop
deriving DecidableEq, Repr

/-- The three possible unfinished sector-code lengths. -/
inductive SectorBits where
  | zero
  | one (first : Bool)
  | two (first second : Bool)
deriving DecidableEq, Repr

namespace SectorBits

def word : SectorBits → Word
  | .zero => []
  | .one first => [first]
  | .two first second => [first, second]

@[simp] theorem word_length : ∀ bits : SectorBits,
    bits.word.length = match bits with
      | .zero => 0
      | .one _ => 1
      | .two _ _ => 2
  | .zero => rfl
  | .one _ => rfl
  | .two _ _ => rfl

end SectorBits

/-- The fixed displayed order of the eight sector rows. -/
def sectorTable : List Sector :=
  [.east, .northEast, .north, .northWest,
    .west, .southWest, .south, .southEast]

/-- Sector rows compatible with an unfinished zero-, one-, or two-bit code. -/
def sectorCandidates (bits : SectorBits) : List Sector :=
  sectorTable.filter fun sector => isWordPrefix bits.word sector.code

theorem sectorCandidates_length (bits : SectorBits) :
    (sectorCandidates bits).length = match bits with
      | .zero => 8
      | .one _ => 4
      | .two _ _ => 2 := by
  cases bits with
  | zero => decide
  | one first => cases first <;> decide
  | two first second => cases first <;> cases second <;> decide

@[simp] theorem sectorCandidates_zero :
    sectorCandidates .zero = sectorTable := by
  decide

@[simp] theorem sectorCandidates_one_false :
    sectorCandidates (.one false) =
      [.east, .northEast, .north, .northWest] := by
  decide

@[simp] theorem sectorCandidates_one_true :
    sectorCandidates (.one true) =
      [.west, .southWest, .south, .southEast] := by
  decide

@[simp] theorem sectorCandidates_two_false_false :
    sectorCandidates (.two false false) = [.east, .northEast] := by
  decide

@[simp] theorem sectorCandidates_two_false_true :
    sectorCandidates (.two false true) = [.north, .northWest] := by
  decide

@[simp] theorem sectorCandidates_two_true_false :
    sectorCandidates (.two true false) = [.west, .southWest] := by
  decide

@[simp] theorem sectorCandidates_two_true_true :
    sectorCandidates (.two true true) = [.south, .southEast] := by
  decide

/-- Decode the third sector bit by the exact eight-row table. -/
def sectorOfBits : Bool → Bool → Bool → Sector
  | false, false, false => .east
  | false, false, true => .northEast
  | false, true, false => .north
  | false, true, true => .northWest
  | true, false, false => .west
  | true, false, true => .southWest
  | true, true, false => .south
  | true, true, true => .southEast

@[simp] theorem sectorOfBits_code (first second third : Bool) :
    (sectorOfBits first second third).code = [first, second, third] := by
  cases first <;> cases second <;> cases third <;> rfl

theorem completed_sectorCandidates (first second third : Bool) :
    sectorTable.filter
        (fun sector => isWordPrefix [first, second, third] sector.code) =
      [sectorOfBits first second third] := by
  cases first <;> cases second <;> cases third <;> decide

/-- Parser phases.  A third sector bit immediately completes its block. -/
inductive Phase where
  | initial
  | highUnary (count : Nat)
  | lowUnary (count : Nat)
  | loopUnary (count : Nat)
  | sector (kind : BlockKind) (exponent : Nat) (bits : SectorBits)
deriving DecidableEq, Repr

namespace Phase

def counter : Phase → Nat
  | .highUnary count => count
  | .lowUnary count => count
  | .loopUnary count => count
  | .sector _ exponent _ => exponent
  | .initial => 0

/-- Syntax-only transition underlying the full raw parser.  Keeping this
finite automaton separate makes it possible to certify producers of ordinary
CCL bits without importing any enclosure or error-sidecar semantics. -/
def next : Phase → Bool → Phase
  | .initial, bit =>
      if bit then .highUnary 1 else .lowUnary 0
  | .highUnary count, bit =>
      if bit then .highUnary (count + 1)
      else .sector .initialHigh count .zero
  | .lowUnary count, bit =>
      if bit then .lowUnary (count + 1)
      else .sector .initialLow count .zero
  | .loopUnary count, bit =>
      if bit then .loopUnary (count + 1)
      else .sector .loop count .zero
  | .sector kind exponent .zero, bit =>
      .sector kind exponent (.one bit)
  | .sector kind exponent (.one first), bit =>
      .sector kind exponent (.two first bit)
  | .sector _ _ (.two _ _), _ => .loopUnary 0

/-- Consume a finite word in the syntax-only raw automaton. -/
def consume (phase : Phase) (word : Word) : Phase :=
  word.foldl next phase

end Phase

/-- Identity decoder before the first complete block. -/
def identityMatrix : Mat2 := ⟨1, 0, 0, 1⟩

/-- Decoder matrix selected when the unfinished sector code completes. -/
def blockMatrix (kind : BlockKind) (exponent : Nat) (sector : Sector) : Mat2 :=
  match kind with
  | .initialLow => CCL.Decoder.lowBlock exponent sector
  | .initialHigh | .loop =>
      CCL.Decoder.regularBlock exponent sector

/-- Normalized annulus value inspected by the sector table. -/
def normalizedValue (kind : BlockKind) (exponent : Nat)
    (value : Gaussian) : Gaussian :=
  match kind with
  | .initialLow => natPow gamma exponent * value
  | .initialHigh | .loop => value * (natPow gamma exponent)⁻¹

/-- The exact radial bracket after the unary delimiter. -/
def radialBracket (kind : BlockKind) (exponent : Nat)
    (value : Gaussian) : Prop :=
  match kind with
  | .initialHigh =>
      (2 : Coordinate) ^ exponent ≤ normSq value ∧
        normSq value < (2 : Coordinate) ^ (exponent + 1)
  | .initialLow =>
      1 ≤ (2 : Coordinate) ^ exponent * normSq value ∧
        (2 : Coordinate) ^ exponent * normSq value < 2
  | .loop =>
      (2 : Coordinate) ^ exponent < normSq value ∧
        normSq value ≤ (2 : Coordinate) ^ (exponent + 1)

instance radialBracketDecidable (kind : BlockKind) (exponent : Nat)
    (value : Gaussian) : Decidable (radialBracket kind exponent value) := by
  cases kind <;> simp only [radialBracket] <;> infer_instance

/-- Exact predicate of one completed raw block. -/
def fullBlockHolds (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (value : Gaussian) : Prop :=
  radialBracket kind exponent value ∧
    sector.Holds (normalizedValue kind exponent value)

instance fullBlockHoldsDecidable (kind : BlockKind) (exponent : Nat)
    (sector : Sector) (value : Gaussian) :
    Decidable (fullBlockHolds kind exponent sector value) := by
  unfold fullBlockHolds
  infer_instance

def numerator (matrix : Mat2) (tail : Gaussian) : Gaussian :=
  matrix.a * tail + matrix.b

def denominator (matrix : Mat2) (tail : Gaussian) : Gaussian :=
  matrix.c * tail + matrix.d

/-- Affine value of one finite projective decoder matrix. -/
def homographic (matrix : Mat2) (tail : Gaussian) : Gaussian :=
  numerator matrix tail * (denominator matrix tail)⁻¹

/-- A completed historical block, pulled back to the current affine tail. -/
structure Constraint where
  matrix : Mat2
  kind : BlockKind
  exponent : Nat
  sector : Sector
deriving DecidableEq

namespace Constraint

def precompose (constraint : Constraint) (block : Mat2) : Constraint :=
  { constraint with matrix := CCL.Mat2.mul constraint.matrix block }

def Holds (constraint : Constraint) (tail : Gaussian) : Prop :=
  denominator constraint.matrix tail ≠ 0 ∧
    fullBlockHolds constraint.kind constraint.exponent constraint.sector
      (homographic constraint.matrix tail)

instance holdsDecidable (constraint : Constraint) (tail : Gaussian) :
    Decidable (constraint.Holds tail) := by
  unfold Holds
  infer_instance

end Constraint

/-- Predicate of the active unfinished fragment. -/
def activeHolds : Phase → Gaussian → Prop
  | .initial, _ => True
  | .highUnary count, value => (2 : Coordinate) ^ count ≤ normSq value
  | .lowUnary 0, value => normSq value < 2
  | .lowUnary (count + 1), value =>
      (2 : Coordinate) ^ count * normSq value < 1
  | .loopUnary count, value => (2 : Coordinate) ^ count < normSq value
  | .sector kind exponent bits, value =>
      radialBracket kind exponent value ∧
        ∃ sector ∈ sectorCandidates bits,
          sector.Holds (normalizedValue kind exponent value)

instance activeHoldsDecidable (phase : Phase) (value : Gaussian) :
    Decidable (activeHolds phase value) := by
  cases phase with
  | initial => simp only [activeHolds]; infer_instance
  | highUnary count => simp only [activeHolds]; infer_instance
  | lowUnary count =>
      cases count <;> simp only [activeHolds] <;> infer_instance
  | loopUnary count => simp only [activeHolds]; infer_instance
  | sector kind exponent bits => simp only [activeHolds]; infer_instance

/-- Complete finite parser state after a raw prefix. -/
structure State where
  phase : Phase
  matrix : Mat2
  history : List Constraint
deriving DecidableEq

def initialState : State := ⟨.initial, identityMatrix, []⟩

/-- Complete one sector code and rebase all finite historical constraints. -/
def completeSector (state : State) (kind : BlockKind) (exponent : Nat)
    (first second third : Bool) : State :=
  let sector := sectorOfBits first second third
  let block := blockMatrix kind exponent sector
  let newest : Constraint := ⟨block, kind, exponent, sector⟩
  { phase := .loopUnary 0
    matrix := CCL.Mat2.mul state.matrix block
    history := newest :: state.history.map (fun item => item.precompose block) }

/-- One deterministic raw-bit transition. -/
def step (state : State) (bit : Bool) : State :=
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

@[simp] theorem step_phase (state : State) (bit : Bool) :
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

/-- The full parser and syntax-only parser always have the same phase. -/
theorem foldl_step_phase (state : State) : ∀ word : Word,
    (word.foldl step state).phase = state.phase.consume word
  | [] => rfl
  | bit :: remaining => by
      simp only [List.foldl_cons, Phase.consume]
      rw [foldl_step_phase (step state bit), step_phase]
      rfl

@[simp] theorem Phase.consume_sector_code
    (kind : BlockKind) (exponent : Nat) (sector : Sector) :
    Phase.consume (.sector kind exponent .zero) sector.code =
      .loopUnary 0 := by
  cases sector <;> rfl

/-- Parse an arbitrary finite raw word by a bounded fold. -/
def parse (word : Word) : State := word.foldl step initialState

namespace State

def Holds (state : State) (tail : Gaussian) : Prop :=
  (∀ constraint ∈ state.history, constraint.Holds tail) ∧
    activeHolds state.phase tail

def holdsBool (state : State) (tail : Gaussian) : Bool :=
  (state.history.all fun constraint => decide (constraint.Holds tail)) &&
    decide (activeHolds state.phase tail)

theorem holdsBool_eq_true (state : State) (tail : Gaussian) :
    state.holdsBool tail = true ↔ state.Holds tail := by
  rw [holdsBool, Holds, Bool.and_eq_true,
    QuotientFreeList.all_eq_true]
  constructor
  · rintro ⟨historyAccepted, activeAccepted⟩
    exact ⟨fun constraint member =>
      of_decide_eq_true (historyAccepted constraint member),
      of_decide_eq_true activeAccepted⟩
  · rintro ⟨historyHolds, activeHolds⟩
    exact ⟨fun constraint member =>
      decide_eq_true (historyHolds constraint member),
      decide_eq_true activeHolds⟩

/-- Tagged truncation coordinate before retaining the raw prefix tag. -/
def truncation (state : State) : Proj :=
  CCL.Mat2.act state.matrix (CCL.Proj.omega : Proj)

end State

@[simp] theorem parse_nil : parse [] = initialState := rfl

theorem parse_append (word suffix : Word) :
    parse (word ++ suffix) = suffix.foldl step (parse word) := by
  unfold parse
  rw [QuotientFreeList.foldl_append]

theorem parse_append_phase (word suffix : Word) :
    (parse (word ++ suffix)).phase =
      (parse word).phase.consume suffix := by
  rw [parse_append, foldl_step_phase]

@[simp] theorem parse_append_singleton (word : Word) (bit : Bool) :
    parse (word ++ [bit]) = step (parse word) bit := by
  rw [parse_append]
  rfl

/-- A unary counter grows by at most one per consumed bit. -/
theorem step_counter_le (state : State) (bit : Bool) :
    (step state bit).phase.counter ≤ state.phase.counter + 1 := by
  cases state with
  | mk phase matrix history =>
      cases phase with
      | initial => cases bit <;> simp [step, Phase.counter]
      | highUnary count => cases bit <;> simp [step, Phase.counter]
      | lowUnary count => cases bit <;> simp [step, Phase.counter]
      | loopUnary count => cases bit <;> simp [step, Phase.counter]
      | sector kind exponent bits =>
          cases bits with
          | zero => simp [step, Phase.counter]
          | one first => simp [step, Phase.counter]
          | two first second =>
              simp [step, completeSector, Phase.counter]

private theorem foldl_counter_le (state : State) :
    ∀ word : Word,
      (word.foldl step state).phase.counter ≤
        state.phase.counter + word.length
  | [] => by simp
  | bit :: remaining => by
      simp only [List.foldl_cons, List.length_cons]
      have rest := foldl_counter_le (step state bit) remaining
      have one := step_counter_le state bit
      omega

/-- The stored unary count is bounded by the finite prefix length. -/
theorem parse_counter_le (word : Word) :
    (parse word).phase.counter ≤ word.length := by
  have bound := foldl_counter_le initialState word
  simpa only [parse, initialState, Phase.counter, Nat.zero_add] using bound

theorem det_mul (left right : Mat2) :
    CCL.Chordal.Mat2.det (CCL.Mat2.mul left right) =
      CCL.Chordal.Mat2.det left *
        CCL.Chordal.Mat2.det right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.Chordal.Mat2.det, CCL.Mat2.mul,
      mul_re, mul_im, add_re, add_im, sub_re, sub_im] <;>
    ring1

theorem blockMatrix_det_ne
    (kind : BlockKind) (exponent : Nat) (sector : Sector) :
    CCL.Chordal.Mat2.det
        (blockMatrix kind exponent sector) ≠ 0 := by
  cases kind with
  | initialHigh =>
      rw [blockMatrix, CCL.Decoder.regularBlock_det]
      exact neg_ne_zero_direct
        (natPow_ne_zero_direct gamma (by decide) (exponent + 1))
  | initialLow =>
      rw [blockMatrix, CCL.Decoder.lowBlock_det]
      exact neg_ne_zero_direct
        (natPow_ne_zero_direct gamma (by decide) (exponent + 1))
  | loop =>
      rw [blockMatrix, CCL.Decoder.regularBlock_det]
      exact neg_ne_zero_direct
        (natPow_ne_zero_direct gamma (by decide) (exponent + 1))

theorem step_det_ne (state : State) (bit : Bool)
    (determinant : CCL.Chordal.Mat2.det state.matrix ≠ 0) :
    CCL.Chordal.Mat2.det (step state bit).matrix ≠ 0 := by
  cases state with
  | mk phase matrix history =>
      cases phase with
      | initial => cases bit <;> simpa [step] using determinant
      | highUnary count => cases bit <;> simpa [step] using determinant
      | lowUnary count => cases bit <;> simpa [step] using determinant
      | loopUnary count => cases bit <;> simpa [step] using determinant
      | sector kind exponent bits =>
          cases bits with
          | zero => simpa [step] using determinant
          | one first => simpa [step] using determinant
          | two first second =>
              change CCL.Chordal.Mat2.det
                (CCL.Mat2.mul matrix
                  (blockMatrix kind exponent
                    (sectorOfBits first second bit))) ≠ 0
              rw [det_mul]
              exact mul_ne_zero_direct determinant
                (blockMatrix_det_ne kind exponent
                  (sectorOfBits first second bit))

private theorem foldl_det_ne (state : State) :
    ∀ word : Word,
      CCL.Chordal.Mat2.det state.matrix ≠ 0 →
        CCL.Chordal.Mat2.det
          (word.foldl step state).matrix ≠ 0
  | [], determinant => determinant
  | bit :: remaining, determinant =>
      foldl_det_ne (step state bit) remaining
        (step_det_ne state bit determinant)

/-- Every finite parser product has a nonzero determinant. -/
theorem parse_det_ne (word : Word) :
    CCL.Chordal.Mat2.det (parse word).matrix ≠ 0 := by
  apply foldl_det_ne initialState word
  decide

/-- Hence the lower row of every parsed matrix is not identically zero. -/
theorem parse_lowerRow_ne (word : Word) :
    (parse word).matrix.c ≠ 0 ∨ (parse word).matrix.d ≠ 0 := by
  by_cases cZero : (parse word).matrix.c = 0
  · by_cases dZero : (parse word).matrix.d = 0
    · have determinantZero :
          CCL.Chordal.Mat2.det (parse word).matrix = 0 := by
        rw [CCL.Chordal.Mat2.det, cZero, dZero]
        simp only [mul_zero, sub_zero]
      exact (parse_det_ne word determinantZero).elim
    · exact Or.inr dZero
  · exact Or.inl cZero

end CCL.RawParser
