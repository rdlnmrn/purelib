import CCL.Encoding.Decoder
import CCL.Boxes

/-!
# Deterministic parser for arbitrary raw CCL prefixes

This is the finite state machine from Section 7.1 of the CCL-1 paper, imported
as Proposition 10.1(iv) by the finite constructive FTA paper.  It retains
unfinished unary runs and zero, one, or two sector bits.  Every state carries
the product of its completed decoder blocks and a finite list of rational
constraints; its predicate is evaluated by a finite Boolean computation.
-/

namespace CCL
namespace RawParser

open GaussianRat

/-- Which radial bracket precedes the sector code currently being read. -/
inductive BlockKind where
  | initialHigh
  | initialLow
  | loop
deriving DecidableEq, Repr

/-- Exactly the three possible unfinished sector-code lengths. -/
inductive SectorBits where
  | zero
  | one (first : Bool)
  | two (first second : Bool)
deriving DecidableEq, Repr

namespace SectorBits

def word : SectorBits → Prefix.Word
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

/-- The sector table in the paper's fixed displayed order. -/
def sectorTable : List Sector :=
  [.east, .northEast, .north, .northWest,
    .west, .southWest, .south, .southEast]

/-- The finite list of sector rows compatible with an unfinished fragment. -/
def sectorCandidates (bits : SectorBits) : List Sector :=
  sectorTable.filter fun sector => bits.word <+: sector.code

theorem sectorCandidates_length (bits : SectorBits) :
    (sectorCandidates bits).length = match bits with
      | .zero => 8
      | .one _ => 4
      | .two _ _ => 2 := by
  cases bits with
  | zero => native_decide
  | one first => cases first <;> native_decide
  | two first second => cases first <;> cases second <;> native_decide

@[simp] theorem sectorCandidates_zero :
    sectorCandidates .zero = sectorTable := by
  native_decide

@[simp] theorem sectorCandidates_one_false :
    sectorCandidates (.one false) =
      [.east, .northEast, .north, .northWest] := by
  native_decide

@[simp] theorem sectorCandidates_one_true :
    sectorCandidates (.one true) =
      [.west, .southWest, .south, .southEast] := by
  native_decide

@[simp] theorem sectorCandidates_two_false_false :
    sectorCandidates (.two false false) = [.east, .northEast] := by
  native_decide

@[simp] theorem sectorCandidates_two_false_true :
    sectorCandidates (.two false true) = [.north, .northWest] := by
  native_decide

@[simp] theorem sectorCandidates_two_true_false :
    sectorCandidates (.two true false) = [.west, .southWest] := by
  native_decide

@[simp] theorem sectorCandidates_two_true_true :
    sectorCandidates (.two true true) = [.south, .southEast] := by
  native_decide

/-- Decode the third sector bit by the exact table (6.1). -/
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
        (fun sector => [first, second, third] <+: sector.code) =
      [sectorOfBits first second third] := by
  cases first <;> cases second <;> cases third <;> native_decide

/-- The five parser phases.  A sector fragment cannot contain three bits:
the third bit completes and applies its block immediately. -/
inductive Phase where
  | initial
  | highUnary (count : ℕ)
  | lowUnary (count : ℕ)
  | loopUnary (count : ℕ)
  | sector (kind : BlockKind) (exponent : ℕ) (bits : SectorBits)
deriving DecidableEq, Repr

namespace Phase

/-- Current unary count, or zero outside a unary phase. -/
def counter : Phase → ℕ
  | .highUnary count => count
  | .lowUnary count => count
  | .loopUnary count => count
  | .sector _ exponent _ => exponent
  | .initial => 0

end Phase

/-- Identity decoder before the first complete block. -/
def identityMatrix : Mat2 GaussianRat := ⟨1, 0, 0, 1⟩

/-- The complete decoder block selected by a parser phase. -/
def blockMatrix (kind : BlockKind) (exponent : ℕ) (sector : Sector) :
    Mat2 GaussianRat :=
  match kind with
  | .initialLow => CCLDecoder.lowBlock exponent sector
  | .initialHigh | .loop => CCLDecoder.regularBlock exponent sector

/-- Normalized annulus value on which the sector table is evaluated. -/
def normalizedValue (kind : BlockKind) (exponent : ℕ)
    (value : GaussianRat) : GaussianRat :=
  match kind with
  | .initialLow => natPow gamma exponent * value
  | .initialHigh | .loop => value * inv (natPow gamma exponent)

/-- The exact radial bracket from table (7.2) after its delimiter. -/
def radialBracket (kind : BlockKind) (exponent : ℕ)
    (value : GaussianRat) : Prop :=
  match kind with
  | .initialHigh =>
      (2 : ℚ) ^ exponent ≤ normSq value ∧
        normSq value < (2 : ℚ) ^ (exponent + 1)
  | .initialLow =>
      1 ≤ (2 : ℚ) ^ exponent * normSq value ∧
        (2 : ℚ) ^ exponent * normSq value < 2
  | .loop =>
      (2 : ℚ) ^ exponent < normSq value ∧
        normSq value ≤ (2 : ℚ) ^ (exponent + 1)

instance radialBracketDecidable (kind : BlockKind) (exponent : ℕ)
    (value : GaussianRat) : Decidable (radialBracket kind exponent value) := by
  cases kind <;> simp only [radialBracket] <;> infer_instance

/-- Exact predicate of one completed raw block on its pre-normalization value. -/
def fullBlockHolds (kind : BlockKind) (exponent : ℕ) (sector : Sector)
    (value : GaussianRat) : Prop :=
  radialBracket kind exponent value ∧
    sector.Holds (normalizedValue kind exponent value)

instance sectorHoldsDecidable (sector : Sector) (value : GaussianRat) :
    Decidable (sector.Holds value) := by
  cases sector <;> simp only [Sector.Holds] <;> infer_instance

instance fullBlockHoldsDecidable (kind : BlockKind) (exponent : ℕ)
    (sector : Sector) (value : GaussianRat) :
    Decidable (fullBlockHolds kind exponent sector value) := by
  cases kind <;>
    simp only [fullBlockHolds, radialBracket, normalizedValue] <;>
    infer_instance

/-- A completed historical block, expressed as a rational homography of the
current affine tail. -/
structure Constraint where
  matrix : Mat2 GaussianRat
  kind : BlockKind
  exponent : ℕ
  sector : Sector
deriving DecidableEq, Repr

namespace Constraint

/-- Precompose a historical constraint when another decoder block completes. -/
def precompose (constraint : Constraint) (block : Mat2 GaussianRat) : Constraint :=
  { constraint with matrix := Mat2.mul constraint.matrix block }

/-- A historical constraint includes the exact nonzero denominator required
to evaluate its affine homography. -/
def Holds (constraint : Constraint) (tail : GaussianRat) : Prop :=
  constraint.matrix.c * tail + constraint.matrix.d ≠ 0 ∧
    fullBlockHolds constraint.kind constraint.exponent constraint.sector
      (RatBox.homographic constraint.matrix tail)

instance holdsDecidable (constraint : Constraint) (tail : GaussianRat) :
    Decidable (constraint.Holds tail) := by
  unfold Holds
  infer_instance

end Constraint

/-- The active unfinished fragment predicate from table (7.2). -/
def activeHolds : Phase → GaussianRat → Prop
  | .initial, _ => True
  | .highUnary count, value => (2 : ℚ) ^ count ≤ normSq value
  | .lowUnary 0, value => normSq value < 2
  | .lowUnary (count + 1), value =>
      (2 : ℚ) ^ count * normSq value < 1
  | .loopUnary count, value => (2 : ℚ) ^ count < normSq value
  | .sector kind exponent bits, value =>
      radialBracket kind exponent value ∧
        ∃ sector ∈ sectorCandidates bits,
          sector.Holds (normalizedValue kind exponent value)

instance activeHoldsDecidable (phase : Phase) (value : GaussianRat) :
    Decidable (activeHolds phase value) := by
  cases phase with
  | initial => simp only [activeHolds]; infer_instance
  | highUnary count => simp only [activeHolds]; infer_instance
  | lowUnary count =>
      cases count <;> simp only [activeHolds] <;> infer_instance
  | loopUnary count => simp only [activeHolds]; infer_instance
  | sector kind exponent bits => simp only [activeHolds]; infer_instance

/-- Complete finite parser state after some raw prefix. -/
structure State where
  phase : Phase
  matrix : Mat2 GaussianRat
  history : List Constraint
deriving DecidableEq, Repr

/-- State before reading any bit. -/
def initialState : State := ⟨.initial, identityMatrix, []⟩

/-- Apply a completed sector code, update the decoder product, and precompose
every retained historical constraint with the new block. -/
def completeSector (state : State) (kind : BlockKind) (exponent : ℕ)
    (first second third : Bool) : State :=
  let sector := sectorOfBits first second third
  let block := blockMatrix kind exponent sector
  let newest : Constraint := ⟨block, kind, exponent, sector⟩
  { phase := .loopUnary 0
    matrix := Mat2.mul state.matrix block
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

/-- Parse every raw finite word by a bounded left fold. -/
def parse (word : Prefix.Word) : State := word.foldl step initialState

namespace State

/-- The finite conjunction of all completed and active rational constraints. -/
def Holds (state : State) (tail : GaussianRat) : Prop :=
  (∀ constraint ∈ state.history, constraint.Holds tail) ∧
    activeHolds state.phase tail

/-- Executable Boolean evaluator for the parser predicate. -/
def holdsBool (state : State) (tail : GaussianRat) : Bool :=
  (state.history.all fun constraint => decide (constraint.Holds tail)) &&
    decide (activeHolds state.phase tail)

theorem holdsBool_eq_true (state : State) (tail : GaussianRat) :
    state.holdsBool tail = true ↔ state.Holds tail := by
  simp [holdsBool, Holds]

/-- Canonical tagged truncation coordinate (7.3), before retaining the tag. -/
def truncation (state : State) : Proj GaussianRat :=
  Mat2.act state.matrix (Proj.omega : Proj GaussianRat)

end State

/-- A unary counter can increase by at most one on a raw-bit transition. -/
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
          | two first second => simp [step, completeSector, Phase.counter]

/-- For a parsed prefix, the stored unary count is bounded by its bit length. -/
theorem parse_counter_le (word : Prefix.Word) :
    (parse word).phase.counter ≤ word.length := by
  induction word using List.reverseRecOn with
  | nil => simp [parse, initialState, Phase.counter]
  | append_singleton word bit ih =>
      rw [parse, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_singleton]
      exact (step_counter_le (parse word) bit).trans (by omega)

theorem det_mul (left right : Mat2 GaussianRat) :
    (Mat2.mul left right).det = left.det * right.det := by
  ext <;>
    simp only [Mat2.det, Mat2.mul, mul_re, mul_im, add_re, add_im,
      sub_re, sub_im] <;>
    ring

theorem natPow_gamma_ne (exponent : ℕ) : natPow gamma exponent ≠ 0 := by
  intro hzero
  have hnorm := normSq_natPow gamma exponent
  rw [hzero, normSq_zero, normSq_gamma] at hnorm
  have hpositive : 0 < (2 : ℚ) ^ exponent := pow_pos (by norm_num) _
  linarith

theorem blockMatrix_det_ne (kind : BlockKind) (exponent : ℕ) (sector : Sector) :
    (blockMatrix kind exponent sector).det ≠ 0 := by
  cases kind with
  | initialHigh =>
      rw [blockMatrix, CCLDecoder.regularBlock_det]
      exact neg_ne_zero.mpr (natPow_gamma_ne (exponent + 1))
  | initialLow =>
      rw [blockMatrix, CCLDecoder.lowBlock_det]
      exact neg_ne_zero.mpr (natPow_gamma_ne (exponent + 1))
  | loop =>
      rw [blockMatrix, CCLDecoder.regularBlock_det]
      exact neg_ne_zero.mpr (natPow_gamma_ne (exponent + 1))

theorem step_det_ne (state : State) (bit : Bool) (hdet : state.matrix.det ≠ 0) :
    (step state bit).matrix.det ≠ 0 := by
  cases state with
  | mk phase matrix history =>
      cases phase with
      | initial => cases bit <;> simpa [step] using hdet
      | highUnary count => cases bit <;> simpa [step] using hdet
      | lowUnary count => cases bit <;> simpa [step] using hdet
      | loopUnary count => cases bit <;> simpa [step] using hdet
      | sector kind exponent bits =>
          cases bits with
          | zero => simpa [step] using hdet
          | one first => simpa [step] using hdet
          | two first second =>
              change (Mat2.mul matrix
                (blockMatrix kind exponent
                  (sectorOfBits first second bit))).det ≠ 0
              rw [det_mul]
              exact mul_ne_zero hdet
                (blockMatrix_det_ne kind exponent
                  (sectorOfBits first second bit))

/-- Every finite parser product is invertible. -/
theorem parse_det_ne (word : Prefix.Word) : (parse word).matrix.det ≠ 0 := by
  induction word using List.reverseRecOn with
  | nil =>
      intro h
      have hre := congrArg GaussianRat.re h
      norm_num [parse, initialState, identityMatrix, Mat2.det] at hre
  | append_singleton word bit ih =>
      rw [parse, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact step_det_ne (parse word) bit ih

/-- In particular, the lower row of every parsed decoder matrix is nonzero,
which is exactly the premise consumed by the finite denominator branch. -/
theorem parse_lowerRow_ne (word : Prefix.Word) :
    (parse word).matrix.c ≠ 0 ∨ (parse word).matrix.d ≠ 0 := by
  by_contra hrow
  have hc : (parse word).matrix.c = 0 := by
    by_contra hc
    exact hrow (Or.inl hc)
  have hd : (parse word).matrix.d = 0 := by
    by_contra hd
    exact hrow (Or.inr hd)
  apply parse_det_ne word
  rw [Mat2.det, hc, hd]
  simp

/-- The ten-bit example from Section 7.1: one complete block followed by the
raw fragment `110`, i.e. loop exponent two with no sector bit yet. -/
theorem tenBitExample :
    let state := parse
      [true, true, true, false, true, false, true, true, true, false]
    state.phase = .sector .loop 2 .zero ∧
      state.matrix = CCLDecoder.regularBlock 3 .southWest := by
  native_decide

end RawParser
end CCL
