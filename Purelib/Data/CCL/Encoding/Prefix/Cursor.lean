module

public import Purelib.Data.CCL.Encoding.Prefix.Enclosure
public import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.Inverse
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate

/-!
# Exact finite canonical affine-prefix cursors

The finite cursor retains the original exposed word, parser and inverse
matrix together with one exact affine rational reading and its local tail.
Each request advances the owned half-open parser decision. A terminal result
certifies that no further affine bit is admissible; it does not append
productive residual padding or assert an affine interpretation of infinity.
-/

public section

namespace Purelib.Data.CCL.Encoding.Prefix

open Purelib
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

set_option genInjectivity false in
/-- Finite canonical data retain one affine reading and its exact word, parser, inverse chart and current tail. -/
structure Cursor where
  /-- The fixed Gaussian-rational reading of this same cursor. -/ point : Basic.Canonical
  /-- The exact already exposed affine raw prefix. -/ word : List Bool
  /-- The same retained parser state of that word. -/ state : Parser.State
  /-- The same retained inverse-chart matrix. -/ inverseMatrix : Matrix2.GaussianMatrix
  /-- The exact local affine tail in that original chart. -/ tail : Basic.Canonical

namespace Cursor

set_option genInjectivity false in
/-- A finite canonical cursor owns its exact parser, inverse chart and complete affine representation. -/
structure Valid (cursor : Cursor) : Prop where
  /-- The supplied parser belongs to this exact original word. -/ stateSpec :
    cursor.state = Parser.State.parse cursor.word
  /-- The retained parser chart is nonsingular. -/ determinant : Matrix2.Matrix2.determinant cursor.state.matrix ≠ 0
  /-- The inverse cache belongs to this same original matrix. -/ inverseSpec :
    cursor.inverseMatrix = Matrix2.BoundaryAdjugate.adjugate cursor.state.matrix
  /-- The cached tail is the reading through this same retained inverse chart. -/ tailSpec :
    cursor.tail = Homography.Basic.homographic cursor.inverseMatrix cursor.point
  /-- The exact current tail satisfies every original half-open affine parser constraint. -/ represents :
    Parser.Semantics.State.Represents cursor.state cursor.point cursor.tail

/-- Construct the native affine zero cursor with its original empty parser and cached identity chart.

This cursor supports every finite initial-low unary request. Zero is outside
the nonzero-numerator domain of automatic terminal encoding.
-/
@[expose] def zero : Cursor :=
  ⟨0, [], Parser.State.initialState,
    Matrix2.BoundaryAdjugate.adjugate Parser.State.initialState.matrix, 0⟩

/-- The named zero cursor retains its exact original affine parser and tail certificates. -/
theorem zero_valid : zero.Valid :=
  ⟨rfl, Parser.State.parse_det_ne [], rfl, by decide, Parser.Semantics.State.initialState_represents 0⟩

/-- Restore an exact canonical cursor from a retained enclosure realization without recomputing its tail or caches. -/
@[expose] def ofRealization {enclosure : Enclosure} (realization : enclosure.Realization) :
    {cursor : Cursor // cursor.Valid} :=
  ⟨⟨realization.point, enclosure.word, enclosure.state, enclosure.inverseMatrix, realization.tail⟩,
    enclosure.stateSpec, enclosure.determinant, enclosure.inverseSpec, realization.tailSpec, realization.represents⟩

/-- Realize a supplied point in an original prefix enclosure using its same cached inverse chart. -/
def ofEnclosure (enclosure : Enclosure) (point : Basic.Canonical) (inside : enclosure.box.Contains point) :
    {cursor : Cursor // cursor.Valid} :=
  ⟨⟨point, enclosure.word, enclosure.state, enclosure.inverseMatrix, enclosure.tail point⟩,
    enclosure.stateSpec, enclosure.determinant, enclosure.inverseSpec, rfl, enclosure.tail_represents inside⟩

/-- The original enclosure constructor retains exactly its supplied affine point. -/
theorem ofEnclosure_point (enclosure : Enclosure) (point : Basic.Canonical) (inside : enclosure.box.Contains point) :
    (ofEnclosure enclosure point inside).val.point = point := by
  unfold ofEnclosure
  rfl

/-- A valid finite canonical cursor represents its exact exposed word at that same fixed affine reading. -/
theorem represented (cursor : Cursor) (valid : cursor.Valid) :
    Parser.Semantics.Prefix.Represented cursor.word cursor.point :=
  ⟨cursor.tail, valid.stateSpec ▸ valid.represents⟩

/-- Every valid affine-zero prefix admits another original canonical bit.

A longer finite initial-low word represents that same zero. Original prefix
uniqueness identifies its next bit after this cursor's exact exposed word.
-/
theorem canStep_zero (cursor : Cursor) (valid : cursor.Valid) (pointZero : cursor.point = 0) :
    ∃ bit, Parser.Semantics.Prefix.CanStep cursor.state cursor.point bit := by
  let longer := false :: List.replicate cursor.word.length true
  have longerRepresents := Parser.Semantics.Prefix.represented_zero_low cursor.word.length
  have length : cursor.word.length < longer.length := by
    change cursor.word.length < (List.replicate cursor.word.length true).length + 1
    rewrite [Data.List.Replicate.length_replicate]
    exact Nat.lt_succ_self _
  have original : Parser.Semantics.Prefix.Represented cursor.word 0 :=
    pointZero ▸ cursor.represented valid
  rcases Parser.Semantics.Prefix.represented_prefix_of_length_le
    (Nat.le_of_lt length) original longerRepresents with ⟨suffix, same⟩
  cases suffix with
  | nil =>
      have sizes := congrArg List.length same
      rewrite [Data.List.Append.length_append] at sizes
      change cursor.word.length + 0 = longer.length at sizes
      have sameLength : cursor.word.length = longer.length :=
        (Nat.add_zero _).symm.trans sizes
      exact (Nat.not_lt_of_ge (Nat.le_of_eq sameLength.symm) length).elim
  | cons bit remaining =>
      have child : (cursor.word ++ [bit]).IsPrefix longer :=
        ⟨remaining, (Data.List.Append.append_assoc cursor.word [bit] remaining).trans same⟩
      rcases Parser.Semantics.Prefix.represented_of_prefix child longerRepresents with ⟨tail, represented⟩
      refine ⟨bit, tail, ?_⟩
      rewrite [Parser.State.parse_append_singleton] at represented
      exact pointZero.symm ▸ (valid.stateSpec.symm ▸ represented)

set_option genInjectivity false in
/-- One exact canonical advance retains the actual new bit and its same next parser and rational cursor. -/
structure Advance (earlier : Cursor) where
  /-- The actual next bit selected by the original local parser decision. -/ bit : Bool
  /-- The finite next cursor with its computed affine tail. -/ next : Cursor
  /-- The same next cursor has its original affine validity certificate. -/ valid : next.Valid
  /-- The same rational reading is retained. -/ pointEq : next.point = earlier.point
  /-- The exposed word appends exactly this actual bit. -/ wordEq : next.word = earlier.word ++ [bit]
  /-- The next parser is one step from the same cached original parser. -/ stateEq :
    next.state = Parser.State.step earlier.state bit
  /-- Every admissible next bit at the original parents equals the same selected bit. -/ unique :
    ∀ other, Parser.Semantics.Prefix.CanStep earlier.state earlier.point other → other = bit

/-- Construct one certified canonical bit using the actual previous parser and inverse-chart cache.

When the parser matrix is unchanged, retain both the original inverse matrix
and its cached tail. A completed chart transition computes their new values
once; phase and exposed-word updates remain those of the original parser.
-/
private def advance (earlier : Cursor) (valid : earlier.Valid) (bit : Bool)
    (possible : Parser.Semantics.Prefix.CanStep earlier.state earlier.point bit)
    (unique : ∀ other, Parser.Semantics.Prefix.CanStep earlier.state earlier.point other → other = bit) :
    Advance earlier := by
  let state := Parser.State.step earlier.state bit
  let word := earlier.word ++ [bit]
  let chart : Matrix2.GaussianMatrix × Basic.Canonical :=
    if state.matrix = earlier.state.matrix then ⟨earlier.inverseMatrix, earlier.tail⟩
    else
      let inverse := Matrix2.BoundaryAdjugate.adjugate state.matrix
      ⟨inverse, Homography.Basic.homographic inverse earlier.point⟩
  have inverseSpec : chart.1 = Matrix2.BoundaryAdjugate.adjugate state.matrix := by
    unfold chart
    split
    · rename_i same
      exact valid.inverseSpec.trans (congrArg Matrix2.BoundaryAdjugate.adjugate same.symm)
    · rfl
  have tailSpec : chart.2 = Homography.Basic.homographic chart.1 earlier.point := by
    unfold chart
    split
    · exact valid.tailSpec
    · rfl
  have determinant := Parser.State.step_det_ne earlier.state bit valid.determinant
  have represents : Parser.Semantics.State.Represents state earlier.point chart.2 := by
    exact tailSpec.symm ▸
      ((congrArg (fun matrix => Homography.Basic.homographic matrix earlier.point) inverseSpec).symm ▸
        Parser.represents_inverse_tail_of_represented state earlier.point determinant possible)
  have stateSpec : state = Parser.State.parse word :=
    (congrArg (fun state => Parser.State.step state bit) valid.stateSpec).trans
      (Parser.State.parse_append_singleton earlier.word bit).symm
  let next : Cursor := ⟨earlier.point, word, state, chart.1, chart.2⟩
  exact ⟨bit, next, ⟨stateSpec, determinant, inverseSpec, tailSpec, represents⟩, rfl, rfl, rfl, unique⟩

set_option genInjectivity false in
/-- Exact canonical stepping either advances an admissible affine bit or proves the current prefix terminal. -/
inductive Step (cursor : Cursor) where
  /-- The actual canonical parser selected this certified next bit. -/ | advanced (result : Advance cursor)
  /-- No Boolean next bit retains an affine representation of this same original reading. -/ | terminal
      (noStep : ∀ bit, ¬ Parser.Semantics.Prefix.CanStep cursor.state cursor.point bit)

/-- Run the original local parser decision once, preserving canonical terminal and half-open boundary conventions. -/
def nextBit (cursor : Cursor) (valid : cursor.Valid) : Step cursor :=
  match Parser.Next.decideLocal cursor.state cursor.point cursor.tail valid.determinant valid.represents with
  | .next bit possible unique => .advanced (advance cursor valid bit possible unique)
  | .terminal noStep => .terminal noStep

set_option genInjectivity false in
/-- A finite canonical bit request retains its exact suffix and either pays the count or reports an affine terminal. -/
structure Result (earlier : Cursor) (count : Nat) where
  /-- The actual returned finite canonical cursor. -/ next : Cursor
  /-- The returned cursor has its same complete affine representation. -/ valid : next.Valid
  /-- The actual fixed rational reading is unchanged. -/ pointEq : next.point = earlier.point
  /-- The exact newly returned finite suffix in order. -/ suffix : List Bool
  /-- The exact previously exposed word persists before that same suffix. -/ wordEq : next.word = earlier.word ++ suffix
  /-- At most the requested additional bits have been exposed. -/ lengthBound : suffix.length ≤ count
  /-- The full count is paid unless the same returned affine prefix has no admissible next bit. -/ completion :
    suffix.length = count ∨ ∀ bit, ¬ Parser.Semantics.Prefix.CanStep next.state next.point bit

/-- Execute a finite canonical bit request, stopping explicitly at an affine terminal without adding padding. -/
def request : (cursor : Cursor) → cursor.Valid → (count : Nat) → Result cursor count
  | cursor, valid, 0 =>
      ⟨cursor, valid, rfl, [], (Data.List.Append.append_nil cursor.word).symm, Nat.le_refl _, .inl rfl⟩
  | cursor, valid, count + 1 =>
      match cursor.nextBit valid with
      | .terminal noStep =>
          ⟨cursor, valid, rfl, [], (Data.List.Append.append_nil cursor.word).symm, Nat.zero_le _, .inr noStep⟩
      | .advanced advanced =>
          let later := request advanced.next advanced.valid count
          { next := later.next
            valid := later.valid
            pointEq := later.pointEq.trans advanced.pointEq
            suffix := advanced.bit :: later.suffix
            wordEq := later.wordEq.trans
              ((congrArg (fun word => word ++ later.suffix) advanced.wordEq).trans
                (Data.List.Append.append_assoc cursor.word [advanced.bit] later.suffix))
            lengthBound := Nat.succ_le_succ later.lengthBound
            completion := match later.completion with
              | .inl paid => .inl (congrArg Nat.succ paid)
              | .inr terminal => .inr terminal }

/-- Every finite request at a valid zero cursor pays its entire original bit count. -/
theorem request_zero_paid (cursor : Cursor) (valid : cursor.Valid) (pointZero : cursor.point = 0) (count : Nat) :
    (cursor.request valid count).suffix.length = count := by
  let result := cursor.request valid count
  cases result.completion with
  | inl paid => exact paid
  | inr terminal =>
      rcases result.next.canStep_zero result.valid (result.pointEq.trans pointZero) with ⟨bit, possible⟩
      exact (terminal bit possible).elim

namespace Result

/-- Every canonical bit request preserves the exact original exposed word. -/
theorem wordPrefix {earlier : Cursor} {count : Nat} (result : Result earlier count) :
    earlier.word.IsPrefix result.next.word := ⟨result.suffix, result.wordEq.symm⟩

/-- Every returned canonical prefix represents the same original affine rational reading. -/
theorem represented {earlier : Cursor} {count : Nat} (result : Result earlier count) :
    Parser.Semantics.Prefix.Represented result.next.word earlier.point :=
  result.pointEq ▸ result.next.represented result.valid

end Result

end Cursor

end Purelib.Data.CCL.Encoding.Prefix

end
