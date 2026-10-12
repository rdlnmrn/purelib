module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
-- Exposed finite searches retain the bounded-index absence certificate in their public bodies.
public import Purelib.Data.Fin
import Purelib.Data.Int.Arithmetic
import Purelib.Data.List.Map

import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Word.Surgery
import Purelib.Data.Vector.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Constructive chord intervals and unit-pivot selection

Finite occurrence splits retain their actual prefixes and suffixes. Cyclic
rotation preserves the balanced word's computed matrix, so an interlaced
pair can be found from that matrix without postulating a geometric basis.
-/

namespace Purelib.Topology.Surface.Word.Selection
open Purelib.Data.List

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.SignedWord

open Purelib.Topology.Surface.Word.Surgery

open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator (occurrences)
open Purelib.Topology.Surface.Word.Pairing
open Purelib.Topology.Surface.Word.Surgery (InterlacedWord IntegralWordSignature)

variable {count : Nat}

namespace SignedGenerator

set_option genInjectivity false in
/-- An actual occurrence of a signed letter with its retained prefix and suffix.

The prefix and suffix are retained from the supplied word. Their equation identifies the selected letter at that exact
split. -/
structure Occurrence (needle : SignedWord.SignedGenerator count) (word : List (SignedWord.SignedGenerator count)) where
  /-- Original prefix preceding the selected signed occurrence. -/ before : List (SignedWord.SignedGenerator count)
  /-- Original suffix following the selected signed occurrence. -/ after : List (SignedWord.SignedGenerator count)
  /-- The original word is exactly the retained prefix, selected letter and suffix. -/ equation : word = before ++
    needle :: after

constructive_injectivity Occurrence

/-- A total finite constructor from proved positive multiplicity.

The positive count ensures a head or tail occurrence exists. The search inspects the word from its beginning and retains
the first matching split. -/
@[expose] def locate (needle : SignedWord.SignedGenerator count) : (word : List (SignedWord.SignedGenerator count)) →
    0 < needle.occurrences word → SignedGenerator.Occurrence needle word
  | [], positive => (Nat.not_lt_zero _ positive).elim
  | head :: remaining, positive =>
      if same : head = needle then
        ⟨[], remaining, by rw [List.nil_append, same]⟩
      else
        let tail := Purelib.Topology.Surface.Word.Selection.SignedGenerator.locate needle remaining (by
          rw [Purelib.Topology.Surface.Word.SignedWord.SignedGenerator.occurrences, if_neg same, zero_add] at positive;
          exact positive)
        ⟨head :: tail.before, tail.after, by rw [List.cons_append, ← tail.equation]⟩

/-- The retained occurrence certifies membership in the original word.

Its split equation places the selected letter between the retained prefix and suffix, providing membership without a new
search. -/
theorem Occurrence.member {needle : SignedWord.SignedGenerator count} {word : List (SignedWord.SignedGenerator count)}
    (located : SignedGenerator.Occurrence needle word) : needle ∈ word := by
  rw [located.equation]
  exact Membership.mem_append.mpr (Or.inr List.mem_cons_self)

/-- If both orientations are absent, every original word letter has zero coefficient at that generator.

The two zero counts exclude either orientation at the displayed index. Every member therefore has zero coefficient at
that index. -/
theorem coefficient_zero_of_counts (word : List (SignedWord.SignedGenerator count)) (index : Fin count)
    (positive : SignedGenerator.occurrences ⟨index, false⟩ word = 0) (negative : SignedGenerator.occurrences ⟨index,
      true⟩ word = 0)
    (letter : SignedWord.SignedGenerator count) (member : letter ∈ word) : letter.coefficients index = 0 := by
  apply SignedGenerator.coefficient_zero_of_ne letter
  intro same
  have countPositive := SignedGenerator.occurrences_positive letter word member
  cases letter with
  | mk position reversed =>
      cases same
      cases reversed
      · rw [positive] at countPositive; omega
      · rw [negative] at countPositive; omega

end SignedGenerator

set_option genInjectivity false in
/-- A cyclic rotation retaining the exact two original word segments.

The two equations bind source and target to the same supplied segments in opposite concatenation order. -/
structure WordRotation (source target : List (SignedWord.SignedGenerator count)) where
  /-- Original leading segment moved to the end. -/ first : List (SignedWord.SignedGenerator count)
  /-- Original trailing segment moved to the start. -/ last : List (SignedWord.SignedGenerator count)
  /-- The original word is the leading segment followed by the trailing segment. -/ source_eq : source = first ++ last
  /-- The rotated word is the same trailing segment followed by the same leading segment. -/ target_eq : target = last
    ++ first

constructive_injectivity WordRotation

namespace WordRotation

variable {source target : List (SignedWord.SignedGenerator count)}

/-- Cyclic rotation preserves every signed letter's multiplicity.

Moving the leading segment past the trailing segment preserves the sum of their two counts for each supplied letter. -/
theorem occurrences (rotation : Selection.WordRotation source target) (needle : SignedWord.SignedGenerator count) :
    needle.occurrences target = needle.occurrences source := by
  rcases rotation with ⟨first, last, source_eq, target_eq⟩
  rw [source_eq, target_eq, SignedGenerator.occurrences_append, SignedGenerator.occurrences_append]
  omega

/-- Cyclic rotation preserves each total integer coefficient.

Each coefficient total is determined by the positive and negative occurrence counts. Rotation preserves those counts at
the displayed index. -/
theorem total (rotation : Selection.WordRotation source target) (index : Fin count) :
    Pairing.totalAt (target.map SignedGenerator.coefficients) index =
      Pairing.totalAt (source.map SignedGenerator.coefficients) index := by
  rw [SignedGenerator.total_eq_counts, SignedGenerator.total_eq_counts, rotation.occurrences, rotation.occurrences]

/-- Rotation preserves a pairing entry when both involved total coefficients vanish.

The two vanishing totals cancel the boundary contribution from exchanging the retained segments. -/
theorem pairing_at (rotation : Selection.WordRotation source target) (row column : Fin count)
    (rowClosed : Pairing.totalAt (source.map SignedGenerator.coefficients) row = 0)
    (columnClosed : Pairing.totalAt (source.map SignedGenerator.coefficients) column = 0) :
    Pairing.pairingAt (target.map SignedGenerator.coefficients) row column =
      Pairing.pairingAt (source.map SignedGenerator.coefficients) row column := by
  rcases rotation with ⟨first, last, source_eq, target_eq⟩
  rw [source_eq, Map.map_append] at rowClosed columnClosed
  rw [source_eq, target_eq, Map.map_append, Map.map_append]
  exact (Surgery.pairingAt_rotate _ _ row column rowClosed columnClosed).symm

/-- Rotation preserves every pairing entry of a balanced word.

Specializing the balanced totals at the two supplied indices gives equality of the corresponding pairing entry. -/
theorem pairing (rotation : Selection.WordRotation source target)
    (closed : ∀ index, Pairing.totalAt (source.map SignedGenerator.coefficients) index = 0) (row column : Fin count) :
    Pairing.pairingAt (target.map SignedGenerator.coefficients) row column =
      Pairing.pairingAt (source.map SignedGenerator.coefficients) row column :=
  rotation.pairing_at row column (closed row) (closed column)

/-- Rotation consumes the existing signature matrix; it does not rebuild the same quadratic data at a new cyclic
starting point.

The transported signature retains the supplied total, matrix and twice certificate. Only their readback equalities
change to the rotated word. -/
@[expose] def integral (rotation : Selection.WordRotation source target) (input : Surgery.IntegralWordSignature source)
    (closed : ∀ index, Pairing.totalAt (source.map SignedGenerator.coefficients) index = 0) :
    Surgery.IntegralWordSignature target where
  signature :=
    { total := input.signature.total
      total_eq := fun index => (input.signature.total_eq index).trans (rotation.total index).symm
      matrix := input.signature.matrix
      matrix_eq := fun row column => (input.signature.matrix_eq row column).trans (rotation.pairing closed row
        column).symm }
  matrix := input.matrix
  twice := input.twice

end WordRotation

namespace SignedGenerator.Occurrence

variable {needle : SignedWord.SignedGenerator count} {word : List (SignedWord.SignedGenerator count)}

/-- Rotate the original word to begin at its retained selected occurrence.

The selected letter starts the rotated word, followed by the retained suffix and prefix in that order. -/
@[expose] def rotation (located : SignedGenerator.Occurrence needle word) : Selection.WordRotation word (needle ::
  (located.after ++ located.before)) :=
  ⟨located.before, needle :: located.after, located.equation, List.cons_append.symm⟩

end SignedGenerator.Occurrence

set_option genInjectivity false in
/-- A displayed generator pair with its original inside and outside word segments.

The two retained segments separate opposite orientations of the displayed generator and determine the ordered chord
word. -/
structure ChordWord (count : Nat) where
  /-- Original generator whose positive and negative endpoints delimit the chord. -/ index : Fin count
  /-- Original occurrences strictly between the two displayed endpoints. -/ inside : List (SignedWord.SignedGenerator
    count)
  /-- Original occurrences after the negative endpoint in the displayed cyclic order. -/ outside : List
    (SignedWord.SignedGenerator count)

constructive_injectivity ChordWord

namespace ChordWord

/-- Form the original positive endpoint, inside segment, negative endpoint and outside segment.

The resulting word uses the supplied chord index and segments without selecting new letters or recomputing a split. -/
@[expose] def word (chord : Selection.ChordWord count) : List (SignedWord.SignedGenerator count) :=
  ⟨chord.index, false⟩ :: (chord.inside ++ (⟨chord.index, true⟩ :: chord.outside))

/-- Concatenate the retained inside and outside segments after removing the displayed pair.

The tail preserves both segment orders and removes exactly the displayed positive and negative endpoints. -/
@[expose] def tail (chord : Selection.ChordWord count) : List (SignedWord.SignedGenerator count) := chord.inside ++
  chord.outside

/-- The chord word has its tail multiplicities plus one occurrence of each endpoint orientation.

The two endpoint contributions are added to the occurrences in the retained tail at each supplied signed letter. -/
theorem occurrences (chord : Selection.ChordWord count) (needle : SignedWord.SignedGenerator count) :
    needle.occurrences chord.word = needle.occurrences chord.tail + (if needle.index = chord.index then 1 else 0) := by
  simp only [word, tail, SignedGenerator.occurrences, SignedGenerator.occurrences_append]
  have orientations := SignedGenerator.two_orientations needle chord.index
  omega

/-- Signed uniqueness excludes the displayed generator from the retained tail.

A tail occurrence of either orientation would add to its displayed endpoint and violate the count bound of one. -/
theorem tail_avoids (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (letter : SignedWord.SignedGenerator count) (member : letter ∈ chord.tail) : letter.index ≠ chord.index := by
  have positive := SignedGenerator.occurrences_positive letter chord.tail member
  have bounded := counts letter.index letter.reversed
  have same : (⟨letter.index, letter.reversed⟩ : SignedWord.SignedGenerator count) = letter := by cases letter; rfl
  rw [same, chord.occurrences] at bounded
  intro equal
  rw [if_pos equal] at bounded
  omega

/-- Both retained segments have zero coefficients at the displayed chord generator.

The signed count bounds exclude the chord generator from the tail. Membership in either segment then gives the stated
coefficient equality. -/
theorem segments_clear (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1) :
    (∀ letter ∈ chord.inside.map SignedGenerator.coefficients, letter chord.index = 0) ∧
    (∀ letter ∈ chord.outside.map SignedGenerator.coefficients, letter chord.index = 0) := by
  have clear (coefficients : Pairing.Coefficients count)
      (member : coefficients ∈ chord.tail.map SignedGenerator.coefficients) : coefficients chord.index = 0 := by
    rcases Map.mem_map.mp member with ⟨letter, member, equal⟩
    rw [← equal]
    exact SignedGenerator.coefficient_zero_of_ne letter chord.index (chord.tail_avoids counts letter member)
  constructor
  · intro letter member
    apply clear letter
    rw [tail, Map.map_append]
    exact Membership.mem_append.mpr (Or.inl member)
  · intro letter member
    apply clear letter
    rw [tail, Map.map_append]
    exact Membership.mem_append.mpr (Or.inr member)

/-- A chord row is twice the signed count strictly between its endpoints.

The count bounds make the chord-generator coefficients vanish on both segments. At a distinct column, the two endpoint
contributions reduce to twice the inside total. -/
theorem pairing_row (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (column : Fin count) (different : column ≠ chord.index) :
    Pairing.pairingAt (chord.word.map SignedGenerator.coefficients) chord.index column =
      2 * Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) column := by
  obtain ⟨inside, outside⟩ := chord.segments_clear counts
  have zero (reversed : Bool) := SignedGenerator.coefficient_zero_of_ne
    (⟨chord.index, reversed⟩ : SignedWord.SignedGenerator count) column (Ne.symm different)
  simp only [word, List.map_cons, Map.map_append, Surgery.pairingAt_append, Surgery.totalAt_append,
    Pairing.pairingAt, Pairing.totalAt, SignedGenerator.coefficient_self, zero,
    Surgery.totalAt_zero_of _ _ inside, Surgery.totalAt_zero_of _ _ outside,
    Surgery.pairingAt_zero_of _ _ _ inside, Surgery.pairingAt_zero_of _ _ _ outside, -eq_self]
  rw [if_neg (show false ≠ true from by intro same; cases same), if_pos (Eq.refl true)]
  simp only [zero_mul, mul_zero, zero_add, add_zero, Purelib.Data.Int.Arithmetic.sub_zero, one_mul, neg_mul, -eq_self]
  omega

/-- The inside segment inherits the original signed occurrence bound.

Its occurrence count is a nonnegative part of the count in the complete chord word, so the supplied bound of one remains
valid. -/
theorem inside_counts_le (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (index : Fin count) (reversed : Bool) : SignedGenerator.occurrences ⟨index, reversed⟩ chord.inside ≤ 1 := by
  have bounded := counts index reversed
  rw [chord.occurrences, tail, SignedGenerator.occurrences_append] at bounded
  omega

/-- Removing the two opposite chord endpoints preserves total coefficients.

The two endpoint orientations cancel at every column. Concatenating the retained inside and outside therefore preserves
the total. -/
theorem tail_total (chord : Selection.ChordWord count) (column : Fin count) :
    Pairing.totalAt (chord.tail.map SignedGenerator.coefficients) column =
      Pairing.totalAt (chord.word.map SignedGenerator.coefficients) column := by
  rw [SignedGenerator.total_eq_counts, SignedGenerator.total_eq_counts, chord.occurrences, chord.occurrences]
  dsimp only
  omega

end ChordWord

set_option genInjectivity false in
/-- The displayed cyclic rotation identifies a chord interval with the original word, including its precise starting
point.

The chord and rotation retain the supplied word and generator index. The rotation equations locate its two segments in
that word. -/
structure ChordAt (word : List (SignedWord.SignedGenerator count)) (index : Fin count) where
  /-- Retained chord and its actual intervening segments. -/ chord : Selection.ChordWord count
  /-- The retained chord belongs to the requested original generator index. -/ index_eq : chord.index = index
  /-- Exact cyclic position of the retained chord word in the original input. -/ rotation : Selection.WordRotation word
    chord.word

constructive_injectivity ChordAt

namespace ChordAt

variable {word : List (SignedWord.SignedGenerator count)} {index : Fin count}

/-- The selected chord rotation inherits the original signed uniqueness bound.

Rotation preserves occurrence counts, transferring the supplied uniqueness bound to the displayed chord word. -/
theorem counts (selected : Selection.ChordAt word index)
    (unique : ∀ position reversed, SignedGenerator.occurrences ⟨position, reversed⟩ word ≤ 1)
    (position : Fin count) (reversed : Bool) :
    SignedGenerator.occurrences ⟨position, reversed⟩ selected.chord.word ≤ 1 := by
  rw [selected.rotation.occurrences]
  exact unique position reversed

/-- A selected chord's integral row is the signed coefficient total strictly between its endpoints.

The cached matrix readback and chord rotation identify its row with half the doubled inside coefficient total at each
distinct column. -/
theorem integral_row (selected : Selection.ChordAt word index) (integral : Surgery.IntegralWordSignature word)
    (unique : ∀ position reversed, SignedGenerator.occurrences ⟨position, reversed⟩ word ≤ 1)
    (closed : ∀ position, Pairing.totalAt (word.map SignedGenerator.coefficients) position = 0)
    (column : Fin count) (different : column ≠ index) :
    integral.matrix index column = Pairing.totalAt (selected.chord.inside.map SignedGenerator.coefficients) column := by
  have interval := selected.chord.pairing_row (selected.counts unique) column
    (fun same => different (same.trans selected.index_eq))
  rw [selected.rotation.pairing closed, selected.index_eq, ← integral.spec] at interval
  omega

/-- Locate both opposite endpoints of a present balanced generator in the original word.

The returned chord retains the actual inside and outside segments and its precise cyclic position. -/
@[expose] def build (word : List (SignedWord.SignedGenerator count)) (index : Fin count)
    (closed : Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0)
    (positive : 0 < SignedGenerator.occurrences ⟨index, false⟩ word) : Selection.ChordAt word index :=
  let located := Selection.SignedGenerator.locate ⟨index, false⟩ word positive
  let rest := located.after ++ located.before
  have negative : 0 < SignedGenerator.occurrences ⟨index, true⟩ rest := by
    rw [SignedGenerator.total_eq_counts] at closed
    have preserved := located.rotation.occurrences (⟨index, true⟩ : SignedWord.SignedGenerator count)
    change SignedGenerator.occurrences ⟨index, true⟩ (⟨index, false⟩ :: rest) = _ at preserved
    rw [SignedGenerator.occurrences, if_neg (by intro equal; have := congrArg SignedGenerator.reversed equal; cases
      this), zero_add] at preserved
    omega
  let finish := Selection.SignedGenerator.locate ⟨index, true⟩ rest negative
  let chord : Selection.ChordWord count := ⟨index, finish.before, finish.after⟩
  { chord := chord
    index_eq := rfl
    rotation :=
      { first := located.before
        last := ⟨index, false⟩ :: located.after
        source_eq := located.equation
        target_eq := by
          change (⟨index, false⟩ :: (finish.before ++ ⟨index, true⟩ :: finish.after)) = _
          rw [← finish.equation, List.cons_append] } }

end ChordAt

namespace IntegralWordSignature

variable {word : List (SignedWord.SignedGenerator count)}

/-- A balanced generator absent in positive orientation has a zero integral matrix row.

Balance forces its negative count to vanish as well. Both orientations then have zero coefficients throughout the word.
-/
theorem row_zero_of_absent (integral : Surgery.IntegralWordSignature word) (row : Fin count)
    (closed : Pairing.totalAt (word.map SignedGenerator.coefficients) row = 0)
    (absent : SignedGenerator.occurrences ⟨row, false⟩ word = 0) (column : Fin count) :
    integral.matrix row column = 0 := by
  have negative : SignedGenerator.occurrences ⟨row, true⟩ word = 0 := by
    rw [SignedGenerator.total_eq_counts, absent] at closed
    omega
  have zero := Surgery.pairingAt_zero_of (word.map SignedGenerator.coefficients) row column (by
    intro coefficients member
    rcases Map.mem_map.mp member with ⟨letter, member, equal⟩
    rw [← equal]
    exact Selection.SignedGenerator.coefficient_zero_of_counts word row absent negative letter member)
  rw [← integral.spec] at zero
  omega

/-- A balanced word using each orientation at most once has only zero or oriented unit entries. This is derived from
actual chord intervals.

The actual chord interval has inside counts between zero and one for both orientations. Its signed difference bounds the
corresponding matrix entry. -/
theorem entry_bounds (integral : Surgery.IntegralWordSignature word)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0)
    (row column : Fin count) : -1 ≤ integral.matrix row column ∧ integral.matrix row column ≤ 1 := by
  by_cases same : column = row
  · have zero : integral.matrix row column = 0 := by rw [same, integral.diagonal]
    exact ⟨by omega, by omega⟩
  · by_cases absent : SignedGenerator.occurrences ⟨row, false⟩ word = 0
    · have zero := IntegralWordSignature.row_zero_of_absent integral row (closed row) absent column
      exact ⟨by omega, by omega⟩
    · let selected := Selection.ChordAt.build word row (closed row) (by omega)
      have interval := selected.integral_row integral unique closed column same
      rw [SignedGenerator.total_eq_counts] at interval
      have positive := selected.chord.inside_counts_le (selected.counts unique) column false
      have negative := selected.chord.inside_counts_le (selected.counts unique) column true
      exact ⟨by omega, by omega⟩

end IntegralWordSignature

set_option genInjectivity false in
/-- An actual interlaced cut together with its cyclic position in the input.

The retained cut and cyclic rotation bind the four ordered endpoints and intermediate segments to the supplied input
word. -/
structure InterlacedAt (word : List (SignedWord.SignedGenerator count)) where
  /-- Actual two-generator interlaced cut and its four retained segments. -/ cut : Surgery.InterlacedWord count
  /-- Exact cyclic identification of the original word with the displayed interlaced word. -/ rotation :
    Selection.WordRotation word cut.before

constructive_injectivity InterlacedAt

namespace InterlacedAt

variable {word : List (SignedWord.SignedGenerator count)}

/-- A positive unit matrix entry supplies both positively oriented first endpoints and both negatively oriented second
endpoints, with no search success or interlacing premise.

The chord-row formula forces an inside positive occurrence and excludes its negative orientation there. The retained
occurrence splits supply the ordered interlaced cut. -/
@[expose] def ofUnit (integral : Surgery.IntegralWordSignature word)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0)
    (row column : Fin count) (unit : integral.matrix row column = 1) : Selection.InterlacedAt word :=
  have different : column ≠ row := by
    intro same
    rw [same, integral.diagonal] at unit
    omega
  have present : 0 < SignedGenerator.occurrences ⟨row, false⟩ word := by
    by_cases absent : SignedGenerator.occurrences ⟨row, false⟩ word = 0
    · rw [Selection.IntegralWordSignature.row_zero_of_absent integral row (closed row) absent column] at unit; omega
    · omega
  let selected := Selection.ChordAt.build word row (closed row) present
  have insideTotal : Pairing.totalAt (selected.chord.inside.map SignedGenerator.coefficients) column = 1 :=
    (selected.integral_row integral unique closed column different).symm.trans unit
  have positive : 0 < SignedGenerator.occurrences ⟨column, false⟩ selected.chord.inside := by
    rw [SignedGenerator.total_eq_counts] at insideTotal
    omega
  have negative : 0 < SignedGenerator.occurrences ⟨column, true⟩ selected.chord.outside := by
    have tailClosed := (selected.chord.tail_total column).trans
      ((selected.rotation.total column).trans (closed column))
    rw [Selection.ChordWord.tail, Map.map_append, Surgery.totalAt_append, insideTotal,
      SignedGenerator.total_eq_counts] at tailClosed
    omega
  let first := Selection.SignedGenerator.locate ⟨column, false⟩ selected.chord.inside positive
  let last := Selection.SignedGenerator.locate ⟨column, true⟩ selected.chord.outside negative
  let cut : Surgery.InterlacedWord count :=
    ⟨selected.chord.index, column, fun same => different (same.symm.trans selected.index_eq),
      first.before, first.after, last.before, last.after⟩
  have before_eq : cut.before = selected.chord.word := by
    simp only [cut, InterlacedWord.before, Selection.ChordWord.word, first.equation, last.equation,
      Append.append_assoc, List.cons_append, -eq_self]
    rfl
  { cut := cut
    rotation :=
      { first := selected.rotation.first
        last := selected.rotation.last
        source_eq := selected.rotation.source_eq
        target_eq := before_eq.trans selected.rotation.target_eq } }

/-- A selected interlaced rotation inherits the original signed occurrence bounds.

Occurrence preservation transfers each count bound from the input word to the displayed interlaced word. -/
theorem counts (selected : Selection.InterlacedAt word)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (index : Fin count) (reversed : Bool) : SignedGenerator.occurrences ⟨index, reversed⟩ selected.cut.before ≤ 1 := by
  rw [selected.rotation.occurrences]
  exact unique index reversed

/-- A selected interlaced rotation preserves the original word's zero total coefficients.

Rotation preserves each integer total, so the supplied balanced input gives the corresponding zero total of the retained
cut. -/
theorem closed (selected : Selection.InterlacedAt word)
    (balanced : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0) (index : Fin count) :
    Pairing.totalAt (selected.cut.before.map SignedGenerator.coefficients) index = 0 :=
  (selected.rotation.total index).trans (balanced index)

end InterlacedAt

set_option genInjectivity false in
/-- Certified finite search result for a decidable predicate on bounded indices.

A found result retains its bounded index and predicate proof. An absent result proves the predicate fails at every
bounded index. -/
inductive FiniteWitness {size : Nat} (predicate : Fin size → Prop) where
  /-- Return a bounded index together with its predicate proof. -/ | found (index : Fin size) (satisfies : predicate
    index)
  /-- Certify that every bounded index fails the requested predicate. -/ | absent (missing : ∀ index, ¬ predicate index)

constructive_injectivity FiniteWitness

/-- Search bounded indices in order, returning an actual witness or pointwise absence certificate.

The procedure tests zero before recursing on successor indices. Its absence result retains the pointwise evidence from
those same tests. -/
@[expose] def findFinite : {size : Nat} → (predicate : Fin size → Prop) →
    [DecidablePred predicate] → Selection.FiniteWitness predicate
  | 0, _, _ => .absent (fun index => Fin.elim0 index)
  | _ + 1, predicate, _ =>
      if head : predicate 0 then .found 0 head
      else
        match Purelib.Topology.Surface.Word.Selection.findFinite (fun index => predicate index.succ) with
        | .found index satisfies => .found index.succ satisfies
        | .absent missing => .absent (Purelib.Data.Fin.cases_induction head missing)

set_option genInjectivity false in
/-- Certified search result for a positive unit entry of a finite integer matrix.

A found result retains both matrix indices and equality to one. An absent result excludes one at every supplied row and
column. -/
inductive UnitEntry {rows columns : Nat} (matrix : Fin rows → Fin columns → Int) where
  /-- Return the actual row and column with their positive unit-entry equality. -/ | found (row : Fin rows) (column :
    Fin columns) (unit : matrix row column = 1)
  /-- Certify that no entry of the original matrix equals one. -/ | absent (missing : ∀ row column, matrix row column ≠
    1)

constructive_injectivity UnitEntry

/-- Scan the original finite matrix by rows for an entry equal to one.

Each row is searched in column order before proceeding to the next row. The result retains the first unit entry or the
evidence that every tested entry differs from one. -/
@[expose] def findUnit {columns : Nat} : {rows : Nat} →
    (matrix : Fin rows → Fin columns → Int) → Selection.UnitEntry matrix
  | 0, _ => .absent (fun row => Fin.elim0 row)
  | _ + 1, matrix =>
      match Selection.findFinite (fun column => matrix 0 column = 1) with
      | .found column unit => .found 0 column unit
      | .absent missing =>
          match Purelib.Topology.Surface.Word.Selection.findUnit (fun row => matrix row.succ) with
          | .found row column unit => .found row.succ column unit
          | .absent remaining => .absent (Purelib.Data.Fin.cases_induction missing remaining)

set_option genInjectivity false in
/-- Both outcomes are certified: an actual interlaced cut, or the vanishing of every entry of the complete residual
matrix.

A handle retains the actual cut and its rotation. A residual outcome proves every entry of the supplied integral matrix
is zero. -/
inductive WordSelection {word : List (SignedWord.SignedGenerator count)} (integral : Surgery.IntegralWordSignature word)
  where
  /-- Return an actual interlaced cut of the original signed word. -/ | handle (selected : Selection.InterlacedAt word)
  /-- Certify that every entry of the retained residual integral matrix is zero. -/ | zero (entries : ∀ row column,
    integral.matrix row column = 0)

constructive_injectivity WordSelection

/-- Exhaustive selection on the cached matrix. Unique balanced signed words cannot get stuck at a nonzero nonunit
residual, unlike arbitrary integral alternating matrices. No generator-supplied successful search is required.

The cached matrix is scanned for a positive unit entry. Balance and signed uniqueness turn the scan result into an
actual interlaced handle or a complete zero residual certificate. -/
@[expose] def selectWord (word : List (SignedWord.SignedGenerator count)) (integral : Surgery.IntegralWordSignature
  word)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0) : Selection.WordSelection
      integral :=
  match Selection.findUnit (fun row column => integral.matrix row column) with
  | .found row column unit => .handle (Selection.InterlacedAt.ofUnit integral unique closed row column unit)
  | .absent missing => .zero (fun row column => by
      have bounds := Selection.IntegralWordSignature.entry_bounds integral unique closed row column
      have opposite := integral.skew row column
      have positive := missing row column
      have negative := missing column row
      omega)

end Purelib.Topology.Surface.Word.Selection
