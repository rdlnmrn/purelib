module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.Int.Division
import Purelib.Algebra.Ring.Int
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.UnitPivot
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Exact handle surgery on an interlaced signed word

The four intervening segments in `p U q V (-p) W (-q) X` reconnect as
`U X W V`. The occurrence and matrix identities below concern that literal
word operation, not a transported definition of a symplectic form.
-/

namespace Purelib.Topology.Surface.Word.Surgery
open Purelib
open Purelib.Data.List
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra.Alternating.UnitPivot
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.SignedWord

open Purelib.Algebra

open Purelib.Topology.Surface.Word.Pairing
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator (occurrences coefficients)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)

section Word

-- Retain the original Surface.Word.Surgery.Word API names.

variable {count : Nat}

/-- Concatenating coefficient words adds their total at each generator.

Structural induction retains each original coefficient row. The scalar
integer addition identity transports its unchanged tail total. -/
theorem totalAt_append (first last : List (Pairing.Coefficients count)) (index : Fin count) :
    Pairing.totalAt (first ++ last) index = Pairing.totalAt first index + Pairing.totalAt last index := by
  induction first with
  | nil => rw [List.nil_append, Pairing.totalAt, Data.Int.Arithmetic.zero_add]
  | cons letter remaining ih =>
      rw [List.cons_append, Pairing.totalAt, Pairing.totalAt, ih]
      exact (Data.Int.Arithmetic.add_assoc _ _ _).symm

/-- Concatenation adds the two pairing matrices and their ordered cross-term. -/
theorem pairingAt_append (first last : List (Pairing.Coefficients count)) (row column : Fin count) :
    Pairing.pairingAt (first ++ last) row column = Pairing.pairingAt first row column + Pairing.pairingAt last row
      column +
      Pairing.totalAt first row * Pairing.totalAt last column - Pairing.totalAt last row * Pairing.totalAt first column
        := by
  induction first with
  | nil => rw [List.nil_append, Pairing.pairingAt, Pairing.totalAt, Pairing.totalAt]; ring1
  | cons letter remaining ih =>
      rw [List.cons_append, Pairing.pairingAt, Pairing.pairingAt, Pairing.totalAt, Pairing.totalAt, totalAt_append,
        totalAt_append, ih]
      ring1

/-- A coordinate zero on every original letter has zero word total. -/
theorem totalAt_zero_of (word : List (Pairing.Coefficients count)) (index : Fin count)
    (zero : ∀ letter ∈ word, letter index = 0) : Pairing.totalAt word index = 0 := by
  induction word with
  | nil => rfl
  | cons letter remaining ih =>
      rw [Pairing.totalAt, zero letter List.mem_cons_self, ih (fun entry member => zero entry (List.mem_cons_of_mem _
        member))]
      rfl

/-- A coordinate zero on every original letter gives a zero pairing row. -/
theorem pairingAt_zero_of (word : List (Pairing.Coefficients count)) (row column : Fin count)
    (zero : ∀ letter ∈ word, letter row = 0) : Pairing.pairingAt word row column = 0 := by
  induction word with
  | nil => rfl
  | cons letter remaining ih =>
      have tail : ∀ entry ∈ remaining, entry row = 0 := fun entry member => zero entry (List.mem_cons_of_mem _ member)
      rw [Pairing.pairingAt, zero letter List.mem_cons_self, totalAt_zero_of remaining row tail, ih tail]
      ring1

/-- Changing the cyclic start of a balanced coefficient word changes no matrix entry. This is false for a general
unbalanced word. -/
theorem pairingAt_rotate (first last : List (Pairing.Coefficients count)) (row column : Fin count)
    (rowClosed : Pairing.totalAt (first ++ last) row = 0) (columnClosed : Pairing.totalAt (first ++ last) column = 0) :
    Pairing.pairingAt (first ++ last) row column = Pairing.pairingAt (last ++ first) row column := by
  rw [totalAt_append] at rowClosed columnClosed
  rw [pairingAt_append, pairingAt_append]
  have rowLast : Pairing.totalAt last row = -Pairing.totalAt first row := by omega
  have columnLast : Pairing.totalAt last column = -Pairing.totalAt first column := by omega
  rw [rowLast, columnLast]
  ring1

/-- The matrix change caused by reconnecting four balanced-total segments. -/
theorem pairingAt_reconnect (u v w x : List (Pairing.Coefficients count)) (row column : Fin count)
    (rowClosed : Pairing.totalAt (u ++ v ++ w ++ x) row = 0)
    (columnClosed : Pairing.totalAt (u ++ v ++ w ++ x) column = 0) :
    Pairing.pairingAt (u ++ x ++ w ++ v) row column = Pairing.pairingAt (u ++ v ++ w ++ x) row column -
      2 * ((Pairing.totalAt u row + Pairing.totalAt v row) * (Pairing.totalAt v column + Pairing.totalAt w column) -
        (Pairing.totalAt v row + Pairing.totalAt w row) * (Pairing.totalAt u column + Pairing.totalAt v column)) := by
  simp only [totalAt_append] at rowClosed columnClosed
  have rowX : Pairing.totalAt x row = -(Pairing.totalAt u row + Pairing.totalAt v row + Pairing.totalAt w row) := by
    omega
  have columnX : Pairing.totalAt x column = -(Pairing.totalAt u column + Pairing.totalAt v column + Pairing.totalAt w
    column) := by omega
  simp only [pairingAt_append, totalAt_append]
  rw [rowX, columnX]
  ring1

end Word

namespace SignedGenerator

variable {count : Nat}

/-- Concatenating signed words adds each exact signed multiplicity.

Each original head contributes its retained zero-or-one indicator.
Natural addition transports the unchanged tail multiplicity across the
concatenation. -/
theorem occurrences_append (needle : SignedWord.SignedGenerator count) (first last : List (SignedWord.SignedGenerator
  count)) :
    SignedGenerator.occurrences needle (first ++ last) = SignedGenerator.occurrences needle first +
      SignedGenerator.occurrences needle last := by
  induction first with
  | nil => rw [List.nil_append, SignedGenerator.occurrences, Nat.zero_add]
  | cons letter remaining ih =>
      rw [List.cons_append, SignedGenerator.occurrences, SignedGenerator.occurrences, ih]
      exact (Nat.add_assoc _ _ _).symm

/-- A member of the original signed word has positive occurrence count.

The original head occurrence contributes one. A retained tail occurrence
has positive count by induction, and the current head contributes a
nonnegative natural indicator. -/
theorem occurrences_positive (letter : SignedWord.SignedGenerator count) (word : List (SignedWord.SignedGenerator
  count))
    (member : letter ∈ word) : 0 < SignedGenerator.occurrences letter word := by
  induction word with
  | nil => nomatch member
  | cons head remaining ih =>
      rw [SignedGenerator.occurrences]
      cases member with
      | head =>
          rw [if_pos rfl, Nat.one_add]
          exact Nat.zero_lt_succ _
      | tail _ member =>
          exact Nat.lt_of_lt_of_le (ih member) (Nat.le_add_left _ _)

/-- The two orientation indicators sum to the indicator of the original generator index.

At the retained generator index, exactly one orientation agrees with the
original letter. At a different index, projecting either constructor equality
would contradict the original index inequality, so both indicators vanish. -/
theorem two_orientations (needle : SignedWord.SignedGenerator count) (index : Fin count) :
    (if (⟨index, false⟩ : SignedWord.SignedGenerator count) = needle then 1 else 0 : Nat) +
      (if (⟨index, true⟩ : SignedWord.SignedGenerator count) = needle then 1 else 0 : Nat) =
      if needle.index = index then 1 else 0 := by
  cases needle with
  | mk position reversed =>
      by_cases same : position = index
      · cases same
        have opposite : SignedWord.SignedGenerator.mk index true ≠
            SignedWord.SignedGenerator.mk index false :=
          fun equal => Bool.noConfusion (congrArg SignedGenerator.reversed equal)
        cases reversed with
        | false =>
            rewrite [if_pos (Eq.refl (SignedWord.SignedGenerator.mk index false)),
              if_neg opposite, if_pos (Eq.refl index)]
            rfl
        | true =>
            rewrite [if_neg opposite.symm,
              if_pos (Eq.refl (SignedWord.SignedGenerator.mk index true)),
              if_pos (Eq.refl index)]
            rfl
      · have notPositive : SignedWord.SignedGenerator.mk index false ≠
            SignedWord.SignedGenerator.mk position reversed :=
          fun equal => same (congrArg SignedGenerator.index equal).symm
        have notNegative : SignedWord.SignedGenerator.mk index true ≠
            SignedWord.SignedGenerator.mk position reversed :=
          fun equal => same (congrArg SignedGenerator.index equal).symm
        rewrite [if_neg notPositive, if_neg notNegative, if_neg same]
        rfl

open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator
/-- A signed letter has zero coefficient away from its own generator. -/
theorem coefficient_zero_of_ne (letter : SignedWord.SignedGenerator count) (index : Fin count) (different : letter.index
  ≠ index) :
    letter.coefficients index = 0 := by
  rw [coefficients, Data.Vector.Basic.vectorOfFn_apply, if_neg (Ne.symm different)]

/-- A signed letter's coefficient at its own generator is one or negative one according to orientation. -/
theorem coefficient_self (index : Fin count) (reversed : Bool) :
    (⟨index, reversed⟩ : SignedWord.SignedGenerator count).coefficients index = if reversed then -1 else 1 := by
  rw [coefficients, Data.Vector.Basic.vectorOfFn_apply, if_pos rfl]

end SignedGenerator

set_option genInjectivity false in
/-- Two distinct original generators with the segments between their interlaced endpoints.

The four ordered segments retain the original occurrences in the cyclic word
between the positive and negative endpoints of the two selected generators.
The distinctness certificate belongs to those original bounded indices. -/
structure InterlacedWord (count : Nat) where
  /-- Original first generator of the interlaced handle. -/ first : Fin count
  /-- Original second generator of the interlaced handle. -/ last : Fin count
  /-- The two selected pivot indices are distinct. -/ distinct : first ≠ last
  /-- Original segment from the first positive endpoint to the second positive endpoint. -/ u : List
    (SignedWord.SignedGenerator count)
  /-- Original segment from the second positive endpoint to the first negative endpoint. -/ v : List
    (SignedWord.SignedGenerator count)
  /-- Original segment from the first negative endpoint to the second negative endpoint. -/ w : List
    (SignedWord.SignedGenerator count)
  /-- Original segment after the second negative endpoint in the displayed cyclic order. -/ x : List
    (SignedWord.SignedGenerator count)

constructive_injectivity InterlacedWord

namespace InterlacedWord

open Purelib.Data.Int

variable {count : Nat}

/-- Form the displayed word `p U q V (-p) W (-q) X` before handle removal.

The original first and last generator indices supply the four oriented
endpoints. Their retained segments occur in the supplied interlaced order
without selecting or recomputing any occurrence. -/
@[expose] def before (cut : Surgery.InterlacedWord count) : List (SignedWord.SignedGenerator count) :=
  ⟨cut.first, false⟩ :: (cut.u ++ (⟨cut.last, false⟩ :: (cut.v ++
    (⟨cut.first, true⟩ :: (cut.w ++ (⟨cut.last, true⟩ :: cut.x))))))

/-- The four original intervening segments in their original order. -/
@[expose] def tail (cut : Surgery.InterlacedWord count) : List (SignedWord.SignedGenerator count) := cut.u ++ cut.v ++
  cut.w ++ cut.x

/-- Reconnect the original intervening segments in the order `U X W V`.

The four retained segments are reused once in this displayed order. The
selected interlaced endpoint occurrences are absent from the resulting
finite signed word. -/
@[expose] def after (cut : Surgery.InterlacedWord count) : List (SignedWord.SignedGenerator count) := cut.u ++ cut.x ++
  cut.w ++ cut.v

section
open Purelib.Topology.Surface.Word.Surgery.InterlacedWord
/-- Reconnecting the four segments preserves every retained signed multiplicity. -/
theorem occurrences_after (cut : Surgery.InterlacedWord count) (needle : SignedWord.SignedGenerator count) :
    needle.occurrences cut.after = needle.occurrences cut.tail := by
  simp only [InterlacedWord.after, tail, Surgery.SignedGenerator.occurrences_append]
  omega

/-- The original word adds one occurrence of each pivot orientation to the retained segments. -/
theorem occurrences_before (cut : Surgery.InterlacedWord count) (needle : SignedWord.SignedGenerator count) :
    needle.occurrences cut.before = needle.occurrences cut.tail +
      (if needle.index = cut.first then 1 else 0) + (if needle.index = cut.last then 1 else 0) := by
  simp only [before, tail, Surgery.SignedGenerator.occurrences_append, SignedGenerator.occurrences]
  have first := Surgery.SignedGenerator.two_orientations needle cut.first
  have last := Surgery.SignedGenerator.two_orientations needle cut.last
  omega

/-- Handle removal deletes exactly four original endpoint occurrences.

The original four segment lengths occur once on each side of the equation.
The displayed before word retains the four pivot endpoints, while the
literal after word retains only the reconnected segments. -/
theorem after_length (cut : Surgery.InterlacedWord count) : cut.after.length + 4 = cut.before.length := by
  simp only [InterlacedWord.after, before, Append.length_append, List.length_cons]
  omega

end

/-- The shorter reconnected word inherits the signed uniqueness bound. -/
theorem after_counts_le (cut : Surgery.InterlacedWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (index : Fin count) (reversed : Bool) : SignedGenerator.occurrences ⟨index, reversed⟩ cut.after ≤ 1 := by
  rw [cut.occurrences_after]
  have before := cut.occurrences_before ⟨index, reversed⟩
  have bounded := counts index reversed
  omega

open Purelib.Topology.Surface.Word.Surgery.InterlacedWord in
/-- Surgery removes exactly the four pivot occurrences, and nothing else. -/
theorem after_occurrences_eq (cut : Surgery.InterlacedWord count) (active : Fin count → Bool)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before = if active index then 1 else
      0)
    (index : Fin count) (reversed : Bool) :
    SignedGenerator.occurrences ⟨index, reversed⟩ cut.after =
      if index = cut.first ∨ index = cut.last then 0 else if active index then 1 else 0 := by
  have before := cut.occurrences_before ⟨index, reversed⟩
  rw [counts] at before
  have cap : (if active index then 1 else 0 : Nat) ≤ 1 := by split <;> omega
  rw [cut.occurrences_after]
  dsimp only at before
  by_cases atFirst : index = cut.first
  · rw [if_pos (Or.inl atFirst)]
    rw [if_pos atFirst] at before
    omega
  · by_cases atLast : index = cut.last
    · rw [if_pos (Or.inr atLast)]
      rw [if_pos atLast] at before
      omega
    · rw [if_neg (fun either => either.elim atFirst atLast)]
      rw [if_neg atFirst, if_neg atLast] at before
      omega

/-- Original signed uniqueness excludes both pivot generators from the retained segments. -/
theorem tail_avoids (cut : Surgery.InterlacedWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (letter : SignedWord.SignedGenerator count) (member : letter ∈ cut.tail) : letter.index ≠ cut.first ∧ letter.index ≠
      cut.last := by
  have positive := Surgery.SignedGenerator.occurrences_positive letter cut.tail member
  have bounded := counts letter.index letter.reversed
  have same : (⟨letter.index, letter.reversed⟩ : SignedWord.SignedGenerator count) = letter := by cases letter; rfl
  rw [same, cut.occurrences_before] at bounded
  constructor
  · intro equal; rw [if_pos equal] at bounded; omega
  · intro equal; rw [if_pos equal] at bounded; omega

open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator Purelib.Topology.Surface.Word.Surgery.InterlacedWord in
/-- All four retained segments have zero coefficients at either pivot index.

Each mapped coefficient retains its original letter occurrence in one of the
four segments. The original signed uniqueness bound excludes the two pivot
indices from those same retained occurrences. -/
private theorem segments_clear (cut : Surgery.InterlacedWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (index : Fin count) (pivot : index = cut.first ∨ index = cut.last) :
    (∀ letter ∈ cut.u.map SignedGenerator.coefficients, letter index = 0) ∧
    (∀ letter ∈ cut.v.map SignedGenerator.coefficients, letter index = 0) ∧
    (∀ letter ∈ cut.w.map SignedGenerator.coefficients, letter index = 0) ∧
    (∀ letter ∈ cut.x.map SignedGenerator.coefficients, letter index = 0) := by
  have clear (coefficients : Pairing.Coefficients count)
      (member : coefficients ∈ cut.u.map SignedGenerator.coefficients ++ cut.v.map SignedGenerator.coefficients ++
        cut.w.map SignedGenerator.coefficients ++ cut.x.map SignedGenerator.coefficients) : coefficients index = 0 := by
    have actual : coefficients ∈ cut.tail.map SignedGenerator.coefficients := by
      simpa only [tail, Map.map_append] using member
    rcases Map.mem_map.mp actual with ⟨letter, member, equal⟩
    rw [← equal]
    apply Surgery.SignedGenerator.coefficient_zero_of_ne letter
    rcases pivot with first | last
    · rw [first]; exact (cut.tail_avoids counts letter member).1
    · rw [last]; exact (cut.tail_avoids counts letter member).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun letter member => clear letter (Membership.mem_append.mpr (Or.inl (Membership.mem_append.mpr
      (Or.inl (Membership.mem_append.mpr (Or.inl member))))))
  · exact fun letter member => clear letter (Membership.mem_append.mpr (Or.inl (Membership.mem_append.mpr
      (Or.inl (Membership.mem_append.mpr (Or.inr member))))))
  · exact fun letter member => clear letter (Membership.mem_append.mpr (Or.inl (Membership.mem_append.mpr (Or.inr
      member))))
  · exact fun letter member => clear letter (Membership.mem_append.mpr (Or.inr member))

open Purelib.Topology.Surface.Word.Surgery

section
open Purelib.Topology.Surface.Word.Surgery.InterlacedWord
/-- Away from both pivots, the original matrix equals the original segment matrix.

The supplied row and column inequalities make all four retained pivot
endpoint coefficients zero. The remaining terms belong to the same original
ordered four-segment tail. -/
theorem before_remaining (cut : Surgery.InterlacedWord count) (row column : Fin count)
    (rowFirst : row ≠ cut.first) (rowLast : row ≠ cut.last)
    (columnFirst : column ≠ cut.first) (columnLast : column ≠ cut.last) :
    Pairing.pairingAt (cut.before.map SignedGenerator.coefficients) row column =
      Pairing.pairingAt (cut.tail.map SignedGenerator.coefficients) row column := by
  have firstRow (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.first, reversed⟩ : SignedWord.SignedGenerator count) row (Ne.symm rowFirst)
  have firstColumn (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.first, reversed⟩ : SignedWord.SignedGenerator count) column (Ne.symm columnFirst)
  have lastRow (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.last, reversed⟩ : SignedWord.SignedGenerator count) row (Ne.symm rowLast)
  have lastColumn (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.last, reversed⟩ : SignedWord.SignedGenerator count) column (Ne.symm columnLast)
  simp only [before, tail, List.map_cons, Map.map_append, pairingAt_append, totalAt_append,
    Pairing.pairingAt, Pairing.totalAt, firstRow, firstColumn, lastRow, lastColumn, zero_mul, mul_zero, zero_add,
      Arithmetic.sub_zero]
  ring1

/-- The two interlaced generators have alternating area pairing equal to two.

Signed uniqueness excludes both pivot indices from the retained segments.
Their four original endpoint coefficients then supply the exact positive
area pairing in the displayed cyclic order. -/
theorem before_unit (cut : Surgery.InterlacedWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1) :
    Pairing.pairingAt (cut.before.map SignedGenerator.coefficients) cut.first cut.last = 2 := by
  obtain ⟨up, vp, wp, xp⟩ := cut.segments_clear counts cut.first (Or.inl rfl)
  obtain ⟨uq, vq, wq, xq⟩ := cut.segments_clear counts cut.last (Or.inr rfl)
  have firstOther (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.first, reversed⟩ : SignedWord.SignedGenerator count) cut.last cut.distinct
  have lastOther (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.last, reversed⟩ : SignedWord.SignedGenerator count) cut.first (Ne.symm cut.distinct)
  have positive : (⟨cut.first, false⟩ : SignedWord.SignedGenerator count).coefficients cut.first = 1 :=
    Surgery.SignedGenerator.coefficient_self cut.first false
  have negative : (⟨cut.first, true⟩ : SignedWord.SignedGenerator count).coefficients cut.first = -1 :=
    Surgery.SignedGenerator.coefficient_self cut.first true
  have lastPositive : (⟨cut.last, false⟩ : SignedWord.SignedGenerator count).coefficients cut.last = 1 :=
    Surgery.SignedGenerator.coefficient_self cut.last false
  have lastNegative : (⟨cut.last, true⟩ : SignedWord.SignedGenerator count).coefficients cut.last = -1 :=
    Surgery.SignedGenerator.coefficient_self cut.last true
  simp only [before, List.map_cons, Map.map_append, pairingAt_append, totalAt_append, Pairing.pairingAt,
    Pairing.totalAt,
    positive, negative, lastPositive, lastNegative, firstOther, lastOther,
    totalAt_zero_of _ _ up, totalAt_zero_of _ _ vp, totalAt_zero_of _ _ wp, totalAt_zero_of _ _ xp,
    totalAt_zero_of _ _ uq, totalAt_zero_of _ _ vq, totalAt_zero_of _ _ wq, totalAt_zero_of _ _ xq,
    pairingAt_zero_of _ _ _ up, pairingAt_zero_of _ _ _ vp, pairingAt_zero_of _ _ _ wp, pairingAt_zero_of _ _ _ xp]
  rfl

/-- The first pivot row is twice the total of original segments U and V.

The supplied signed uniqueness bound removes the first pivot from all four
segments. The surviving column differs from both pivots, so only the two
original first-pivot endpoints contribute to that row. -/
theorem before_first (cut : Surgery.InterlacedWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (column : Fin count) (columnFirst : column ≠ cut.first) (columnLast : column ≠ cut.last) :
    Pairing.pairingAt (cut.before.map SignedGenerator.coefficients) cut.first column =
      2 * (Pairing.totalAt (cut.u.map SignedGenerator.coefficients) column + Pairing.totalAt (cut.v.map
        SignedGenerator.coefficients) column) := by
  obtain ⟨up, vp, wp, xp⟩ := cut.segments_clear counts cut.first (Or.inl rfl)
  have lastOther (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.last, reversed⟩ : SignedWord.SignedGenerator count) cut.first (Ne.symm cut.distinct)
  have firstColumn (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.first, reversed⟩ : SignedWord.SignedGenerator count) column (Ne.symm columnFirst)
  have lastColumn (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.last, reversed⟩ : SignedWord.SignedGenerator count) column (Ne.symm columnLast)
  have positive : (⟨cut.first, false⟩ : SignedWord.SignedGenerator count).coefficients cut.first = 1 :=
    Surgery.SignedGenerator.coefficient_self cut.first false
  have negative : (⟨cut.first, true⟩ : SignedWord.SignedGenerator count).coefficients cut.first = -1 :=
    Surgery.SignedGenerator.coefficient_self cut.first true
  simp only [before, List.map_cons, Map.map_append, pairingAt_append, totalAt_append, Pairing.pairingAt,
    Pairing.totalAt,
    positive, negative, lastOther, firstColumn, lastColumn,
    totalAt_zero_of _ _ up, totalAt_zero_of _ _ vp, totalAt_zero_of _ _ wp, totalAt_zero_of _ _ xp,
    pairingAt_zero_of _ _ _ up, pairingAt_zero_of _ _ _ vp, pairingAt_zero_of _ _ _ wp, pairingAt_zero_of _ _ _ xp]
  simp only [zero_mul, mul_zero, add_zero, zero_add, Arithmetic.sub_zero, one_mul, neg_mul]
  ring1

/-- The last pivot row is twice the total of original segments V and W.

The supplied signed uniqueness bound removes the last pivot from all four
segments. The surviving column differs from both pivots, so only the two
original last-pivot endpoints contribute to that row. -/
theorem before_last (cut : Surgery.InterlacedWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (column : Fin count) (columnFirst : column ≠ cut.first) (columnLast : column ≠ cut.last) :
    Pairing.pairingAt (cut.before.map SignedGenerator.coefficients) cut.last column =
      2 * (Pairing.totalAt (cut.v.map SignedGenerator.coefficients) column + Pairing.totalAt (cut.w.map
        SignedGenerator.coefficients) column) := by
  obtain ⟨uq, vq, wq, xq⟩ := cut.segments_clear counts cut.last (Or.inr rfl)
  have firstOther (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.first, reversed⟩ : SignedWord.SignedGenerator count) cut.last cut.distinct
  have firstColumn (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.first, reversed⟩ : SignedWord.SignedGenerator count) column (Ne.symm columnFirst)
  have lastColumn (reversed : Bool) := Surgery.SignedGenerator.coefficient_zero_of_ne
    (⟨cut.last, reversed⟩ : SignedWord.SignedGenerator count) column (Ne.symm columnLast)
  have positive : (⟨cut.last, false⟩ : SignedWord.SignedGenerator count).coefficients cut.last = 1 :=
    Surgery.SignedGenerator.coefficient_self cut.last false
  have negative : (⟨cut.last, true⟩ : SignedWord.SignedGenerator count).coefficients cut.last = -1 :=
    Surgery.SignedGenerator.coefficient_self cut.last true
  simp only [before, List.map_cons, Map.map_append, pairingAt_append, totalAt_append, Pairing.pairingAt,
    Pairing.totalAt,
    positive, negative, firstOther, firstColumn, lastColumn,
    totalAt_zero_of _ _ uq, totalAt_zero_of _ _ vq, totalAt_zero_of _ _ wq, totalAt_zero_of _ _ xq,
    pairingAt_zero_of _ _ _ uq, pairingAt_zero_of _ _ _ vq, pairingAt_zero_of _ _ _ wq, pairingAt_zero_of _ _ _ xq]
  simp only [zero_mul, mul_zero, add_zero, zero_add, Arithmetic.sub_zero, one_mul, neg_mul]
  ring1

end

/-- Removing both endpoint pairs preserves the original total coefficients.

Each pivot's positive and negative indicators contribute the same natural
increment to the two occurrence counts. Their original integer difference
therefore agrees with the total of the retained segment tail. -/
theorem tail_total (cut : Surgery.InterlacedWord count) (index : Fin count) :
    Pairing.totalAt (cut.tail.map SignedGenerator.coefficients) index = Pairing.totalAt (cut.before.map
      SignedGenerator.coefficients) index := by
  rw [SignedGenerator.total_eq_counts, SignedGenerator.total_eq_counts, cut.occurrences_before, cut.occurrences_before]
  simp only [Int.natCast_add]
  ring1

/-- Handle surgery preserves the total coefficient vector. -/
theorem after_total (cut : Surgery.InterlacedWord count) (index : Fin count) :
    Pairing.totalAt (cut.after.map SignedGenerator.coefficients) index = Pairing.totalAt (cut.before.map
      SignedGenerator.coefficients) index := by
  rw [← cut.tail_total, SignedGenerator.total_eq_counts, SignedGenerator.total_eq_counts,
    cut.occurrences_after, cut.occurrences_after]

open Purelib.Topology.Surface.Word.Surgery.InterlacedWord in
/-- Reconnection subtracts the rank-two alternating term on surviving coordinates.

The retained row and column differ from both pivots. The supplied zero totals
belong to the original complete word, and its unchanged segment coefficients
supply the explicit correction for the literal reconnection. -/
theorem after_pairing (cut : Surgery.InterlacedWord count) (row column : Fin count)
    (rowFirst : row ≠ cut.first) (rowLast : row ≠ cut.last)
    (columnFirst : column ≠ cut.first) (columnLast : column ≠ cut.last)
    (closed : ∀ index, Pairing.totalAt (cut.before.map SignedGenerator.coefficients) index = 0) :
    Pairing.pairingAt (cut.after.map SignedGenerator.coefficients) row column =
      Pairing.pairingAt (cut.before.map SignedGenerator.coefficients) row column -
      2 * ((Pairing.totalAt (cut.u.map SignedGenerator.coefficients) row + Pairing.totalAt (cut.v.map
        SignedGenerator.coefficients) row) *
        (Pairing.totalAt (cut.v.map SignedGenerator.coefficients) column + Pairing.totalAt (cut.w.map
          SignedGenerator.coefficients) column) -
        (Pairing.totalAt (cut.v.map SignedGenerator.coefficients) row + Pairing.totalAt (cut.w.map
          SignedGenerator.coefficients) row) *
        (Pairing.totalAt (cut.u.map SignedGenerator.coefficients) column + Pairing.totalAt (cut.v.map
          SignedGenerator.coefficients) column)) := by
  have rowClosed := (cut.tail_total row).trans (closed row)
  have columnClosed := (cut.tail_total column).trans (closed column)
  rw [cut.before_remaining row column rowFirst rowLast columnFirst columnLast]
  simp only [tail, Map.map_append] at rowClosed columnClosed
  simp only [InterlacedWord.after, tail, Map.map_append]
  exact pairingAt_reconnect _ _ _ _ row column rowClosed columnClosed

end InterlacedWord

set_option genInjectivity false in
/-- Cached exact halving of an original signed-word signature.

The retained integer matrix has twice each entry equal to the original
signature entry. Its factor-two certificate concerns that same cached word
signature, preserving both matrix owners for subsequent comparison. -/
structure IntegralWordSignature {count : Nat} (word : List (SignedWord.SignedGenerator count)) where
  /-- Original cached signed-word total and alternating area matrix. -/ signature : Pairing.Signature (word.map
    SignedGenerator.coefficients)
  /-- Cached exact integer half of the alternating area matrix. -/ matrix : Pairing.IntegralMatrix count
  /-- Twice every retained integral entry equals the original cached area entry. -/ twice : ∀ row column, 2 * matrix row
    column = signature.matrix row column

constructive_injectivity IntegralWordSignature

namespace IntegralWordSignature

open Purelib.LinearAlgebra
open Purelib.Topology.Surface.Word.Pairing (totalAt pairingAt)

variable {count : Nat} {word : List (SignedWord.SignedGenerator count)}

/-- A balanced signed word's cached area entries divide exactly by two.

Diagonal entries vanish by the retained signature law. Every other entry is
twice its original ordered contribution because the supplied total is zero,
so the original integer quotient cancels the nonzero factor two. -/
theorem even (signature : Pairing.Signature (word.map SignedGenerator.coefficients))
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0) (row column : Fin count) :
    2 * (signature.matrix row column / 2) = signature.matrix row column := by
  by_cases same : row = column
  · cases same; rw [signature.diagonal]; rfl
  · rw [signature.matrix_eq, Word.pairing_eq_twice_ordered word same, closed row,
      Data.Int.Arithmetic.zero_mul, Data.Int.Arithmetic.sub_zero]
    rw [Data.Int.Division.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0)]

/-- Cache exact integral halves of an existing balanced word signature.

The original supplied signature is retained unchanged. Each finite matrix
entry is its integer quotient by two, and the supplied zero totals certify
that twice this same cached quotient recovers the original area entry. -/
@[expose] def build (signature : Pairing.Signature (word.map SignedGenerator.coefficients))
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0) :
      Surgery.IntegralWordSignature word :=
  { signature := signature
    matrix := LinearAlgebra.Matrix.matrixOfFn fun row column => signature.matrix row column /
      2
    twice := fun row column => by
      rw [LinearAlgebra.Matrix.matrixOfFn_apply]
      exact IntegralWordSignature.even signature closed row column }

/-- Twice the cached integral entry is the original word's computed alternating pairing. -/
theorem spec (integral : Surgery.IntegralWordSignature word) (row column : Fin count) :
    2 * integral.matrix row column = Pairing.pairingAt (word.map SignedGenerator.coefficients) row column :=
  (integral.twice row column).trans (integral.signature.matrix_eq row column)

/-- The retained integral word matrix is skew-symmetric. -/
theorem skew (integral : Surgery.IntegralWordSignature word) (row column : Fin count) :
    integral.matrix row column = -integral.matrix column row := by
  have first := integral.twice row column
  have last := integral.twice column row
  have skew := integral.signature.skew row column
  omega

/-- Every diagonal entry of the retained integral matrix is zero. -/
theorem diagonal (integral : Surgery.IntegralWordSignature word) (index : Fin count) : integral.matrix index index = 0
  := by
  have skew := integral.skew index index
  omega

end IntegralWordSignature

namespace InterlacedWord

open Purelib.Topology.Surface.Word.Pairing (totalAt pairingAt)

variable {count : Nat}

/-- Construct the positive unit pivot of the retained interlaced word matrix.

The original first and last generator indices become the pivot coordinates.
Their unit-entry certificate follows from the supplied signed multiplicity
bounds and the same retained matrix factor-two equation. -/
@[expose] def unitPivot (cut : Surgery.InterlacedWord count) (source : Surgery.IntegralWordSignature cut.before)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1) :
    LinearAlgebra.Alternating.UnitPivot source.matrix :=
  ⟨cut.first, cut.last, by have := source.spec cut.first cut.last; rw [cut.before_unit counts] at this; omega⟩

open Purelib.Data.Int in
/-- Literal word reconnection agrees with pivot reduction on all surviving coordinates.

The source and target retain integral halves of their original word signatures.
Their factor-two certificates and original segment totals identify the explicit
pivot correction, and scalar cancellation preserves those cached entries. -/
theorem reduced_remaining (cut : Surgery.InterlacedWord count)
    (source : Surgery.IntegralWordSignature cut.before)
    (target : Surgery.IntegralWordSignature cut.after)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (closed : ∀ index, Pairing.totalAt (cut.before.map SignedGenerator.coefficients) index = 0)
    (row column : Fin count) (rowFirst : row ≠ cut.first) (rowLast : row ≠ cut.last)
    (columnFirst : column ≠ cut.first) (columnLast : column ≠ cut.last) :
    (cut.unitPivot source counts).reduced row column = target.matrix row column := by
  have first (index : Fin count) (first : index ≠ cut.first) (last : index ≠ cut.last) :
      source.matrix cut.first index = Pairing.totalAt (cut.u.map SignedGenerator.coefficients) index +
        Pairing.totalAt (cut.v.map SignedGenerator.coefficients) index := by
    have twice := source.spec cut.first index
    rw [cut.before_first counts index first last] at twice
    exact Arithmetic.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) twice
  have last (index : Fin count) (first : index ≠ cut.first) (last : index ≠ cut.last) :
      source.matrix cut.last index = Pairing.totalAt (cut.v.map SignedGenerator.coefficients) index +
        Pairing.totalAt (cut.w.map SignedGenerator.coefficients) index := by
    have twice := source.spec cut.last index
    rw [cut.before_last counts index first last] at twice
    exact Arithmetic.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) twice
  have comparison := target.spec row column
  rw [cut.after_pairing row column rowFirst rowLast columnFirst columnLast closed, ← source.spec,
    ← first row rowFirst rowLast, ← first column columnFirst columnLast,
    ← last row rowFirst rowLast, ← last column columnFirst columnLast] at comparison
  rw [LinearAlgebra.Alternating.UnitPivot.reduced_remaining _ source.skew row column rowFirst rowLast columnFirst
    columnLast]
  change source.matrix row column + source.matrix row cut.last * source.matrix column cut.first -
    source.matrix row cut.first * source.matrix column cut.last = _
  rw [source.skew row cut.last, source.skew column cut.first,
    source.skew row cut.first, source.skew column cut.last]
  have scaled : 2 * (source.matrix row column + -source.matrix cut.last row * -source.matrix cut.first column -
      -source.matrix cut.first row * -source.matrix cut.last column) = 2 * target.matrix row column := by
    rw [comparison]
    ring1
  exact Arithmetic.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) scaled

open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator Purelib.Topology.Surface.Word.Surgery.InterlacedWord in
/-- The shorter word's integral matrix has zero rows at the removed pivots.

Each original reconnected occurrence belongs to the same retained four-segment
tail. Its zero pivot coefficient forces the corresponding computed area row
to vanish, and the cached factor-two certificate identifies the integral row. -/
theorem after_zero (cut : Surgery.InterlacedWord count) (target : Surgery.IntegralWordSignature cut.after)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (row column : Fin count) (pivot : row = cut.first ∨ row = cut.last) : target.matrix row column = 0 := by
  have zero : ∀ coefficients ∈ cut.after.map SignedGenerator.coefficients, coefficients row = 0 := by
    intro coefficients member
    rcases Map.mem_map.mp member with ⟨letter, member, equal⟩
    rw [← equal]
    apply Surgery.SignedGenerator.coefficient_zero_of_ne letter
    have inTail : letter ∈ cut.tail := by
      change letter ∈ cut.u ++ cut.x ++ cut.w ++ cut.v at member
      change letter ∈ cut.u ++ cut.v ++ cut.w ++ cut.x
      cases Membership.mem_append.mp member with
      | inr inV =>
          exact Membership.mem_append.mpr (Or.inl (Membership.mem_append.mpr
            (Or.inl (Membership.mem_append.mpr (Or.inr inV)))))
      | inl inUXW =>
          cases Membership.mem_append.mp inUXW with
          | inr inW =>
              exact Membership.mem_append.mpr (Or.inl (Membership.mem_append.mpr (Or.inr inW)))
          | inl inUX =>
              cases Membership.mem_append.mp inUX with
              | inl inU =>
                  exact Membership.mem_append.mpr (Or.inl (Membership.mem_append.mpr
                    (Or.inl (Membership.mem_append.mpr (Or.inl inU)))))
              | inr inX => exact Membership.mem_append.mpr (Or.inr inX)
    rcases pivot with first | last
    · rw [first]; exact (cut.tail_avoids counts letter inTail).1
    · rw [last]; exact (cut.tail_avoids counts letter inTail).2
  have twice := target.spec row column
  rw [pairingAt_zero_of _ _ _ zero] at twice
  omega

/-- The reduced matrix is one original unit handle plus the shorter word matrix.

The cached source and target matrices belong to the original word and its
literal reconnection. Pivot rows and columns give the displayed handle,
while all surviving coordinates retain the shorter word's integral pairing. -/
theorem reduced_eq_handle_add (cut : Surgery.InterlacedWord count) (source : Surgery.IntegralWordSignature cut.before)
    (target : Surgery.IntegralWordSignature cut.after)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (closed : ∀ index, Pairing.totalAt (cut.before.map SignedGenerator.coefficients) index = 0)
    (row column : Fin count) :
    (cut.unitPivot source counts).reduced row column =
      Handle.Basic.handleEntry [(cut.first, cut.last)] row column + target.matrix row column := by
  let pivot := cut.unitPivot source counts
  by_cases rowFirst : row = cut.first
  · subst row
    rw [cut.after_zero target counts cut.first column (Or.inl rfl), add_zero]
    change pivot.reduced pivot.first column = _
    rw [pivot.reduced_first source.skew]
    change (if column = cut.last then 1 else 0 : Int) =
      (if cut.first = cut.first ∧ column = cut.last then 1 else 0) -
        (if cut.first = cut.last ∧ column = cut.first then 1 else 0) + 0
    by_cases last : column = cut.last
    · rw [if_pos last, if_pos ⟨rfl, last⟩,
        if_neg (fun pair => cut.distinct pair.1)]
      rfl
    · rw [if_neg last, if_neg (fun pair => last pair.2),
        if_neg (fun pair => cut.distinct pair.1)]
      rfl
  · by_cases rowLast : row = cut.last
    · subst row
      rw [cut.after_zero target counts cut.last column (Or.inr rfl), add_zero]
      change pivot.reduced pivot.last column = _
      rw [pivot.reduced_last source.skew]
      change (if column = cut.first then -1 else 0 : Int) =
        (if cut.last = cut.first ∧ column = cut.last then 1 else 0) -
          (if cut.last = cut.last ∧ column = cut.first then 1 else 0) + 0
      by_cases first : column = cut.first
      · rw [if_pos first, if_neg (fun pair => cut.distinct pair.1.symm),
          if_pos ⟨rfl, first⟩]
        rfl
      · rw [if_neg first, if_neg (fun pair => cut.distinct pair.1.symm),
          if_neg (fun pair => first pair.2)]
        rfl
    · have handle : Handle.Basic.handleEntry [(cut.first, cut.last)] row column = 0 := by
        change (if row = cut.first ∧ column = cut.last then 1 else 0 : Int) -
          (if row = cut.last ∧ column = cut.first then 1 else 0) + 0 = 0
        rw [if_neg (fun pair => rowFirst pair.1), if_neg (fun pair => rowLast pair.1)]
        rfl
      rw [handle, zero_add]
      by_cases columnFirst : column = cut.first
      · subst column
        rw [target.skew, cut.after_zero target counts cut.first row (Or.inl rfl), neg_zero]
        change pivot.reduced row pivot.first = _
        rw [pivot.reduced_skew source.skew, pivot.reduced_first source.skew]
        change -(if row = cut.last then 1 else 0 : Int) = 0
        rw [if_neg rowLast, neg_zero]
      · by_cases columnLast : column = cut.last
        · subst column
          rw [target.skew, cut.after_zero target counts cut.last row (Or.inr rfl), neg_zero]
          change pivot.reduced row pivot.last = _
          rw [pivot.reduced_skew source.skew, pivot.reduced_last source.skew]
          change -(if row = cut.first then -1 else 0 : Int) = 0
          rw [if_neg rowFirst, neg_zero]
        · exact cut.reduced_remaining source target counts closed row column rowFirst rowLast columnFirst columnLast

end InterlacedWord

end Purelib.Topology.Surface.Word.Surgery
