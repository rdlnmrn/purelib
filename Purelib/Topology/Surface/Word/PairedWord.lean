module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.List.Filter
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
public import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.Selection
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Surgery
public import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# The paired subword of the actual cut boundary

Deleting the one-sided physical-boundary letters restricts the alternating
matrix to exactly its paired block. The original remaining matrix is not
discarded: this construction supplies a normal form only for that block.
-/

namespace Purelib.Topology.Surface.Word.PairedWord

open Purelib
open Purelib.Data.List
open Purelib.LinearAlgebra.Alternating
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.Selection
open Purelib.Topology.Surface.Word.SignedWord
open Purelib.Topology.Surface.Word.Surgery

open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator (occurrences coefficients total_eq_counts)
open Purelib.Topology.Surface.Word.Pairing
open Purelib.Topology.Surface.Word.Surgery (IntegralWordSignature)
open Purelib.Topology.Surface.Word.NormalForm (WordNormalForm normalizeWord)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

variable {count : Nat}

namespace SignedGenerator

/-- Keep signed word occurrences whose original generator index satisfies a fixed Boolean mask.

The mask is evaluated on each original generator index. Accepted signed occurrences keep their original order and
multiplicity. -/
@[expose] def retain (keep : Fin count → Bool) (word : List (SignedWord.SignedGenerator count)) : List
  (SignedWord.SignedGenerator count) :=
  word.filter fun letter => keep letter.index

/-- A retained signed letter keeps its original multiplicity, while a removed letter has multiplicity zero.

The fixed Boolean mask depends only on the original generator index. The two orientations retain their original counts
when accepted and contribute zero when rejected. -/
theorem occurrences_retain (keep : Fin count → Bool) (needle : SignedWord.SignedGenerator count)
    (word : List (SignedWord.SignedGenerator count)) :
    needle.occurrences (retain keep word) = if keep needle.index then needle.occurrences word else 0 :=
      by
  induction word with
  | nil => cases keep needle.index <;> rfl
  | cons head remaining ih =>
      cases chosen : keep head.index
      · rw [retain, Filter.filter_cons, chosen]
        change needle.occurrences (retain keep remaining) = _
        rw [ih, SignedGenerator.occurrences]
        by_cases same : head = needle
        · cases same; rw [chosen]; rfl
        · rw [if_neg same, zero_add]
      · rw [retain, Filter.filter_cons, chosen]
        change needle.occurrences (head :: retain keep remaining) = _
        rw [SignedGenerator.occurrences, ih, SignedGenerator.occurrences]
        by_cases same : head = needle
        · cases same; rw [chosen]; rfl
        · rw [if_neg same, zero_add, zero_add]

/-- Masking a signed word restricts its total coefficient vector by the same mask. -/
theorem total_retain (keep : Fin count → Bool) (word : List (SignedWord.SignedGenerator count)) (index : Fin count) :
    Pairing.totalAt ((retain keep word).map SignedGenerator.coefficients) index =
      if keep index then Pairing.totalAt (word.map SignedGenerator.coefficients) index else 0 := by
  rw [SignedGenerator.total_eq_counts, SignedGenerator.total_eq_counts, occurrences_retain,
    occurrences_retain]
  cases keep index <;> rfl

/-- Pairing entries between two retained coordinates are unchanged by filtering.

Both supplied coordinate certificates select retained entries. Structural recursion keeps the original coefficient
products and the pairing of the unchanged tail. -/
theorem pairing_retain_kept (keep : Fin count → Bool) (word : List (SignedWord.SignedGenerator count)) (row column : Fin
  count)
    (first : keep row = true) (last : keep column = true) :
    Pairing.pairingAt ((retain keep word).map SignedGenerator.coefficients) row column =
      Pairing.pairingAt (word.map SignedGenerator.coefficients) row column := by
  induction word with
  | nil => rfl
  | cons head remaining ih =>
      cases chosen : keep head.index
      · have rowZero := SignedGenerator.coefficient_zero_of_ne head row (by
          intro same; rw [same, first] at chosen;
          cases chosen)
        have columnZero := SignedGenerator.coefficient_zero_of_ne head column (by
          intro same; rw [same, last] at chosen;
          cases chosen)
        rw [retain, Filter.filter_cons, chosen]
        change Pairing.pairingAt ((retain keep remaining).map SignedGenerator.coefficients) row column =
          _
        rw [ih, List.map_cons, Pairing.pairingAt, rowZero, columnZero, zero_mul, mul_zero,
          Purelib.Data.Int.Arithmetic.sub_zero, zero_add]
      · rw [retain, Filter.filter_cons, chosen]
        change Pairing.pairingAt ((head :: retain keep remaining).map SignedGenerator.coefficients) row
          column = _
        rw [List.map_cons, List.map_cons, Pairing.pairingAt, Pairing.pairingAt, ih,
          total_retain, total_retain, first, last]
        rw [if_pos (Eq.refl true), if_pos (Eq.refl true)]

/-- A removed coordinate has a zero row in the filtered word's pairing matrix. -/
theorem pairing_retain_zero (keep : Fin count → Bool) (word : List (SignedWord.SignedGenerator count)) (row column : Fin
  count)
    (absent : keep row = false) : Pairing.pairingAt ((retain keep word).map
      SignedGenerator.coefficients) row column = 0 := by
  have zero (reversed : Bool) : SignedGenerator.occurrences ⟨row, reversed⟩ (retain keep word) = 0 := by
    rw [occurrences_retain, absent]
    rfl
  apply Surgery.pairingAt_zero_of
  intro values member
  rcases Map.mem_map.mp member with ⟨letter, member, equal⟩
  rw [← equal]
  exact SignedGenerator.coefficient_zero_of_counts _ row (zero false) (zero true) letter member

/-- Filtering is an exact coordinate restriction of the area matrix, even when the original word is unbalanced. -/
theorem pairing_retain (keep : Fin count → Bool) (word : List (SignedWord.SignedGenerator count)) (row column : Fin
  count) :
    Pairing.pairingAt ((retain keep word).map SignedGenerator.coefficients) row column =
      if keep row && keep column then Pairing.pairingAt (word.map SignedGenerator.coefficients) row column else 0 := by
  cases first : keep row
  · rw [Bool.false_and]
    exact pairing_retain_zero keep word row column first
  · cases last : keep column
    · rw [Pairing.pairingAt_skew, pairing_retain_zero keep word column row last]
      rfl
    · exact pairing_retain_kept keep word row column first last

end SignedGenerator

namespace CutBoundaryWord

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

/-- The original cut word with one-sided physical boundary letters removed. -/
@[expose] def pairedLetters (word : BoundaryWord.CutBoundaryWord labels edges) : List (SignedWord.SignedGenerator
  word.alphabet.count) :=
  PairedWord.SignedGenerator.retain (fun index => !word.alphabet.oneSided index) word.letters

/-- Each orientation of a paired generator occurs once; physical generators are absent. -/
theorem pairedLetters_occurrences (word : BoundaryWord.CutBoundaryWord labels edges) (index : Fin word.alphabet.count)
  (reversed : Bool) :
    SignedGenerator.occurrences ⟨index, reversed⟩ (pairedLetters word) = if word.alphabet.oneSided index
      then 0 else 1 := by
  rw [pairedLetters, PairedWord.SignedGenerator.occurrences_retain, CutBoundaryWord.occurrences_eq word]
  cases word.alphabet.oneSided index <;> cases reversed <;> rfl

/-- Each signed generator occurs at most once in the paired subword. -/
theorem pairedLetters_unique (word : BoundaryWord.CutBoundaryWord labels edges) (index : Fin word.alphabet.count)
  (reversed : Bool) :
    SignedGenerator.occurrences ⟨index, reversed⟩ (pairedLetters word) ≤ 1 := by
  rw [pairedLetters_occurrences word]
  split <;> omega

/-- The paired subword has zero total coefficient at every original generator. -/
theorem pairedLetters_closed (word : BoundaryWord.CutBoundaryWord labels edges) (index : Fin word.alphabet.count) :
    Pairing.totalAt ((pairedLetters word).map SignedGenerator.coefficients) index = 0 := by
  rw [SignedGenerator.total_eq_counts, pairedLetters_occurrences word,
    pairedLetters_occurrences word, sub_self]

namespace IntegralPairing

variable {word : BoundaryWord.CutBoundaryWord labels edges}

/-- The retained paired integral matrix is half the actual paired subword's alternating area matrix. -/
theorem paired_word_twice (pairing : IntegralPairing word) (row column : Fin word.alphabet.count) :
    2 * pairing.paired row column = Pairing.pairingAt ((pairedLetters word).map
      SignedGenerator.coefficients) row column := by
  rw [pairedLetters, PairedWord.SignedGenerator.pairing_retain]
  cases first : word.alphabet.oneSided row <;> cases last : word.alphabet.oneSided column
  · change 2 * pairing.paired row column = Pairing.pairingAt (word.letters.map SignedGenerator.coefficients) row column
    rw [pairing.paired_twice row column first last, word.signature.matrix_eq, word.coefficients_eq]
  all_goals rw [pairing.paired_eq, first, last]; rfl

/-- Reuse the existing paired matrix exactly.

No word-matrix calculation is rerun to initialize the automatic normal-form algorithm. -/
@[expose] def wordSignature (pairing : IntegralPairing word) : Surgery.IntegralWordSignature
  (pairedLetters word) where
  signature :=
    { total := Data.Vector.Basic.vectorOfFn fun _ => 0
      total_eq := fun index => (Data.Vector.Basic.vectorOfFn_apply _ index).trans ((pairedLetters_closed
        word) index).symm
      matrix := LinearAlgebra.Matrix.matrixOfFn fun row column => 2 * pairing.paired row
        column
      matrix_eq := fun row column => (LinearAlgebra.Matrix.matrixOfFn_apply _ row
        column).trans
        (paired_word_twice pairing row column) }
  matrix := pairing.paired
  twice := fun row column => (LinearAlgebra.Matrix.matrixOfFn_apply
    (fun i j => 2 * pairing.paired i j) row column).symm

/-- Automatic normal form of this actual cut boundary's paired integral block, including the original filtered
occurrence word and literal surgeries. -/
@[expose] def wordNormalForm (pairing : IntegralPairing word) : NormalForm.WordNormalForm
  (pairedLetters word) (wordSignature pairing) :=
  NormalForm.normalizeWord (pairedLetters word) (wordSignature pairing)
    (pairedLetters_unique word) (pairedLetters_closed word)

/-- No physical-boundary generator can become a handle coordinate. -/
theorem normalForm_paired (pairing : IntegralPairing word)
    (normal : NormalForm.WordNormalForm (pairedLetters word) (wordSignature pairing))
      (index : Fin word.alphabet.count)
    (member : index ∈ Handle.Basic.handleIndices normal.pivots) : word.alphabet.oneSided index = false := by
  have positive := normal.used index member
  rw [pairedLetters_occurrences word] at positive
  cases sided : word.alphabet.oneSided index
  · rfl
  · rw [sided, if_pos rfl] at positive
    omega

end IntegralPairing

end CutBoundaryWord

end Purelib.Topology.Surface.Word.PairedWord

end
