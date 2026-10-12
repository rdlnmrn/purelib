module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic

import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.Selection
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Surgery
public import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Constructive cancellation of the zero-pairing residual word

For a balanced signed word with unique orientations, a zero pairing forces
each chord interval to be balanced. Its inside and outside use disjoint
generators and again have zero pairing. Recursion therefore returns a finite
tree of cancelling pairs, including actual cyclic splits at every node.
This supplies the terminal geometric data missing from matrix reduction.
-/

public section

namespace Purelib.Topology.Surface.Word.ZeroReduction

open Purelib
open Purelib.Data.List
open Purelib.LinearAlgebra.Alternating
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.NormalForm
open Purelib.Topology.Surface.Word.Selection
open Purelib.Topology.Surface.Word.SignedWord
open Purelib.Topology.Surface.Word.Surgery

open Purelib.Topology.Surface.Word.Selection (ChordWord WordRotation InterlacedAt)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.Pairing
open Purelib.Topology.Surface.Word.Surgery (IntegralWordSignature)
open Purelib.Topology.Surface.Word.NormalForm (WordSurgeryTrace)

variable {count : Nat}

namespace ChordWord

/-- The outside chord segment inherits the original signed occurrence bound. -/
theorem outside_counts_le (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (index : Fin count) (reversed : Bool) : SignedGenerator.occurrences ⟨index, reversed⟩ chord.outside ≤ 1 := by
  have bounded := counts index reversed
  rw [chord.occurrences, ChordWord.tail, SignedGenerator.occurrences_append] at bounded
  omega

/-- A chord interval in a unique zero-pairing word has zero total coefficients. -/
theorem inside_closed_of_zero (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (zero : ∀ row column, Pairing.pairingAt (chord.word.map SignedGenerator.coefficients) row column = 0)
    (column : Fin count) : Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) column = 0 := by
  by_cases same : column = chord.index
  · subst column
    apply Surgery.totalAt_zero_of
    intro values member
    rcases Map.mem_map.mp member with ⟨letter, inInside, equal⟩
    rw [← equal]
    exact SignedGenerator.coefficient_zero_of_ne letter chord.index
      (chord.tail_avoids counts letter (List.mem_append_left _ inInside))
  · have interval := chord.pairing_row counts column same
    rw [zero] at interval
    omega

/-- The outside segment is balanced when the original unique balanced chord word has zero pairing. -/
theorem outside_closed_of_zero (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (closed : ∀ column, Pairing.totalAt (chord.word.map SignedGenerator.coefficients) column = 0)
    (zero : ∀ row column, Pairing.pairingAt (chord.word.map SignedGenerator.coefficients) row column = 0)
    (column : Fin count) : Pairing.totalAt (chord.outside.map SignedGenerator.coefficients) column = 0 := by
  have total := (chord.tail_total column).trans (closed column)
  rw [ChordWord.tail, Map.map_append, Surgery.totalAt_append, ChordWord.inside_closed_of_zero chord counts zero,
    zero_add]
    at total
  exact total

/-- The negative occurrence's coefficient is the negative of its positive counterpart. -/
private theorem opposite_coefficient (index column : Fin count) :
    (SignedGenerator.mk index true).coefficients column = -(SignedGenerator.mk index false).coefficients column := by
  change Data.Vector.Basic.vectorOfFn (fun position => if position = index then (-1 : Int) else 0) column =
    -Data.Vector.Basic.vectorOfFn (fun position => if position = index then (1 : Int) else 0) column
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  by_cases same : column = index
  · rw [if_pos same, if_pos same]
  · rw [if_neg same, if_neg same, neg_zero]

/-- Balanced inside and outside segments split the original chord pairing into their two pairing matrices. -/
theorem pairing_split (chord : Selection.ChordWord count)
    (insideClosed : ∀ column, Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) column = 0)
    (outsideClosed : ∀ column, Pairing.totalAt (chord.outside.map SignedGenerator.coefficients) column = 0)
    (row column : Fin count) :
    Pairing.pairingAt (chord.word.map SignedGenerator.coefficients) row column =
      Pairing.pairingAt (chord.inside.map SignedGenerator.coefficients) row column +
        Pairing.pairingAt (chord.outside.map SignedGenerator.coefficients) row column := by
  simp only [ChordWord.word, List.map_cons, Map.map_append, Pairing.pairingAt, Pairing.totalAt,
    Surgery.pairingAt_append, Surgery.totalAt_append, insideClosed, outsideClosed, ChordWord.opposite_coefficient]
  ring1

/-- Inside balance and original signed uniqueness exclude every inside generator from the outside segment. -/
private theorem counts_disjoint (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (insideClosed : ∀ column, Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) column = 0)
    (row : Fin count) (present : 0 < SignedGenerator.occurrences ⟨row, false⟩ chord.inside)
    (reversed : Bool) : SignedGenerator.occurrences ⟨row, reversed⟩ chord.outside = 0 := by
  have total := insideClosed row
  rw [SignedGenerator.total_eq_counts] at total
  have bounded := counts row reversed
  rw [chord.occurrences, ChordWord.tail, SignedGenerator.occurrences_append] at bounded
  cases reversed <;> omega

/-- The inside segment inherits zero pairing from a unique balanced zero-pairing chord word. -/
theorem inside_pairing_zero (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (closed : ∀ column, Pairing.totalAt (chord.word.map SignedGenerator.coefficients) column = 0)
    (zero : ∀ row column, Pairing.pairingAt (chord.word.map SignedGenerator.coefficients) row column = 0)
    (row column : Fin count) : Pairing.pairingAt (chord.inside.map SignedGenerator.coefficients) row column = 0 := by
  have insideClosed := ChordWord.inside_closed_of_zero chord counts zero
  have outsideClosed := ChordWord.outside_closed_of_zero chord counts closed zero
  have split := ChordWord.pairing_split chord insideClosed outsideClosed row column
  rw [zero] at split
  by_cases absent : SignedGenerator.occurrences ⟨row, false⟩ chord.inside = 0
  · have total := insideClosed row
    rw [SignedGenerator.total_eq_counts, absent] at total
    have negative : SignedGenerator.occurrences ⟨row, true⟩ chord.inside = 0 := by omega
    apply Surgery.pairingAt_zero_of
    intro values member
    rcases Map.mem_map.mp member with ⟨letter, inInside, equal⟩
    rw [← equal]
    exact SignedGenerator.coefficient_zero_of_counts chord.inside row absent negative letter inInside
  · have outsideZero : Pairing.pairingAt (chord.outside.map SignedGenerator.coefficients) row column = 0 := by
      apply Surgery.pairingAt_zero_of
      intro values member
      rcases Map.mem_map.mp member with ⟨letter, inOutside, equal⟩
      rw [← equal]
      exact SignedGenerator.coefficient_zero_of_counts chord.outside row
        (ChordWord.counts_disjoint chord counts insideClosed row (by omega) false)
        (ChordWord.counts_disjoint chord counts insideClosed row (by omega) true) letter inOutside
    omega

/-- The outside segment inherits zero pairing from a unique balanced zero-pairing chord word. -/
theorem outside_pairing_zero (chord : Selection.ChordWord count)
    (counts : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (closed : ∀ column, Pairing.totalAt (chord.word.map SignedGenerator.coefficients) column = 0)
    (zero : ∀ row column, Pairing.pairingAt (chord.word.map SignedGenerator.coefficients) row column = 0)
    (row column : Fin count) : Pairing.pairingAt (chord.outside.map SignedGenerator.coefficients) row column = 0 := by
  have split := ChordWord.pairing_split chord (ChordWord.inside_closed_of_zero chord counts zero)
    (ChordWord.outside_closed_of_zero chord counts closed zero) row column
  rw [zero, ChordWord.inside_pairing_zero chord counts closed zero] at split
  omega

end ChordWord

set_option genInjectivity false in
/-- A retained finite cancellation tree. Rotation records only a cyclic change of start; each node removes one opposite
pair after reducing its inside, then reduces the outside. There is no zero-matrix assumption in this certificate's
constructors.

The tree retains the actual cyclic split at every cancelled opposite pair. Its inside and outside subtrees refer to the
original selected segments. -/
inductive WordCancellation : List (SignedWord.SignedGenerator count) → Type
  /-- The empty signed word has an empty cancellation tree. -/ | nil :
    Purelib.Topology.Surface.Word.ZeroReduction.WordCancellation []
  /-- Cancel one retained opposite pair after retaining cancellation trees for its actual inside and outside segments.
  -/
  | pair {word} (selected : Selection.ChordAt word index)
      (inside : Purelib.Topology.Surface.Word.ZeroReduction.WordCancellation selected.chord.inside)
      (outside : Purelib.Topology.Surface.Word.ZeroReduction.WordCancellation selected.chord.outside) :
        Purelib.Topology.Surface.Word.ZeroReduction.WordCancellation word

constructive_injectivity Purelib.Topology.Surface.Word.ZeroReduction.WordCancellation

namespace WordCancellation

/-- Count the actual opposite pairs retained in the cancellation tree. -/
@[expose] def pairs : {word : List (SignedWord.SignedGenerator count)} → ZeroReduction.WordCancellation word → Nat
  | _, .nil => 0
  | _, .pair _ inside outside => inside.pairs + outside.pairs + 1

/-- The original word has exactly two occurrences for each retained cancelling pair. -/
theorem length_eq {word : List (SignedWord.SignedGenerator count)} (reduction : ZeroReduction.WordCancellation word) :
    word.length = 2 * reduction.pairs := by
  induction reduction with
  | nil => rfl
  | pair selected inside outside insideEq outsideEq =>
      have rotated := WordRotation.length selected.rotation
      simp only [ChordWord.word, List.length_cons, Append.length_append] at rotated
      simp only [WordCancellation.pairs]
      omega

/-- A certified cancellation tree makes every original total coefficient zero. -/
theorem closed {word : List (SignedWord.SignedGenerator count)} (reduction : ZeroReduction.WordCancellation word) (index
  : Fin count) :
    Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0 := by
  induction reduction with
  | nil => rfl
  | pair selected inside outside insideClosed outsideClosed =>
      rw [← selected.rotation.total, ← selected.chord.tail_total, ChordWord.tail,
        Map.map_append, Surgery.totalAt_append, insideClosed, outsideClosed, zero_add]

/-- A certified cancellation tree makes every original alternating pairing entry zero. -/
theorem pairing_zero {word : List (SignedWord.SignedGenerator count)} (reduction : ZeroReduction.WordCancellation word)
  (row column : Fin count) :
    Pairing.pairingAt (word.map SignedGenerator.coefficients) row column = 0 := by
  induction reduction with
  | nil => rfl
  | pair selected inside outside insideZero outsideZero =>
      rw [← selected.rotation.pairing (ZeroReduction.WordCancellation.pair selected inside outside).closed,
        ZeroReduction.ChordWord.pairing_split selected.chord inside.closed outside.closed, insideZero, outsideZero,
          zero_add]

open Purelib.Topology.Surface.Word.ZeroReduction.WordCancellation in
/-- The zero block is not accepted on faith: construct all cancelling chord intervals, recursively, from its proved
exact entries. -/
@[expose] def ofZero (word : List (SignedWord.SignedGenerator count))
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0)
    (zero : ∀ row column, Pairing.pairingAt (word.map SignedGenerator.coefficients) row column = 0) :
    ZeroReduction.WordCancellation word :=
  match word with
  | [] => .nil
  | head :: remaining =>
      have positive : 0 < SignedGenerator.occurrences ⟨head.index, false⟩ (head :: remaining) := by
        have member := SignedGenerator.occurrences_positive head (head :: remaining) List.mem_cons_self
        have balanced := closed head.index
        rw [SignedGenerator.total_eq_counts] at balanced
        cases head with
        | mk index reversed => cases reversed <;> dsimp only at member balanced ⊢ <;> omega
      let selected := ChordAt.build (head :: remaining) head.index (closed head.index) positive
      have counts := selected.counts unique
      have balanced := fun index => (selected.rotation.total index).trans (closed index)
      have entries := fun row column => (selected.rotation.pairing closed row column).trans (zero row column)
      .pair selected
        (Purelib.Topology.Surface.Word.ZeroReduction.WordCancellation.ofZero selected.chord.inside
          (selected.chord.inside_counts_le counts)
          (Purelib.Topology.Surface.Word.ZeroReduction.ChordWord.inside_closed_of_zero selected.chord counts entries)
            (Purelib.Topology.Surface.Word.ZeroReduction.ChordWord.inside_pairing_zero selected.chord counts balanced
            entries))
        (Purelib.Topology.Surface.Word.ZeroReduction.WordCancellation.ofZero selected.chord.outside
          (Purelib.Topology.Surface.Word.ZeroReduction.ChordWord.outside_counts_le selected.chord counts)
          (Purelib.Topology.Surface.Word.ZeroReduction.ChordWord.outside_closed_of_zero selected.chord counts balanced
            entries) (Purelib.Topology.Surface.Word.ZeroReduction.ChordWord.outside_pairing_zero selected.chord counts
            balanced entries))
termination_by word.length
decreasing_by
  all_goals
    have rotated := WordRotation.length selected.rotation
    dsimp only [selected] at rotated
    simp only [ChordWord.word, List.length_cons, Append.length_append] at rotated ⊢
    omega

end WordCancellation

namespace WordSurgeryTrace

/-- The actual terminal residual inherits the original signed occurrence bounds. -/
theorem terminal_unique {word : List (SignedWord.SignedGenerator count)} {integral : Surgery.IntegralWordSignature word}
    {pivots : List (Handle.Basic.PivotIndices count)} (trace : NormalForm.WordSurgeryTrace word integral pivots)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1) :
    ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ trace.terminalWord ≤ 1 := by
  induction trace with
  | zero => exact unique
  | handle selected counts _ _ _ ih => exact ih (selected.cut.after_counts_le (selected.counts counts))

/-- The actual terminal residual inherits the original zero total coefficients. -/
theorem terminal_closed {word : List (SignedWord.SignedGenerator count)} {integral : Surgery.IntegralWordSignature word}
    {pivots : List (Handle.Basic.PivotIndices count)} (trace : NormalForm.WordSurgeryTrace word integral pivots)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0) :
    ∀ index, Pairing.totalAt (trace.terminalWord.map SignedGenerator.coefficients) index = 0 := by
  induction trace with
  | zero => exact closed
  | handle selected _ balanced _ _ ih =>
    exact ih (fun index => (selected.cut.after_total index).trans (selected.closed balanced index))

/-- Construct the terminal cancellation tree from the retained surgery trace's exact zero matrix.

Original signed uniqueness and balance supply the finite chord recursion's conditions without replacing the retained
residual word. -/
@[expose] def terminalCancellation {word : List (SignedWord.SignedGenerator count)} {integral :
  Surgery.IntegralWordSignature word}
    {pivots : List (Handle.Basic.PivotIndices count)} (trace : NormalForm.WordSurgeryTrace word integral pivots)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0) :
    ZeroReduction.WordCancellation trace.terminalWord :=
  .ofZero trace.terminalWord (WordSurgeryTrace.terminal_unique trace unique) (WordSurgeryTrace.terminal_closed trace
    closed) (fun row column => by
    rw [← trace.terminalIntegral.spec, trace.terminal_zero, mul_zero])

end WordSurgeryTrace

end Purelib.Topology.Surface.Word.ZeroReduction

end
