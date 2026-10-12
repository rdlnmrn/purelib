module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Surgery
public import Purelib.Topology.Surface.Word.PairedWord
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Int.Arithmetic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Exact number of paired letters in the actual cut word

The reordered alphabet retains its original one-sided mask. Summing the
proved signed multiplicities therefore counts two occurrences per stored
cut pair, with no physical boundary letter or unused generator added.
-/

namespace Purelib.Topology.Surface.Word.PairedWordCount

open Purelib
open Purelib.Algebra
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.PairedWord
open Purelib.Topology.Surface.Word.Surgery

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ sumFin_add sumFin_congr sumFin_ite_eq)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutAlphabet CutBoundaryWord)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)

namespace SignedGenerator

open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator (occurrences)

variable {count : Nat}

open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator
/-- Prepending a signed letter increases its generator's combined orientation count by one. -/
private theorem paired_occurrences_cons (head : SignedWord.SignedGenerator count) (tail : List
  (SignedWord.SignedGenerator count)) (index : Fin count) :
    occurrences ⟨index, false⟩ (head :: tail) + occurrences ⟨index, true⟩ (head :: tail) =
      (if index = head.index then 1 else 0) + (occurrences ⟨index, false⟩ tail + occurrences ⟨index, true⟩ tail) := by
  rw [occurrences, occurrences]
  cases head with
  | mk position reversed =>
      by_cases same : index = position
      · cases same
        have opposite : SignedWord.SignedGenerator.mk index true ≠
            SignedWord.SignedGenerator.mk index false :=
          fun equal => Bool.noConfusion (congrArg SignedWord.SignedGenerator.reversed equal)
        cases reversed with
        | false =>
            rw [if_pos (Eq.refl (SignedWord.SignedGenerator.mk index false)),
              if_neg opposite.symm, if_pos (Eq.refl index)]
            omega
        | true =>
            rw [if_neg opposite, if_pos (Eq.refl (SignedWord.SignedGenerator.mk index true)),
              if_pos (Eq.refl index)]
            omega
      · have notPositive : SignedWord.SignedGenerator.mk position reversed ≠
            SignedWord.SignedGenerator.mk index false :=
          fun equal => same (congrArg SignedWord.SignedGenerator.index equal).symm
        have notNegative : SignedWord.SignedGenerator.mk position reversed ≠
            SignedWord.SignedGenerator.mk index true :=
          fun equal => same (congrArg SignedWord.SignedGenerator.index equal).symm
        rw [if_neg notPositive, if_neg notNegative, if_neg same]
        omega

/-- Word length equals the finite sum of both signed multiplicities at every original generator.

Structural induction retains every head and tail occurrence. The finite sum of the head's single occupied slot adds one
to the original tail count. -/
theorem length_eq_occurrences (word : List (SignedWord.SignedGenerator count)) :
    (word.length : Int) = FiniteSum.Fin.sumFin (fun index => (occurrences ⟨index, false⟩ word : Int) + (occurrences
      ⟨index, true⟩ word : Int)) := by
  induction word with
  | nil => exact FiniteSum.Fin.sumFin_zero.symm
  | cons head tail ih =>
      have step (index : Fin count) :
          (occurrences ⟨index, false⟩ (head :: tail) : Int) + (occurrences ⟨index, true⟩ (head :: tail) : Int) =
          (if index = head.index then (1 : Int) else 0) +
            ((occurrences ⟨index, false⟩ tail : Int) + (occurrences ⟨index, true⟩ tail : Int)) := by
        have equation := congrArg (fun value : Nat => (value : Int)) (SignedGenerator.paired_occurrences_cons head tail
          index)
        simp only [Int.natCast_add] at equation
        by_cases same : index = head.index
        · simpa only [if_pos same, Nat.cast_one] using equation
        · simpa only [if_neg same, Nat.cast_zero] using equation
      calc
        _ = 1 + (tail.length : Int) := by rw [List.length_cons, Int.natCast_add, Nat.cast_one]; omega
        _ = FiniteSum.Fin.sumFin (fun index => if index = head.index then (1 : Int) else 0) +
            FiniteSum.Fin.sumFin (fun index => (occurrences ⟨index, false⟩ tail : Int) + (occurrences ⟨index, true⟩ tail
              : Int)) := by
          rw [FiniteSum.Fin.sumFin_ite_eq head.index (fun _ => (1 : Int)), ← ih]
        _ = FiniteSum.Fin.sumFin (fun index => (if index = head.index then (1 : Int) else 0) +
            ((occurrences ⟨index, false⟩ tail : Int) + (occurrences ⟨index, true⟩ tail : Int))) :=
              (FiniteSum.Fin.sumFin_add _ _).symm
        _ = _ := FiniteSum.Fin.sumFin_congr (fun index => (step index).symm)

end SignedGenerator

namespace CutAlphabet

/-- Integer count of the original alphabet's two-sided generator slots. -/
@[expose] def pairedCount {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge
  source)}
    (alphabet : BoundaryWord.CutAlphabet labels edges) : Int :=
  FiniteSum.Fin.sumFin fun index => if alphabet.oneSided index then 0 else 1

/-- An alphabet built from physical edges and retained pairs has exactly the displayed number of paired slots.

Each physical edge retains its one-sided mask and contributes zero. Each original retained pair contributes one to the
same finite paired-slot sum. -/
theorem ofLists_pairedCount {source target : Nat} {labels : Fin source → Fin target} :
    ∀ (boundary : List (Stokes.OrientedEdge source)) (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)),
      CutAlphabet.pairedCount (CutAlphabet.ofLists boundary pairs) = (pairs.length : Int) := by
  intro boundary
  induction boundary with
  | nil =>
      intro pairs
      induction pairs with
      | nil => rfl
      | cons pair pairs ih =>
          change FiniteSum.Fin.sumFin (fun index : Fin ((CutAlphabet.ofLists [] pairs).count + 1) =>
            if (Data.Vector.cons false (CutAlphabet.ofLists [] pairs).oneSided) index then (0 : Int) else
              1) = _
          rw [FiniteSum.Fin.sumFin_succ, List.length_cons, Int.natCast_add, Nat.cast_one]
          change 1 + CutAlphabet.pairedCount (CutAlphabet.ofLists [] pairs) = (pairs.length : Int) + 1
          rw [ih, add_comm]
  | cons edge boundary ih =>
      intro pairs
      change FiniteSum.Fin.sumFin (fun index : Fin ((CutAlphabet.ofLists boundary pairs).count + 1) =>
        if (Data.Vector.cons true (CutAlphabet.ofLists boundary pairs).oneSided) index then (0 : Int) else
          1) = _
      rw [FiniteSum.Fin.sumFin_succ]
      change 0 + CutAlphabet.pairedCount (CutAlphabet.ofLists boundary pairs) = (pairs.length : Int)
      rw [ih, zero_add]

end CutAlphabet

/-- The actual paired subword contains exactly two occurrences per paired alphabet slot.

Both signed multiplicities come from the original paired-letter equations. Their finite sum doubles the unchanged
paired-slot count without adding physical boundary letters. -/
theorem CutBoundaryWord.pairedLetters_length {source target : Nat} {labels : Fin source → Fin target}
    {edges : List (Stokes.OrientedEdge source)} (word : BoundaryWord.CutBoundaryWord labels edges) :
    (CutBoundaryWord.pairedLetters word).length = 2 * (PairedWordCount.CutAlphabet.pairedCount word.alphabet) := by
  rw [PairedWordCount.SignedGenerator.length_eq_occurrences]
  calc
    _ = FiniteSum.Fin.sumFin (fun index => (if word.alphabet.oneSided index then (0 : Int) else 1) +
        (if word.alphabet.oneSided index then (0 : Int) else 1)) := by
      apply FiniteSum.Fin.sumFin_congr
      intro index
      rw [CutBoundaryWord.pairedLetters_occurrences word index false, CutBoundaryWord.pairedLetters_occurrences word
        index true]
      cases word.alphabet.oneSided index <;> rfl
    _ = _ := by
      rw [FiniteSum.Fin.sumFin_add]
      change (PairedWordCount.CutAlphabet.pairedCount word.alphabet) + (PairedWordCount.CutAlphabet.pairedCount
        word.alphabet) = 2 * (PairedWordCount.CutAlphabet.pairedCount word.alphabet)
      omega

/-- The paired subword has exactly twice as many letters as retained original edge pairs. -/
theorem ProjectedEdgePairing.pairedLetters_length {source target : Nat} {labels : Fin source → Fin target}
    {edges : List (Stokes.OrientedEdge source)} (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges) :
    (CutBoundaryWord.pairedLetters (ProjectedEdgePairing.boundaryWord pairing)).length = 2 * pairing.pairs.length := by
  have count := PairedWordCount.CutBoundaryWord.pairedLetters_length (ProjectedEdgePairing.boundaryWord pairing)
  change ((CutBoundaryWord.pairedLetters (ProjectedEdgePairing.boundaryWord pairing)).length : Int) = 2 *
    (PairedWordCount.CutAlphabet.pairedCount (CutAlphabet.ofLists pairing.boundary pairing.pairs)) at count
  rw [PairedWordCount.CutAlphabet.ofLists_pairedCount] at count
  omega

end Purelib.Topology.Surface.Word.PairedWordCount

end
