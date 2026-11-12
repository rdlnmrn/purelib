module

public import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

/-!
# Preparation from original progressive approximation samples

An original sample-stage lower bound supplies candidate apartness at the
same stage of the actual shifted numerical process. The existing preparation
bridge refines that original process and retains its operational comparison.
-/

public section

namespace Purelib.Approximation.Gaussian.Sequence.ApproximationData

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

/-- Retain the original sample stage in the original process for approximation minus an exact point.

The exact summand keeps its original unit state. The manual source stage
retains candidate provenance and the initial canonical retry index; it is not
reported as an automatic retry transition.
-/
@[expose] def differenceState (approximation : ApproximationData) (point : Canonical) (index : Nat) :
    Name.Coherent.Refinement.State
      (CoherentNamed.add (CoherentNamed.ofApproximation approximation) (CoherentNamed.Coherence.exact (-point))) where
  source := (index, ())
  nextIndex := 0
  persists := by
    rintro value ⟨left, right, leftPossible, rightPossible, same⟩
    exact ⟨left, right, approximation.possible_persists (Nat.zero_le index) leftPossible, rightPossible, same⟩

/-- Original later-sample bounds certify candidate apartness throughout the retained shifted-process future. -/
@[expose] def differenceEvidence (approximation : ApproximationData) (point : Canonical) (index : Nat)
    (lowerSq : Rational) (positive : 0 < lowerSq)
    (samples : ∀ later, index ≤ later → lowerSq ≤ Norm.Basic.normSq
      (approximation.sample later - point)) :
    Process.Apart.Possible.PossibleApart
      (Process.Based.based
        (CoherentNamed.add (CoherentNamed.ofApproximation approximation)
          (CoherentNamed.Coherence.exact (-point))).name.process
        (approximation.differenceState point index).source) where
  lowerSq := lowerSq
  positive := positive
  lower := by
    intro state value possible
    have original := state.persists possible
    change ∃ left right : Canonical,
      approximation.Possible index left ∧ right = -point ∧ value = left + right at original
    rcases original with ⟨left, right, leftPossible, rightEq, rfl⟩
    rcases leftPossible with ⟨later, laterGe, leftEq⟩
    rewrite [rightEq, leftEq, ← Basic.sub_eq_add_neg]
    exact samples later laterGe

/-- Prepare the unchanged shifted numerical channel from a positive bound on its original later samples. -/
@[expose] def prepareDifference (approximation : ApproximationData) (point : Canonical) (index : Nat)
    (lowerSq : Rational) (positive : 0 < lowerSq)
    (samples : ∀ later, index ≤ later → lowerSq ≤ Norm.Basic.normSq
      (approximation.sample later - point)) :
    Division.Prepared
      (CoherentNamed.add (CoherentNamed.ofApproximation approximation) (CoherentNamed.Coherence.exact (-point))) :=
  Division.Prepared.ofEvidence (approximation.differenceState point index)
    (approximation.differenceEvidence point index lowerSq positive samples)

/-- Retain each original sample stage in the actual process for the difference of two approximations.

The ordered pair of source stages preserves both original sample histories.
Candidate persistence retains their actual witnesses, while the canonical retry
index starts at zero for this manually selected original process state.
-/
@[expose] def subtractionState (first second : ApproximationData) (firstIndex secondIndex : Nat) :
    Name.Coherent.Refinement.State
      (CoherentNamed.add (CoherentNamed.ofApproximation first)
        (CoherentNamed.neg (CoherentNamed.ofApproximation second))) where
  source := (firstIndex, secondIndex)
  nextIndex := 0
  persists := by
    rintro value ⟨left, right, leftPossible, ⟨source, sourcePossible, rightEq⟩, same⟩
    exact ⟨left, right, first.possible_persists (Nat.zero_le firstIndex) leftPossible,
      ⟨source, second.possible_persists (Nat.zero_le secondIndex) sourcePossible, rightEq⟩, same⟩

/-- A positive bound on all later original sample pairs certifies apartness of their retained difference process. -/
@[expose] def subtractionEvidence (first second : ApproximationData) (firstIndex secondIndex : Nat)
    (lowerSq : Rational) (positive : 0 < lowerSq)
    (samples : ∀ firstLater secondLater, firstIndex ≤ firstLater → secondIndex ≤ secondLater →
      lowerSq ≤ Norm.Basic.normSq (first.sample firstLater - second.sample secondLater)) :
    Process.Apart.Possible.PossibleApart
      (Process.Based.based
        (CoherentNamed.add (CoherentNamed.ofApproximation first)
          (CoherentNamed.neg (CoherentNamed.ofApproximation second))).name.process
        (first.subtractionState second firstIndex secondIndex).source) where
  lowerSq := lowerSq
  positive := positive
  lower := by
    intro state value possible
    have original := state.persists possible
    change ∃ left right : Canonical,
      first.Possible firstIndex left ∧ (∃ source, second.Possible secondIndex source ∧ right = -source) ∧
        value = left + right at original
    rcases original with ⟨left, right, leftPossible, ⟨source, sourcePossible, rightEq⟩, rfl⟩
    rcases leftPossible with ⟨firstLater, firstOrder, leftEq⟩
    rcases sourcePossible with ⟨secondLater, secondOrder, sourceEq⟩
    rewrite [rightEq, leftEq, sourceEq, ← Basic.sub_eq_add_neg]
    exact samples firstLater secondLater firstOrder secondOrder

/-- Prepare the unchanged ordered difference channel from a positive bound on its original later sample pairs. -/
@[expose] def prepareSubtraction (first second : ApproximationData) (firstIndex secondIndex : Nat)
    (lowerSq : Rational) (positive : 0 < lowerSq)
    (samples : ∀ firstLater secondLater, firstIndex ≤ firstLater → secondIndex ≤ secondLater →
      lowerSq ≤ Norm.Basic.normSq (first.sample firstLater - second.sample secondLater)) :
    Division.Prepared
      (CoherentNamed.add (CoherentNamed.ofApproximation first)
        (CoherentNamed.neg (CoherentNamed.ofApproximation second))) :=
  Division.Prepared.ofEvidence (first.subtractionState second firstIndex secondIndex)
    (first.subtractionEvidence second firstIndex secondIndex lowerSq positive samples)

end Purelib.Approximation.Gaussian.Sequence.ApproximationData

end
