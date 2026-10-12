module
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Representation.Sequence
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic
public import Purelib.Approximation.Gaussian.Translation.Realizer
import Purelib.Approximation.Gaussian.Translation.Request
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation.Gaussian.Translation (Request)

open Purelib

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Representation

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Gaussian.Translation

open Purelib.Approximation.Gaussian.Translation.CCL

open Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Finite translations through a progressive CCL cursor

A finite CCL observation contains two synchronized interfaces to one named
program: a persistent raw prefix of an explicitly requested length and a
finite rational sample/error observation.  The prefix has exact projective
machine semantics; the sidecar supplies the rational precision gauge used for
cross-representation comparison.
-/

namespace Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Realizer

/-- Indices selected by the already-proved operational round trip for one finite request. Naming this computation keeps
the realizer and its coherence proof definitionally synchronized. -/
def approximationToCursorComparison
    (approximation : ApproximationData) (index : Nat)
    (request : Request) :=
  let cclApproximation :=
    CursorObservation.approximation approximation.toNamed
  let accurateStart := cclApproximation.refineIndex 0 request.targetSq
    request.positive
  let equivalent :=
    Equivalent.toNamed_sampling approximation
  equivalent.compare accurateStart index request.targetSq request.positive

/-- The canonical finite realizer from random-access fast-Cauchy observations to the productive CCL protocol. The
comparison indices come from the existing operational round-trip theorem. `bitCount = sampleIndex + 1` exposes the
sequential cost of retaining a raw prefix alongside a random-access query. -/
def approximationToCursor (approximation :
  ApproximationData) :
    Approximation.Gaussian.Translation.Realizer (Sequence.approximationRepresentation approximation)
      (Cursor.Basic.cursorRepresentation approximation.toNamed) where
  translate index request := by
    let cclApproximation :=
      CursorObservation.approximation approximation.toNamed
    let accurateStart := cclApproximation.refineIndex 0 request.targetSq
      request.positive
    let comparison :=
      approximationToCursorComparison approximation index request
    let output : Cursor.Basic.CursorObservation approximation.toNamed :=
      { sampleIndex := comparison.leftIndex
        bitCount := comparison.leftIndex + 1 }
    exact
      { source' := comparison.rightIndex
        output := output
        source_refines := comparison.right_ge
        relates := fun sourceValue targetValue =>
          Data.Gaussian.Norm.Basic.normSq
            (targetValue - sourceValue) < request.targetSq
        source_to_target := by
          rintro sourceValue ⟨sourceLater, sourceOrder, rfl⟩
          refine ⟨cclApproximation.sample comparison.leftIndex,
            cclApproximation.sample_possible comparison.leftIndex, ?_⟩
          exact comparison.close (Nat.le_refl _) sourceOrder
        target_to_source := by
          rintro targetValue ⟨targetLater, targetOrder, rfl⟩
          refine ⟨approximation.sample comparison.rightIndex,
            approximation.sample_possible comparison.rightIndex, ?_⟩
          exact comparison.close targetOrder (Nat.le_refl _)
        precisionLoss := 0
        precisionLoss_nonneg := le_rfl
        precision := by
          change cclApproximation.radiusSq comparison.leftIndex <
            request.targetSq + 0
          calc
            cclApproximation.radiusSq comparison.leftIndex ≤
                cclApproximation.radiusSq accurateStart := by
              change Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 4
                  comparison.leftIndex ≤
                Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 4 accurateStart
              exact quarterRadius_antitone
                (by decide) comparison.left_ge
            _ < request.targetSq :=
              cclApproximation.refineIndex_accurate 0 request.targetSq
                request.positive
            _ = request.targetSq + 0 := by ring1
        schedule :=
          { sourceRefinements := comparison.leftIndex + 1
            emittedUnits := comparison.leftIndex + 1
            arithmeticSteps := 2 }
        costBound := 2 * (comparison.leftIndex + 1) + 2
        cost_le := by
          change
            (comparison.leftIndex + 1) + (comparison.leftIndex + 1) + 2 ≤
              2 * (comparison.leftIndex + 1) + 2
          omega }

/-- Nat-indexed executable entry point for clients of the fast-Cauchy representation. -/
def approximationToCursorAt (approximation :
  ApproximationData)
    (index : Nat) (request : Request) :=
  (approximationToCursor approximation).translate index request

/-- The translated cursor retains one more raw bit than its sampled approximation index. -/
@[simp] theorem approximationToCursorAt_bitCount
    (approximation : ApproximationData) (index : Nat)
    (request : Request) :
    (approximationToCursorAt approximation index
      request).output.bitCount =
      (approximationToCursorAt approximation index
        request).output.sampleIndex +
        1 := rfl

/-- The finite translation cost bound is twice the retained bit count plus two. -/
@[simp] theorem approximationToCursorAt_costBound
    (approximation : ApproximationData) (index : Nat)
    (request : Request) :
    (approximationToCursorAt approximation index
      request).costBound =
      2 * ((approximationToCursorAt approximation index
        request).output.sampleIndex +
        1) + 2 := rfl

/-- The translated response retains its exact word length, synchronized sample and bit counts, and computed cost bound.
-/
theorem approximationToCursorAt_schedule
    (approximation : ApproximationData) (index : Nat)
    (request : Request) :
    let result := approximationToCursorAt approximation index
      request
    result.output.word.length = result.output.bitCount ∧
      result.output.bitCount = result.output.sampleIndex + 1 ∧
      result.costBound = 2 * (result.output.sampleIndex + 1) + 2 := by
  dsimp only
  exact ⟨CursorObservation.word_length _,
    approximationToCursorAt_bitCount approximation index request,
    approximationToCursorAt_costBound approximation index
      request⟩

/-- The translated cursor's squared precision allowance is strictly below the original positive request target. -/
theorem approximationToCursorAt_precision
    (approximation : ApproximationData) (index : Nat)
    (request : Request) :
    (Cursor.Basic.cursorRepresentation approximation.toNamed).precisionSq
        (approximationToCursorAt approximation index
          request).output <
      request.targetSq := by
  let result := approximationToCursorAt approximation index
    request
  calc
    (Cursor.Basic.cursorRepresentation approximation.toNamed).precisionSq result.output <
        request.targetSq + result.precisionLoss := result.precision
    _ = request.targetSq := by
      change request.targetSq + 0 = request.targetSq
      ring1

/-- The emitted raw word in every translated response has exactly the displayed sequential cost and exact machine
semantics. -/
theorem approximationToCursor_word_certificate
    (approximation : ApproximationData) (index : Nat)
    (request : Request) :
    let result := (approximationToCursor approximation).translate
      index request
    result.output.word.length = result.output.bitCount ∧
      Semantics.Basic.ExactCursor
        approximation.toNamed.process approximation.toNamed.state
        (Advance.advance approximation.toNamed.machine
          result.output.bitCount) := by
  dsimp only
  exact ⟨CursorObservation.word_length _, CursorObservation.exactCursor _⟩

/-- One headline finite-request certificate. It collects the quantitative sidecar precision, exact productive-machine
prefix semantics, and the measured schedule bound which are otherwise stored in separate projections of the translation
result. -/
theorem approximationToCursorAt_certified
    (approximation : ApproximationData) (index : Nat)
    (request : Request) :
    let result := approximationToCursorAt approximation index
      request
    result.output.word.length = result.output.bitCount ∧
      Semantics.Basic.ExactCursor
        approximation.toNamed.process approximation.toNamed.state
        (Advance.advance approximation.toNamed.machine
          result.output.bitCount) ∧
      (Cursor.Basic.cursorRepresentation approximation.toNamed).precisionSq result.output <
        request.targetSq ∧
      result.schedule.work ≤ result.costBound ∧
      result.costBound = 2 * (result.output.sampleIndex + 1) + 2 := by
  dsimp only
  exact ⟨CursorObservation.word_length _, CursorObservation.exactCursor _,
    approximationToCursorAt_precision approximation index
      request,
    (approximationToCursorAt approximation index
      request).cost_le,
    approximationToCursorAt_costBound approximation index
      request⟩

/-- Independent requests from the same approximation retain one persistent external protocol. Their output cursors are
ordered by refinement, and the raw word of the coarser cursor is literally a prefix of the finer word. -/
theorem approximationToCursorAt_persistent
    (approximation : ApproximationData)
    (leftIndex rightIndex : Nat) (leftRequest rightRequest : Request) :
    let left := approximationToCursorAt approximation leftIndex
      leftRequest
    let right := approximationToCursorAt approximation rightIndex
      rightRequest
    ((Cursor.Basic.cursorRepresentation approximation.toNamed).Refines
          right.output left.output ∧
        left.output.word.IsPrefix right.output.word) ∨
      ((Cursor.Basic.cursorRepresentation approximation.toNamed).Refines
          left.output right.output ∧
        right.output.word.IsPrefix left.output.word) := by
  dsimp only
  have leftSynchronized := approximationToCursorAt_bitCount
    approximation
    leftIndex leftRequest
  have rightSynchronized := approximationToCursorAt_bitCount
    approximation
    rightIndex rightRequest
  rcases Nat.le_total
      (approximationToCursorAt approximation leftIndex
        leftRequest).output.sampleIndex
      (approximationToCursorAt approximation rightIndex
        rightRequest).output.sampleIndex
      with leftBeforeRight | rightBeforeLeft
  · apply Or.inl
    have bitOrder :
        (approximationToCursorAt approximation leftIndex
          leftRequest).output.bitCount ≤
          (approximationToCursorAt approximation rightIndex
            rightRequest).output.bitCount := by
      rw [leftSynchronized, rightSynchronized]
      exact Nat.add_le_add_right leftBeforeRight 1
    exact ⟨⟨leftBeforeRight, bitOrder⟩,
      CursorObservation.word_isPrefix_of_bitCount_le bitOrder⟩
  · apply Or.inr
    have bitOrder :
        (approximationToCursorAt approximation rightIndex
          rightRequest).output.bitCount ≤
          (approximationToCursorAt approximation leftIndex
            leftRequest).output.bitCount := by
      rw [leftSynchronized, rightSynchronized]
      exact Nat.add_le_add_right rightBeforeLeft 1
    exact ⟨⟨rightBeforeLeft, bitOrder⟩,
      CursorObservation.word_isPrefix_of_bitCount_le bitOrder⟩
end Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Realizer

end
