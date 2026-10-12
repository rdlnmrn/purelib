module
public import Purelib.Measure.Distribution.Markov.Block
import Purelib.Measure.Distribution.Kernel.Iteration
public import Purelib.Measure.Distribution.Support

import Purelib.Data.Bool.Decide
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

section
/-!
# Exact finite absorption from a decreasing rank

An absorbing Boolean event and a displayed natural-valued rank give an exact
finite hitting theorem when every transition outside the event either enters
the event or strictly decreases the rank.  The proof follows atom-table
membership through finite binds.  It uses no limiting argument, infinite
path, compactness principle, or choice.
-/

public section

namespace Purelib.Measure

namespace Distribution

open Purelib.Data

/-- Require the exact transition kernel to preserve the event and strictly decrease a natural rank outside it unless it
enters the event.

Both clauses hold on every retained transition atom, using the original event and rank functions. -/
@[expose] def RankedAbsorbing {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (rank : alpha → Nat) : Prop :=
  (∀ item, event item = true →
      (transition item).Supports fun next => event next = true) ∧
    (∀ item, event item = false →
      (transition item).Supports fun next =>
        event next = true ∨ rank next < rank item)

namespace RankedAbsorbing

/-- A source supported on event states or ranks below the step count reaches event-only support after that exact count.
-/
theorem iterate_supports_event {alpha : Type}
    {transition : alpha → Distribution alpha} {event : alpha → Bool}
    {rank : alpha → Nat}
    (absorbing : RankedAbsorbing transition event rank) :
    ∀ (count : Nat) (source : Distribution alpha),
      source.Supports (fun item =>
        event item = true ∨ rank item < count) →
      (Distribution.iterate transition count source).Supports
        (fun item => event item = true)
  | 0, source, sourceSupport => by
      intro atom member
      rcases sourceSupport atom member with selected | impossible
      · exact selected
      · omega
  | count + 1, source, sourceSupport => by
      apply iterate_supports_event absorbing count (source.step transition)
      intro target targetMember
      rcases mem_bindAtoms_source_transition transition target targetMember with
          ⟨sourceAtom, sourceMember, transitionAtom, transitionMember,
            itemIdentity⟩
      by_cases sourceSelected : event sourceAtom.item = true
      · left
        have targetSelected := absorbing.1 sourceAtom.item sourceSelected
          transitionAtom transitionMember
        simpa only [itemIdentity] using targetSelected
      · have sourceNotSelected : event sourceAtom.item = false :=
          Bool.Decide.bool_eq_false_of_not_eq_true (event sourceAtom.item) sourceSelected
        have sourceRank : rank sourceAtom.item < count + 1 := by
          rcases sourceSupport sourceAtom sourceMember with
              impossible | rankBound
          · exact (sourceSelected impossible).elim
          · exact rankBound
        rcases absorbing.2 sourceAtom.item sourceNotSelected transitionAtom
            transitionMember with targetSelected | targetRank
        · left
          simpa only [itemIdentity] using targetSelected
        · right
          have targetRankBound : rank transitionAtom.item < count := by
            omega
          simpa only [itemIdentity] using targetRankBound

/-- The exact finite iterate has event probability one under the retained absorbing-rank and original-source support
certificates. -/
theorem iterate_probability_eq_one {alpha : Type}
    {transition : alpha → Distribution alpha} {event : alpha → Bool}
    {rank : alpha → Nat}
    (absorbing : RankedAbsorbing transition event rank)
    (count : Nat) (source : Distribution alpha)
    (sourceSupport : source.Supports fun item =>
      event item = true ∨ rank item < count) :
    (Distribution.iterate transition count source).probability event = 1 :=
  probability_eq_one_of_supports _ _
    (absorbing.iterate_supports_event count source sourceSupport)

/-- An original state already in the event or below the retained rank budget has event probability one after that many
steps. -/
theorem iterate_pure_probability_eq_one {alpha : Type}
    {transition : alpha → Distribution alpha} {event : alpha → Bool}
    {rank : alpha → Nat}
    (absorbing : RankedAbsorbing transition event rank)
    (count : Nat) (item : alpha)
    (bounded : event item = true ∨ rank item < count) :
    (Distribution.iterate transition count
      (Distribution.pure item)).probability event = 1 :=
  absorbing.iterate_probability_eq_one count (Distribution.pure item)
    (Supports.pure bounded)

/-- Construct a unit-rate endpoint hit certificate from an original uniform rank bound and positive block length.

Every starting state is absorbed within that exact block length, so the retained endpoint lower bound is one. -/
@[expose] def blockHitCertificate {alpha : Type}
    {transition : alpha → Distribution alpha} {event : alpha → Bool}
    {rank : alpha → Nat}
    (absorbing : RankedAbsorbing transition event rank)
    (blockLength : Nat) (blockLengthPositive : 0 < blockLength)
    (rankBound : ∀ item, rank item < blockLength) :
    UniformBlockHitCertificate transition event := by
  refine
    { blockLength := blockLength
      blockLengthPositive := blockLengthPositive
      rate := 1
      ratePositive := by decide
      rateAtMostOne := le_rfl
      endpointHitLower := ?_ }
  intro item
  unfold blockTransition
  rw [absorbing.iterate_pure_probability_eq_one blockLength item
    (Or.inr (rankBound item))]

end RankedAbsorbing

end Distribution

end Purelib.Measure

end
