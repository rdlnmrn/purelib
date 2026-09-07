import mathlib.Tactic.QuotientFreeOmega
import FiniteMeasure.MarkovReturn

/-!
# Exact finite absorption from a decreasing rank

An absorbing Boolean event and a displayed natural-valued rank give an exact
finite hitting theorem when every transition outside the event either enters
the event or strictly decreases the rank.  The proof follows atom-table
membership through finite binds.  It uses no limiting argument, infinite
path, compactness principle, or choice.
-/

namespace FiniteMeasure

namespace Distribution

/-- Every displayed atom of a finite distribution satisfies `property`. -/
def Supports {alpha : Type} (distribution : Distribution alpha)
    (property : alpha → Prop) : Prop :=
  ∀ atom, atom ∈ distribution.atoms → property atom.item

theorem Supports.pure {alpha : Type} {property : alpha → Prop}
    {item : alpha} (selected : property item) :
    (Distribution.pure item).Supports property := by
  intro atom member
  have atomIdentity := List.mem_singleton.mp member
  have itemIdentity := congrArg Weighted.item atomIdentity
  simpa only [itemIdentity] using selected

theorem Supports.bind {alpha beta : Type}
    {source : Distribution alpha} {transition : alpha → Distribution beta}
    {sourceProperty : alpha → Prop} {targetProperty : beta → Prop}
    (sourceSupport : source.Supports sourceProperty)
    (transitionSupport : ∀ item, sourceProperty item →
      (transition item).Supports targetProperty) :
    (source.bind transition).Supports targetProperty := by
  intro atom member
  rcases mem_bindAtoms_source_transition transition atom member with
      ⟨sourceAtom, sourceMember, targetAtom, targetMember, itemIdentity⟩
  have targetSelected := transitionSupport sourceAtom.item
    (sourceSupport sourceAtom sourceMember) targetAtom targetMember
  simpa only [itemIdentity] using targetSelected

private theorem eventWeight_eq_totalWeight_of_all {alpha : Type}
    (event : alpha → Bool) :
    ∀ atoms : List (Weighted alpha),
      (∀ atom, atom ∈ atoms → event atom.item = true) →
      eventWeight atoms event = totalWeight atoms
  | [], _ => rfl
  | atom :: remaining, selected => by
      simp only [eventWeight, selected atom List.mem_cons_self, totalWeight]
      rw [eventWeight_eq_totalWeight_of_all event remaining]
      intro target member
      exact selected target (List.mem_cons_of_mem atom member)

/-- A finite distribution supported entirely on an event gives that event
probability exactly one. -/
theorem probability_eq_one_of_supports {alpha : Type}
    (distribution : Distribution alpha) (event : alpha → Bool)
    (support : distribution.Supports fun item => event item = true) :
    distribution.probability event = 1 := by
  unfold Distribution.probability
  rw [eventWeight_eq_totalWeight_of_all event distribution.atoms support,
    distribution.total_one]

/-- Atomwise form of a ranked absorbing transition. -/
def RankedAbsorbing {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (rank : alpha → Nat) : Prop :=
  (∀ item, event item = true →
      (transition item).Supports fun next => event next = true) ∧
    (∀ item, event item = false →
      (transition item).Supports fun next =>
        event next = true ∨ rank next < rank item)

namespace RankedAbsorbing

/-- After `count` steps, support lies inside the absorbing event whenever
every starting atom was already inside or had rank below `count`. -/
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
          Bool.eq_false_of_not_eq_true sourceSelected
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

/-- Exact probability-one form of ranked finite absorption for an arbitrary
displayed initial law. -/
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

/-- Statewise specialization from one deterministic starting state. -/
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

/-- A uniform displayed strict rank bound produces a probability-one finite
block-hit certificate. -/
def blockHitCertificate {alpha : Type}
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

end FiniteMeasure
