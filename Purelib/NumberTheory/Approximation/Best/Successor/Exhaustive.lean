module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Best.Search

import Purelib.Data.List.Membership
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.Basic

section
public section

/-!
# Exhaustive consecutive best levels

The original bounded candidate list is filtered by its executable consecutive-level predicate. Retained pairs carry
their original best-test and intermediate-level exclusion evidence.
-/

namespace Purelib.NumberTheory.Approximation.Best.Successor.Exhaustive

open Purelib.Data
open Purelib.NumberTheory.Approximation

/-- The finite implication checked for one possible intermediate pair. -/
@[expose] def CandidateNotIntermediate (source : GaussianInt.Fraction) (lower upper middle :
  GaussianInt.Pair.Basic.ConvergentPair) :
    Prop :=
  Best.Search.PassesBestTest source middle →
    ¬ (Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance middle ∧
      Best.Error.denominatorQuadrance middle < Best.Error.denominatorQuadrance upper)

/-- Decide the finite best-test implication excluding an intermediate denominator level. -/
instance candidateNotIntermediateDecidable
    (source : GaussianInt.Fraction) (lower upper middle : GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (Best.Successor.Exhaustive.CandidateNotIntermediate source lower upper middle) := by
  unfold Best.Successor.Exhaustive.CandidateNotIntermediate
  infer_instance

/-- Structural finite conjunction asserting that no candidate in a supplied
list is a best pair at an intermediate denominator level. -/
@[expose] def EveryCandidateNotIntermediate
    (source : GaussianInt.Fraction) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) : List
      GaussianInt.Pair.Basic.ConvergentPair → Prop
  | [] => True
  | middle :: remaining =>
      Best.Successor.Exhaustive.CandidateNotIntermediate source lower upper middle ∧
        Purelib.NumberTheory.Approximation.Best.Successor.Exhaustive.EveryCandidateNotIntermediate source lower upper
          remaining

/-- Decide the structural conjunction of intermediate-level exclusions along a finite list. -/
instance everyCandidateNotIntermediateDecidable
    (source : GaussianInt.Fraction) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) (list : List
      GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (Best.Successor.Exhaustive.EveryCandidateNotIntermediate source lower upper list) := by
  induction list with
  | nil =>
      change Decidable True
      infer_instance
  | cons middle remaining inductionHypothesis =>
      letI : Decidable
          (Best.Successor.Exhaustive.EveryCandidateNotIntermediate source lower upper remaining) :=
        inductionHypothesis
      change Decidable
        (Best.Successor.Exhaustive.CandidateNotIntermediate source lower upper middle ∧
          Best.Successor.Exhaustive.EveryCandidateNotIntermediate source lower upper remaining)
      infer_instance

/-- Extract the intermediate-level exclusion for a member of the certified list. -/
theorem EveryCandidateNotIntermediate.of_mem
    {source : GaussianInt.Fraction} {lower upper middle : GaussianInt.Pair.Basic.ConvergentPair} {list : List
      GaussianInt.Pair.Basic.ConvergentPair}
    (every : Best.Successor.Exhaustive.EveryCandidateNotIntermediate source lower upper list)
    (member : middle ∈ list) :
    Best.Successor.Exhaustive.CandidateNotIntermediate source lower upper middle := by
  induction list with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      change Best.Successor.Exhaustive.CandidateNotIntermediate source lower upper head ∧
        Best.Successor.Exhaustive.EveryCandidateNotIntermediate source lower upper remaining at every
      rcases List.Membership.mem_cons.mp member with equal | tailMember
      · subst middle
        exact every.1
      · exact inductionHypothesis every.2 tailMember

/-- Assemble the structural list certificate from an exclusion proof for each member. -/
theorem everyCandidateNotIntermediate_of_forall
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair} {list : List
      GaussianInt.Pair.Basic.ConvergentPair}
    (noneBetween : ∀ middle ∈ list,
      Best.Successor.Exhaustive.CandidateNotIntermediate source lower upper middle) :
    Best.Successor.Exhaustive.EveryCandidateNotIntermediate source lower upper list := by
  induction list with
  | nil => trivial
  | cons middle remaining inductionHypothesis =>
      exact ⟨noneBetween middle List.mem_cons_self,
        inductionHypothesis (fun candidate member =>
          noneBetween candidate (List.mem_cons_of_mem _ member))⟩

/-- Executable certificate that two supplied pairs occupy consecutive best
denominator levels. -/
@[expose] def PassesConsecutiveTest (source : GaussianInt.Fraction) (lower upper :
  GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  Best.Search.PassesBestTest source lower ∧ Best.Search.PassesBestTest source upper ∧
    Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance upper ∧
    Best.Successor.Exhaustive.EveryCandidateNotIntermediate source lower upper (Best.Search.candidates source)

/-- Decide both best tests, denominator ordering and all finite intermediate-level exclusions. -/
instance passesConsecutiveTestDecidable
    (source : GaussianInt.Fraction) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (Best.Successor.Exhaustive.PassesConsecutiveTest source lower upper) := by
  unfold Best.Successor.Exhaustive.PassesConsecutiveTest
  infer_instance

/-- Exactness of the bounded consecutive-level test. -/
theorem passesConsecutiveTest_iff
    (source : GaussianInt.Fraction) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) :
    Best.Successor.Exhaustive.PassesConsecutiveTest source lower upper ↔
      Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper := by
  constructor
  · intro passes
    refine ⟨(Best.Search.passesBestTest_iff_isBest source lower).mp passes.1,
      (Best.Search.passesBestTest_iff_isBest source upper).mp passes.2.1,
      passes.2.2.1, ?_⟩
    intro middle middleBest between
    have middleMember := (Best.Search.IsBest.mem_candidates middleBest)
    have checked := Best.Successor.Exhaustive.EveryCandidateNotIntermediate.of_mem passes.2.2.2
      middleMember
    exact checked ((Best.Search.passesBestTest_iff_isBest source middle).mpr middleBest)
      between
  · intro consecutive
    refine ⟨(Best.Search.passesBestTest_iff_isBest source lower).mpr consecutive.1,
      (Best.Search.passesBestTest_iff_isBest source upper).mpr consecutive.2.1,
      consecutive.2.2.1, ?_⟩
    apply Best.Successor.Exhaustive.everyCandidateNotIntermediate_of_forall
    intro middle _ middlePasses between
    exact consecutive.2.2.2 middle
      ((Best.Search.passesBestTest_iff_isBest source middle).mp middlePasses) between

/-- Retain all candidates occupying the next best denominator level above a
supplied lower pair. -/
@[expose] def retainConsecutiveSuccessors (source : GaussianInt.Fraction) (lower :
  GaussianInt.Pair.Basic.ConvergentPair) :
    List GaussianInt.Pair.Basic.ConvergentPair → List GaussianInt.Pair.Basic.ConvergentPair
  | [] => []
  | candidate :: remaining =>
      if Best.Successor.Exhaustive.PassesConsecutiveTest source lower candidate then
        candidate :: Purelib.NumberTheory.Approximation.Best.Successor.Exhaustive.retainConsecutiveSuccessors source
          lower remaining
      else
        Purelib.NumberTheory.Approximation.Best.Successor.Exhaustive.retainConsecutiveSuccessors source lower remaining

/-- The successor filter retains exactly list members passing the consecutive-level test. -/
theorem mem_retainConsecutiveSuccessors_iff
    (source : GaussianInt.Fraction) (lower candidate : GaussianInt.Pair.Basic.ConvergentPair) (list : List
      GaussianInt.Pair.Basic.ConvergentPair) :
    candidate ∈ Best.Successor.Exhaustive.retainConsecutiveSuccessors source lower list ↔
      candidate ∈ list ∧ Best.Successor.Exhaustive.PassesConsecutiveTest source lower candidate := by
  induction list with
  | nil =>
      constructor
      · intro impossible; nomatch impossible
      · intro impossible; nomatch impossible.1
  | cons head remaining inductionHypothesis =>
      by_cases headPasses : Best.Successor.Exhaustive.PassesConsecutiveTest source lower head
      · rw [Best.Successor.Exhaustive.retainConsecutiveSuccessors, if_pos headPasses]
        constructor
        · intro member
          rcases List.Membership.mem_cons.mp member with equal | tail
          · subst candidate
            exact ⟨List.Mem.head _, headPasses⟩
          · have selected := inductionHypothesis.mp tail
            exact ⟨List.Mem.tail _ selected.1, selected.2⟩
        · intro member
          rcases List.Membership.mem_cons.mp member.1 with equal | tailMember
          · exact List.Membership.mem_cons.mpr (Or.inl equal)
          · exact List.Mem.tail _ (inductionHypothesis.mpr ⟨tailMember, member.2⟩)
      · rw [Best.Successor.Exhaustive.retainConsecutiveSuccessors, if_neg headPasses]
        constructor
        · intro member
          have selected := inductionHypothesis.mp member
          exact ⟨List.Mem.tail _ selected.1, selected.2⟩
        · intro member
          rcases List.Membership.mem_cons.mp member.1 with equal | tailMember
          · subst candidate
            exact (headPasses member.2).elim
          · exact inductionHypothesis.mpr ⟨tailMember, member.2⟩

/-- Complete finite list of the pairs at the consecutive best denominator
level above `lower`.  The list is empty exactly when no such level exists. -/
@[expose] def consecutiveSuccessors (source : GaussianInt.Fraction) (lower : GaussianInt.Pair.Basic.ConvergentPair) :
  List GaussianInt.Pair.Basic.ConvergentPair :=
  Best.Successor.Exhaustive.retainConsecutiveSuccessors source lower (Best.Search.candidates source)

/-- Soundness and completeness of the finite consecutive-minimal-vector
successor list. -/
theorem mem_consecutiveSuccessors_iff
    (source : GaussianInt.Fraction) (lower candidate : GaussianInt.Pair.Basic.ConvergentPair) :
    candidate ∈ Best.Successor.Exhaustive.consecutiveSuccessors source lower ↔
      Best.Consecutive.Basic.AreConsecutiveBest source.value lower candidate := by
  constructor
  · intro member
    have selected := (Best.Successor.Exhaustive.mem_retainConsecutiveSuccessors_iff source lower candidate
      (Best.Search.candidates source)).mp member
    exact (Best.Successor.Exhaustive.passesConsecutiveTest_iff source lower candidate).mp selected.2
  · intro consecutive
    exact (Best.Successor.Exhaustive.mem_retainConsecutiveSuccessors_iff source lower candidate
      (Best.Search.candidates source)).mpr ⟨Best.Search.IsBest.mem_candidates consecutive.2.1,
      (Best.Successor.Exhaustive.passesConsecutiveTest_iff source lower candidate).mpr consecutive⟩

/-- Filtering consecutive successors cannot increase the supplied candidate-list length. -/
theorem retainConsecutiveSuccessors_length_le
    (source : GaussianInt.Fraction) (lower : GaussianInt.Pair.Basic.ConvergentPair) (list : List
      GaussianInt.Pair.Basic.ConvergentPair) :
    (Best.Successor.Exhaustive.retainConsecutiveSuccessors source lower list).length ≤ list.length := by
  induction list with
  | nil => rfl
  | cons candidate remaining inductionHypothesis =>
      rw [Best.Successor.Exhaustive.retainConsecutiveSuccessors]
      by_cases passes : Best.Successor.Exhaustive.PassesConsecutiveTest source lower candidate
      · rw [if_pos passes, List.length_cons, List.length_cons]
        exact Nat.succ_le_succ inductionHypothesis
      · rw [if_neg passes, List.length_cons]
        exact inductionHypothesis.trans (Nat.le_succ _)

/-- The consecutive successor list inherits the explicit all-best candidate
bound. -/
theorem consecutiveSuccessors_length_le (source : GaussianInt.Fraction) (lower : GaussianInt.Pair.Basic.ConvergentPair)
  :
    (Best.Successor.Exhaustive.consecutiveSuccessors source lower).length ≤
      16 * (GaussianInt.normNat source.denominator + 1) ^ 2 *
        (Best.Search.numeratorQuadranceBound source + 1) ^ 2 := by
  exact
    (Best.Successor.Exhaustive.retainConsecutiveSuccessors_length_le source lower (Best.Search.candidates
      source)).trans_eq
      (Best.Search.candidates_length source)

end Purelib.NumberTheory.Approximation.Best.Successor.Exhaustive

end
