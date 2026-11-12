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
  Search.PassesBestTest source middle →
    ¬ (Error.denominatorQuadrance lower < Error.denominatorQuadrance middle ∧
      Error.denominatorQuadrance middle < Error.denominatorQuadrance upper)

/-- Decide the finite best-test implication excluding an intermediate denominator level. -/
instance candidateNotIntermediateDecidable
    (source : GaussianInt.Fraction) (lower upper middle : GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (CandidateNotIntermediate source lower upper middle) := by
  unfold CandidateNotIntermediate
  infer_instance

/-- Structural finite conjunction asserting that no candidate in a supplied
list is a best pair at an intermediate denominator level. -/
@[expose] def EveryCandidateNotIntermediate
    (source : GaussianInt.Fraction) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) : List
      GaussianInt.Pair.Basic.ConvergentPair → Prop
  | [] => True
  | middle :: remaining =>
      CandidateNotIntermediate source lower upper middle ∧
        Exhaustive.EveryCandidateNotIntermediate source lower upper
          remaining

/-- Decide the structural conjunction of intermediate-level exclusions along a finite list. -/
instance everyCandidateNotIntermediateDecidable
    (source : GaussianInt.Fraction) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) (list : List
      GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (EveryCandidateNotIntermediate source lower upper list) := by
  induction list with
  | nil =>
      change Decidable True
      infer_instance
  | cons middle remaining inductionHypothesis =>
      letI : Decidable
          (EveryCandidateNotIntermediate source lower upper remaining) :=
        inductionHypothesis
      change Decidable
        (CandidateNotIntermediate source lower upper middle ∧
          EveryCandidateNotIntermediate source lower upper remaining)
      infer_instance

/-- Extract the intermediate-level exclusion for a member of the certified list. -/
theorem EveryCandidateNotIntermediate.of_mem
    {source : GaussianInt.Fraction} {lower upper middle : GaussianInt.Pair.Basic.ConvergentPair} {list : List
      GaussianInt.Pair.Basic.ConvergentPair}
    (every : EveryCandidateNotIntermediate source lower upper list)
    (member : middle ∈ list) :
    CandidateNotIntermediate source lower upper middle := by
  induction list with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      change CandidateNotIntermediate source lower upper head ∧
        EveryCandidateNotIntermediate source lower upper remaining at every
      rcases List.Membership.mem_cons.mp member with equal | tailMember
      · subst middle
        exact every.1
      · exact inductionHypothesis every.2 tailMember

/-- Assemble the structural list certificate from an exclusion proof for each member. -/
theorem everyCandidateNotIntermediate_of_forall
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair} {list : List
      GaussianInt.Pair.Basic.ConvergentPair}
    (noneBetween : ∀ middle ∈ list,
      CandidateNotIntermediate source lower upper middle) :
    EveryCandidateNotIntermediate source lower upper list := by
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
  Search.PassesBestTest source lower ∧ Search.PassesBestTest source upper ∧
    Error.denominatorQuadrance lower < Error.denominatorQuadrance upper ∧
    EveryCandidateNotIntermediate source lower upper (Search.candidates source)

/-- Decide both best tests, denominator ordering and all finite intermediate-level exclusions. -/
instance passesConsecutiveTestDecidable
    (source : GaussianInt.Fraction) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (PassesConsecutiveTest source lower upper) := by
  unfold PassesConsecutiveTest
  infer_instance

/-- Exactness of the bounded consecutive-level test. -/
theorem passesConsecutiveTest_iff
    (source : GaussianInt.Fraction) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) :
    PassesConsecutiveTest source lower upper ↔
      Consecutive.Basic.AreConsecutiveBest source.value lower upper := by
  constructor
  · intro passes
    refine ⟨(Search.passesBestTest_iff_isBest source lower).mp passes.1,
      (Search.passesBestTest_iff_isBest source upper).mp passes.2.1,
      passes.2.2.1, ?_⟩
    intro middle middleBest between
    have middleMember := (Search.IsBest.mem_candidates middleBest)
    have checked := EveryCandidateNotIntermediate.of_mem passes.2.2.2
      middleMember
    exact checked ((Search.passesBestTest_iff_isBest source middle).mpr middleBest)
      between
  · intro consecutive
    refine ⟨(Search.passesBestTest_iff_isBest source lower).mpr consecutive.1,
      (Search.passesBestTest_iff_isBest source upper).mpr consecutive.2.1,
      consecutive.2.2.1, ?_⟩
    apply everyCandidateNotIntermediate_of_forall
    intro middle _ middlePasses between
    exact consecutive.2.2.2 middle
      ((Search.passesBestTest_iff_isBest source middle).mp middlePasses) between

/-- Retain all candidates occupying the next best denominator level above a
supplied lower pair. -/
@[expose] def retainConsecutiveSuccessors (source : GaussianInt.Fraction) (lower :
  GaussianInt.Pair.Basic.ConvergentPair) :
    List GaussianInt.Pair.Basic.ConvergentPair → List GaussianInt.Pair.Basic.ConvergentPair
  | [] => []
  | candidate :: remaining =>
      if PassesConsecutiveTest source lower candidate then
        candidate :: Exhaustive.retainConsecutiveSuccessors source
          lower remaining
      else
        Exhaustive.retainConsecutiveSuccessors source lower remaining

/-- The successor filter retains exactly list members passing the consecutive-level test. -/
theorem mem_retainConsecutiveSuccessors_iff
    (source : GaussianInt.Fraction) (lower candidate : GaussianInt.Pair.Basic.ConvergentPair) (list : List
      GaussianInt.Pair.Basic.ConvergentPair) :
    candidate ∈ retainConsecutiveSuccessors source lower list ↔
      candidate ∈ list ∧ PassesConsecutiveTest source lower candidate := by
  induction list with
  | nil =>
      constructor
      · intro impossible; nomatch impossible
      · intro impossible; nomatch impossible.1
  | cons head remaining inductionHypothesis =>
      by_cases headPasses : PassesConsecutiveTest source lower head
      · rw [retainConsecutiveSuccessors, if_pos headPasses]
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
      · rw [retainConsecutiveSuccessors, if_neg headPasses]
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
  retainConsecutiveSuccessors source lower (Search.candidates source)

/-- Soundness and completeness of the finite consecutive-minimal-vector
successor list. -/
theorem mem_consecutiveSuccessors_iff
    (source : GaussianInt.Fraction) (lower candidate : GaussianInt.Pair.Basic.ConvergentPair) :
    candidate ∈ consecutiveSuccessors source lower ↔
      Consecutive.Basic.AreConsecutiveBest source.value lower candidate := by
  constructor
  · intro member
    have selected := (mem_retainConsecutiveSuccessors_iff source lower candidate
      (Search.candidates source)).mp member
    exact (passesConsecutiveTest_iff source lower candidate).mp selected.2
  · intro consecutive
    exact (mem_retainConsecutiveSuccessors_iff source lower candidate
      (Search.candidates source)).mpr ⟨Search.IsBest.mem_candidates consecutive.2.1,
      (passesConsecutiveTest_iff source lower candidate).mpr consecutive⟩

/-- Filtering consecutive successors cannot increase the supplied candidate-list length. -/
theorem retainConsecutiveSuccessors_length_le
    (source : GaussianInt.Fraction) (lower : GaussianInt.Pair.Basic.ConvergentPair) (list : List
      GaussianInt.Pair.Basic.ConvergentPair) :
    (retainConsecutiveSuccessors source lower list).length ≤ list.length := by
  induction list with
  | nil => rfl
  | cons candidate remaining inductionHypothesis =>
      rw [retainConsecutiveSuccessors]
      by_cases passes : PassesConsecutiveTest source lower candidate
      · rw [if_pos passes, List.length_cons, List.length_cons]
        exact Nat.succ_le_succ inductionHypothesis
      · rw [if_neg passes, List.length_cons]
        exact inductionHypothesis.trans (Nat.le_succ _)

/-- The consecutive successor list inherits the explicit all-best candidate
bound. -/
theorem consecutiveSuccessors_length_le (source : GaussianInt.Fraction) (lower : GaussianInt.Pair.Basic.ConvergentPair)
  :
    (consecutiveSuccessors source lower).length ≤
      16 * (GaussianInt.normNat source.denominator + 1) ^ 2 *
        (Search.numeratorQuadranceBound source + 1) ^ 2 := by
  exact
    (retainConsecutiveSuccessors_length_le source lower (Search.candidates
      source)).trans_eq
      (Search.candidates_length source)

end Purelib.NumberTheory.Approximation.Best.Successor.Exhaustive

end
