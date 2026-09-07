import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Empirical
import FiniteMeasure.RankedAbsorption
import RFAP.Approximation.LocalSuccessor

/-!
# Finite coefficient-local successor dynamics

For one displayed rational Gaussian source, consecutive best levels form a
finite executable transversal.  Its states are adjacent best pairs, obtained
by filtering the already bounded `allBest` table.  From each state, the local
successor generator emits exactly the next consecutive level; if no next
level exists, the regenerative transition returns to one supplied seed.

The reset is explicit and is not asserted to be part of the Gaussian
continued-fraction dynamics.  Every non-reset edge is nevertheless certified
by the coefficient-local successor theorem.  This separation will let the
finite return argument account honestly for the regeneration boundary.
-/

namespace RFAP.SuccessorDynamics

abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation

/-- One displayed state of the rational consecutive-minimal-vector
transversal. -/
structure State (source : Fraction) where
  previous : Pair
  current : Pair
  consecutive : AreConsecutiveBest source.value previous current

@[ext] theorem State.ext {source : Fraction} {left right : State source}
    (previous : left.previous = right.previous)
    (current : left.current = right.current) :
    left = right := by
  cases left
  cases right
  cases previous
  cases current
  rfl

/-- Run the executable bounded consecutive-level test and retain its proof in
the returned state. -/
def testedState? (source : Fraction) (previous current : Pair) :
    Option (State source) :=
  if passes : PassesConsecutiveTest source previous current then
    some
      { previous := previous
        current := current
        consecutive :=
          (passesConsecutiveTest_iff source previous current).mp passes }
  else
    none

/-- Complete displayed finite transversal for one rational source.  The
outer and inner tables are both the finite `allBest` table. -/
def states (source : Fraction) : List (State source) :=
  (allBest source).flatMap fun previous =>
    (allBest source).filterMap fun current =>
      testedState? source previous current

/-- Every proof-bearing consecutive state occurs in the displayed finite
transversal. -/
theorem State.mem_states {source : Fraction} (state : State source) :
    state ∈ states source := by
  rw [states, QuotientFreeList.mem_flatMap]
  refine ⟨state.previous,
    (mem_allBest_iff_isBest source state.previous).mpr state.consecutive.1,
    ?_⟩
  rw [QuotientFreeList.mem_filterMap]
  refine ⟨state.current,
    (mem_allBest_iff_isBest source state.current).mpr state.consecutive.2.1,
    ?_⟩
  unfold testedState?
  have passes :=
    (passesConsecutiveTest_iff source state.previous state.current).mpr
      state.consecutive
  rw [dif_pos passes]

private theorem length_filterMap_le
    {input output : Type} (function : input → Option output) :
    ∀ values : List input, (values.filterMap function).length ≤ values.length
  | [] => le_rfl
  | value :: remaining => by
      cases selected : function value with
      | none =>
          simp only [List.filterMap_cons, selected, List.length_cons]
          exact (length_filterMap_le function remaining).trans
            (Nat.le_succ _)
      | some result =>
          simp only [List.filterMap_cons, selected, List.length_cons]
          exact Nat.succ_le_succ (length_filterMap_le function remaining)

private theorem length_flatMap_filterMap_le
    {outer inner output : Type} (right : List inner)
    (function : outer → inner → Option output) :
    ∀ left : List outer,
      (left.flatMap fun first => right.filterMap (function first)).length ≤
        left.length * right.length
  | [] => by
      simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
      exact le_rfl
  | first :: remaining => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        Nat.succ_mul]
      have headBound := length_filterMap_le (function first) right
      have tailBound :=
        length_flatMap_filterMap_le right function remaining
      omega

/-- Explicit squared bound inherited from the finite `allBest` rectangle. -/
def stateCountBound (source : Fraction) : Nat :=
  (16 *
    (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        source.denominator + 1) ^ 2 *
      (numeratorQuadranceBound source + 1) ^ 2) ^ 2

theorem states_length_le (source : Fraction) :
    (states source).length ≤ stateCountBound source := by
  let bestBound := 16 *
    (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        source.denominator + 1) ^ 2 *
      (numeratorQuadranceBound source + 1) ^ 2
  have tableBound : (allBest source).length ≤ bestBound := by
    simpa only [bestBound] using allBest_length_le source
  calc
    (states source).length ≤
        (allBest source).length * (allBest source).length := by
      exact length_flatMap_filterMap_le (allBest source)
        (fun previous current => testedState? source previous current)
        (allBest source)
    _ ≤ bestBound * bestBound := Nat.mul_le_mul tableBound tableBound
    _ = stateCountBound source := by
      unfold stateCountBound
      dsimp only [bestBound]
      ring1

/-- Proof-bearing local successors of one transversal state.  Attaching list
membership lets the exact local-successor theorem certify every output. -/
def successorStates {source : Fraction} (state : State source) :
    List (State source) :=
  (RFAP.LocalSuccessor.successors source state.previous state.current).attach.map
    fun candidate =>
      { previous := state.current
        current := candidate.1
        consecutive :=
          (RFAP.LocalSuccessor.mem_successors_iff state.consecutive
            candidate.1).mp candidate.2 }

/-- Every local edge really advances to the next consecutive best level. -/
theorem mem_successorStates_data {source : Fraction}
    {state target : State source} (member : target ∈ successorStates state) :
    target.previous = state.current ∧
      AreConsecutiveBest source.value state.current target.current := by
  rw [successorStates, QuotientFreeList.mem_map] at member
  rcases member with ⟨candidate, _, rfl⟩
  exact ⟨rfl,
    (RFAP.LocalSuccessor.mem_successors_iff state.consecutive candidate.1).mp
      candidate.2⟩

theorem mem_successorStates_denominator_strict {source : Fraction}
    {state target : State source} (member : target ∈ successorStates state) :
    denominatorQuadrance state.current < denominatorQuadrance target.current :=
  (mem_successorStates_data member).2.2.2.1

theorem mem_successorStates_denominator_le_source {source : Fraction}
    {state target : State source} (member : target ∈ successorStates state) :
    denominatorQuadrance target.current ≤
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat source.denominator :=
  (mem_successorStates_data member).2.2.1.denominatorQuadrance_le_source

theorem mem_successorStates_mem_states {source : Fraction}
    {state target : State source} (_member : target ∈ successorStates state) :
    target ∈ states source :=
  target.mem_states

theorem successorStates_length_eq {source : Fraction} (state : State source) :
    (successorStates state).length =
      (RFAP.LocalSuccessor.successors source state.previous state.current).length := by
  simp only [successorStates, List.length_map, List.length_attach]

/-- The proof-bearing transition table inherits the coefficient-space bound
of the local successor generator. -/
theorem successorStates_length_le {source : Fraction} (state : State source) :
    (successorStates state).length ≤
      64 * (RFAP.LocalSuccessor.trailingCoefficientBound
        source state.previous + 1) ^ 2 := by
  rw [successorStates_length_eq]
  calc
    (RFAP.LocalSuccessor.successors source state.previous state.current).length ≤
        (RFAP.LocalSuccessor.candidates source state.previous
          state.current).length := by
      unfold RFAP.LocalSuccessor.successors
      exact List.length_filter_le _ _
    _ ≤ 64 * (RFAP.LocalSuccessor.trailingCoefficientBound
          source state.previous + 1) ^ 2 :=
      RFAP.LocalSuccessor.candidates_length_le source state.previous
        state.current

/-- Terminality of the computed state is exact: the list is empty precisely
when there is no next consecutive best denominator level. -/
theorem successorStates_eq_nil_iff {source : Fraction} (state : State source) :
    successorStates state = [] ↔
      ∀ next : Pair,
        ¬ AreConsecutiveBest source.value state.current next := by
  constructor
  · intro empty next consecutive
    have rawMember : next ∈ RFAP.LocalSuccessor.successors source
        state.previous state.current :=
      (RFAP.LocalSuccessor.mem_successors_iff state.consecutive next).mpr
        consecutive
    let attached :
        { candidate // candidate ∈ RFAP.LocalSuccessor.successors source
          state.previous state.current } := ⟨next, rawMember⟩
    have attachedMember : attached ∈
        (RFAP.LocalSuccessor.successors source state.previous
          state.current).attach := QuotientFreeList.mem_attach _ _
    have mappedMember :
        ({ previous := state.current
           current := attached.1
           consecutive :=
             (RFAP.LocalSuccessor.mem_successors_iff state.consecutive
               attached.1).mp attached.2 } : State source) ∈
          successorStates state := by
      unfold successorStates
      exact QuotientFreeList.mem_map_of_mem attachedMember
    rw [empty] at mappedMember
    exact List.not_mem_nil mappedMember
  · intro noNext
    cases listIdentity : successorStates state with
    | nil => rfl
    | cons target remaining =>
        have member : target ∈ successorStates state := by
          rw [listIdentity]
          exact List.mem_cons_self
        exact (noNext target.current (mem_successorStates_data member).2).elim

/-- Uniform distribution on the genuine local successors, with one explicit
regeneration edge to `seed` exactly at a terminal state. -/
def regeneratedTransition {source : Fraction} (seed : State source) :
    State source → _root_.FiniteMeasure.Distribution (State source) :=
  fun state =>
    let next := successorStates state
    if positive : 0 < next.length then
      _root_.FiniteMeasure.empiricalDistribution next positive
    else
      _root_.FiniteMeasure.Distribution.pure seed

/-- Every atom of the regenerative transition is either a certified local
successor or the explicitly marked terminal reset. -/
theorem regeneratedTransition_atom {source : Fraction} (seed state : State source)
    (atom : _root_.FiniteMeasure.Weighted (State source))
    (member : atom ∈ (regeneratedTransition seed state).atoms) :
    atom.item ∈ successorStates state ∨
      successorStates state = [] ∧ atom.item = seed := by
  by_cases positive : 0 < (successorStates state).length
  · left
    unfold regeneratedTransition at member
    simp only [dif_pos positive] at member
    exact _root_.FiniteMeasure.sampleContains_mem atom.item
      (_root_.FiniteMeasure.empiricalDistribution_atom_sampleContains
        (successorStates state) positive atom member)
  · right
    have empty : successorStates state = [] :=
      List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos positive)
    refine ⟨empty, ?_⟩
    unfold regeneratedTransition at member
    simp only [empty, List.length_nil, lt_self_iff_false] at member
    have atomIdentity := List.mem_singleton.mp member
    exact congrArg _root_.FiniteMeasure.Weighted.item atomIdentity

/-- Thus the transition never leaves the displayed bounded transversal. -/
theorem regeneratedTransition_atom_mem_states {source : Fraction}
    (seed state : State source)
    (atom : _root_.FiniteMeasure.Weighted (State source))
    (member : atom ∈ (regeneratedTransition seed state).atoms) :
    atom.item ∈ states source := by
  rcases regeneratedTransition_atom seed state atom member with
      successor | reset
  · exact mem_successorStates_mem_states successor
  · rw [reset.2]
    exact seed.mem_states

/-- Executable event identifying one supplied seed by its two displayed pair
coordinates.  Proof fields are deliberately ignored. -/
def seedEvent {source : Fraction} (seed : State source) :
    State source → Bool :=
  fun state => decide
    (state.previous = seed.previous ∧ state.current = seed.current)

theorem seedEvent_eq_true_iff {source : Fraction}
    (seed state : State source) :
    seedEvent seed state = true ↔ state = seed := by
  unfold seedEvent
  rw [decide_eq_true_eq]
  constructor
  · intro equal
    exact State.ext equal.1 equal.2
  · intro equal
    subst state
    exact ⟨rfl, rfl⟩

/-- Natural rank remaining before the source denominator bound is exhausted.
Every genuine local successor strictly decreases it. -/
def remainingRank {source : Fraction} (state : State source) : Nat :=
  RFAP.ConstructiveGaussianHeight.GaussianInt.normNat source.denominator -
    denominatorQuadrance state.current

theorem remainingRank_lt_sourceBound {source : Fraction}
    (state : State source) :
    remainingRank state <
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat source.denominator +
        1 := by
  unfold remainingRank
  omega

/-- Stopped regenerative dynamics: the seed is absorbing; away from it the
kernel follows genuine local successors until the terminal reset.  The seed
hold and terminal reset are the two explicit non-successor edges. -/
def stoppedTransition {source : Fraction} (seed : State source) :
    State source → _root_.FiniteMeasure.Distribution (State source) :=
  fun state =>
    if _selected : seedEvent seed state = true then
      _root_.FiniteMeasure.Distribution.pure seed
    else
      regeneratedTransition seed state

/-- The stopped successor kernel is ranked absorbing.  Outside the seed,
each atom is either the terminal reset into the seed or a genuine successor
with strictly smaller remaining rank. -/
theorem stoppedTransition_rankedAbsorbing {source : Fraction}
    (seed : State source) :
    _root_.FiniteMeasure.Distribution.RankedAbsorbing
      (stoppedTransition seed) (seedEvent seed) remainingRank := by
  constructor
  · intro state selected atom member
    unfold stoppedTransition at member
    simp only [dif_pos selected] at member
    have atomIdentity := List.mem_singleton.mp member
    apply (seedEvent_eq_true_iff seed atom.item).mpr
    exact congrArg _root_.FiniteMeasure.Weighted.item atomIdentity
  · intro state notSelected atom member
    have selectedNe : seedEvent seed state ≠ true := by
      intro selected
      rw [notSelected] at selected
      cases selected
    unfold stoppedTransition at member
    simp only [dif_neg selectedNe] at member
    rcases regeneratedTransition_atom seed state atom member with
        successor | reset
    · right
      have strict := mem_successorStates_denominator_strict successor
      have bounded := mem_successorStates_denominator_le_source successor
      unfold remainingRank
      omega
    · left
      apply (seedEvent_eq_true_iff seed atom.item).mpr
      exact reset.2

/-- One uniform block, bounded only by the displayed source denominator,
reaches the stopped seed with probability exactly one from every state. -/
def stoppedBlockHitCertificate {source : Fraction} (seed : State source) :
    _root_.FiniteMeasure.Distribution.UniformBlockHitCertificate
      (stoppedTransition seed) (seedEvent seed) :=
  (stoppedTransition_rankedAbsorbing seed).blockHitCertificate
    (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat source.denominator + 1)
    (by omega)
    remainingRank_lt_sourceBound

theorem stoppedBlockLength {source : Fraction} (seed : State source) :
    (stoppedBlockHitCertificate seed).blockLength =
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat source.denominator +
        1 := by
  rfl

theorem stoppedBlockRate {source : Fraction} (seed : State source) :
    (stoppedBlockHitCertificate seed).rate = 1 := by
  rfl

end RFAP.SuccessorDynamics
