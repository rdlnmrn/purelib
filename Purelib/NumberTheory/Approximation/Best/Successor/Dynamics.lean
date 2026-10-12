module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.List.Membership
import Purelib.Data.List.Filter

import Purelib.Data.List.Attach
import Purelib.Data.List.FilterMap
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Markov.Absorption.Rank
import Purelib.Measure.Distribution.Markov.Block
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Best.Search
public import Purelib.NumberTheory.Approximation.Best.Successor.Exhaustive
public import Purelib.NumberTheory.Approximation.Best.Successor.Local
import Purelib.Data.List.Multiplicity
public import Purelib.Measure.Distribution.Empirical.Basic

import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

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

namespace Purelib.NumberTheory.Approximation.Best.Successor.Dynamics

open Purelib.Data
open Purelib
open Purelib.NumberTheory.Approximation

/-- The executable Gaussian-denominator source type for successor dynamics. -/
abbrev Fraction := GaussianInt.Fraction
/-- The retained Gaussian integer numerator-denominator pair type. -/
abbrev Pair := GaussianInt.Pair.Basic.ConvergentPair

set_option genInjectivity false in
/-- One displayed state of the rational consecutive-minimal-vector
transversal. -/
structure State (source : Best.Successor.Dynamics.Fraction) where
  /-- The previous displayed best numerator-denominator pair. -/ previous : Best.Successor.Dynamics.Pair
  /-- The current displayed best numerator-denominator pair. -/ current : Best.Successor.Dynamics.Pair
  /-- The two retained pairs occupy consecutive best levels for the original source. -/ consecutive :
    Best.Consecutive.Basic.AreConsecutiveBest source.value previous current

constructive_injectivity State

/-- Two consecutive states agree when their previous and current pairs agree. -/
@[ext] theorem State.ext {source : Best.Successor.Dynamics.Fraction} {left right : Best.Successor.Dynamics.State source}
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
@[expose] def testedState? (source : Best.Successor.Dynamics.Fraction) (previous current : Best.Successor.Dynamics.Pair)
  :
    Option (Best.Successor.Dynamics.State source) :=
  if passes : Best.Successor.Exhaustive.PassesConsecutiveTest source previous current then
    some
      { previous := previous
        current := current
        consecutive :=
          (Best.Successor.Exhaustive.passesConsecutiveTest_iff source previous current).mp passes }
  else
    none

/-- Complete displayed finite transversal for one rational source.  The
outer and inner tables are both the finite `allBest` table. -/
@[expose] def states (source : Best.Successor.Dynamics.Fraction) : List (Best.Successor.Dynamics.State source) :=
  (Best.Search.allBest source).flatMap fun previous =>
    (Best.Search.allBest source).filterMap fun current =>
      Best.Successor.Dynamics.testedState? source previous current

/-- Every proof-bearing consecutive state occurs in the displayed finite
transversal. -/
theorem State.mem_states {source : Best.Successor.Dynamics.Fraction} (state : Best.Successor.Dynamics.State source) :
    state ∈ Best.Successor.Dynamics.states source := by
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨state.previous,
    (Best.Search.mem_allBest_iff_isBest source state.previous).mpr state.consecutive.1, ?_⟩
  apply Data.List.FilterMap.mem_filterMap.mpr
  refine ⟨state.current,
    (Best.Search.mem_allBest_iff_isBest source state.current).mpr state.consecutive.2.1, ?_⟩
  unfold Best.Successor.Dynamics.testedState?
  have passes := (Best.Successor.Exhaustive.passesConsecutiveTest_iff source state.previous state.current).mpr
    state.consecutive
  rw [dif_pos passes]

/-- Explicit squared bound inherited from the finite `allBest` rectangle. -/
@[expose] def stateCountBound (source : Best.Successor.Dynamics.Fraction) : Nat :=
  (16 *
    (GaussianInt.normNat
        source.denominator + 1) ^ 2 *
      (Best.Search.numeratorQuadranceBound source + 1) ^ 2) ^ 2

/-- The finite consecutive-state table meets the squared all-best candidate bound. -/
theorem states_length_le (source : Best.Successor.Dynamics.Fraction) :
    (Best.Successor.Dynamics.states source).length ≤ Best.Successor.Dynamics.stateCountBound source := by
  let bestBound := 16 *
    (GaussianInt.normNat
        source.denominator + 1) ^ 2 *
      (Best.Search.numeratorQuadranceBound source + 1) ^ 2
  have tableBound : (Best.Search.allBest source).length ≤ bestBound := by
    dsimp only [bestBound]
    exact Best.Search.allBest_length_le source
  calc
    (Best.Successor.Dynamics.states source).length ≤
        (Best.Search.allBest source).length * (Best.Search.allBest source).length := by
      exact Data.List.Flatten.length_flatMap_filterMap_le (Best.Search.allBest source)
        (fun previous current => Best.Successor.Dynamics.testedState? source previous current)
        (Best.Search.allBest source)
    _ ≤ bestBound * bestBound := Nat.mul_le_mul tableBound tableBound
    _ = Best.Successor.Dynamics.stateCountBound source := by
      unfold Best.Successor.Dynamics.stateCountBound
      dsimp only [bestBound]
      ring1

/-- Proof-bearing local successors of one transversal state.  Attaching list
membership lets the exact local-successor theorem certify every output. -/
@[expose] def successorStates {source : Best.Successor.Dynamics.Fraction} (state : Best.Successor.Dynamics.State source)
  :
    List (Best.Successor.Dynamics.State source) :=
  (Best.Successor.Local.successors source state.previous state.current).attach.map
    fun candidate =>
      { previous := state.current
        current := candidate.1
        consecutive :=
          (Best.Successor.Local.mem_successors_iff state.consecutive
            candidate.1).mp candidate.2 }

/-- Every local edge really advances to the next consecutive best level. -/
theorem mem_successorStates_data {source : Best.Successor.Dynamics.Fraction}
    {state target : Best.Successor.Dynamics.State source} (member : target ∈ Best.Successor.Dynamics.successorStates
      state) :
    target.previous = state.current ∧
      Best.Consecutive.Basic.AreConsecutiveBest source.value state.current target.current := by
  unfold Best.Successor.Dynamics.successorStates at member
  have member := Data.List.Map.mem_map.mp member
  rcases member with ⟨candidate, _, rfl⟩
  exact ⟨rfl,
    (Best.Successor.Local.mem_successors_iff state.consecutive candidate.1).mp
      candidate.2⟩

/-- Every certified local successor strictly increases the current denominator quadrance. -/
theorem mem_successorStates_denominator_strict {source : Best.Successor.Dynamics.Fraction}
    {state target : Best.Successor.Dynamics.State source} (member : target ∈ Best.Successor.Dynamics.successorStates
      state) :
    Best.Error.denominatorQuadrance state.current < Best.Error.denominatorQuadrance target.current :=
  (Best.Successor.Dynamics.mem_successorStates_data member).2.2.2.1

/-- Every local successor denominator quadrance is bounded by the source denominator quadrance. -/
theorem mem_successorStates_denominator_le_source {source : Best.Successor.Dynamics.Fraction}
    {state target : Best.Successor.Dynamics.State source} (member : target ∈ Best.Successor.Dynamics.successorStates
      state) :
    Best.Error.denominatorQuadrance target.current ≤
      GaussianInt.normNat source.denominator :=
  (Best.Search.IsBest.denominatorQuadrance_le_source (Best.Successor.Dynamics.mem_successorStates_data member).2.2.1)

/-- Every proof-bearing local successor belongs to the complete finite state table. -/
theorem mem_successorStates_mem_states {source : Best.Successor.Dynamics.Fraction}
    {state target : Best.Successor.Dynamics.State source} (_member : target ∈ Best.Successor.Dynamics.successorStates
      state) :
    target ∈ Best.Successor.Dynamics.states source :=
  target.mem_states

/-- Attaching consecutive-best certificates preserves the raw local successor-list length. -/
theorem successorStates_length_eq {source : Best.Successor.Dynamics.Fraction} (state : Best.Successor.Dynamics.State
  source) :
    (Best.Successor.Dynamics.successorStates state).length =
      (Best.Successor.Local.successors source state.previous state.current).length := by
  rw [Best.Successor.Dynamics.successorStates, Data.List.Map.length_map]
  have lengthIdentity := congrArg List.length
    (Data.List.attach_map_subtype_val (Best.Successor.Local.successors source state.previous state.current))
  rw [Data.List.Map.length_map] at lengthIdentity
  exact lengthIdentity

/-- The proof-bearing transition table inherits the coefficient-space bound
of the local successor generator. -/
theorem successorStates_length_le {source : Best.Successor.Dynamics.Fraction} (state : Best.Successor.Dynamics.State
  source) :
    (Best.Successor.Dynamics.successorStates state).length ≤
      64 * (Best.Successor.Local.trailingCoefficientBound
        source state.previous + 1) ^ 2 := by
  rw [Best.Successor.Dynamics.successorStates_length_eq]
  calc
    (Best.Successor.Local.successors source state.previous state.current).length ≤
        (Best.Successor.Local.candidates source state.previous
          state.current).length := by
      unfold Best.Successor.Local.successors
      exact Data.List.Filter.length_filter_le _ _
    _ ≤ 64 * (Best.Successor.Local.trailingCoefficientBound
          source state.previous + 1) ^ 2 :=
      Best.Successor.Local.candidates_length_le source state.previous
        state.current

/-- Terminality of the computed state is exact: the list is empty precisely
when there is no next consecutive best denominator level. -/
theorem successorStates_eq_nil_iff {source : Best.Successor.Dynamics.Fraction} (state : Best.Successor.Dynamics.State
  source) :
    Best.Successor.Dynamics.successorStates state = [] ↔
      ∀ next : Best.Successor.Dynamics.Pair,
        ¬ Best.Consecutive.Basic.AreConsecutiveBest source.value state.current next := by
  constructor
  · intro empty next consecutive
    have rawMember : next ∈ Best.Successor.Local.successors source
        state.previous state.current :=
      (Best.Successor.Local.mem_successors_iff state.consecutive next).mpr
        consecutive
    let attached :
        { candidate // candidate ∈ Best.Successor.Local.successors source
          state.previous state.current } := ⟨next, rawMember⟩
    have attachedMember : attached ∈
        (Best.Successor.Local.successors source state.previous
          state.current).attach := Data.List.Attach.mem_attach _ _
    have mappedMember :
        ({ previous := state.current
           current := attached.1
           consecutive :=
             (Best.Successor.Local.mem_successors_iff state.consecutive
               attached.1).mp attached.2 } : Best.Successor.Dynamics.State source) ∈
          Best.Successor.Dynamics.successorStates state := by
      unfold Best.Successor.Dynamics.successorStates
      exact Data.List.Map.mem_map_of_mem attachedMember
    rw [empty] at mappedMember
    exact List.not_mem_nil mappedMember
  · intro noNext
    cases listIdentity : Best.Successor.Dynamics.successorStates state with
    | nil => rfl
    | cons target remaining =>
        have member : target ∈ Best.Successor.Dynamics.successorStates state := by
          rw [listIdentity]
          exact List.mem_cons_self
        exact (noNext target.current (Best.Successor.Dynamics.mem_successorStates_data member).2).elim

/-- Uniform distribution on the genuine local successors, with one explicit
regeneration edge to `seed` exactly at a terminal state. -/
@[expose] def regeneratedTransition {source : Best.Successor.Dynamics.Fraction} (seed : Best.Successor.Dynamics.State
  source) :
    Best.Successor.Dynamics.State source → Measure.Distribution (Best.Successor.Dynamics.State source) :=
  fun state =>
    let next := Best.Successor.Dynamics.successorStates state
    if positive : 0 < next.length then
      Measure.empiricalDistribution next positive
    else
      Measure.Distribution.pure seed

/-- Every atom of the regenerative transition is either a certified local
successor or the explicitly marked terminal reset. -/
theorem regeneratedTransition_atom {source : Best.Successor.Dynamics.Fraction} (seed state :
  Best.Successor.Dynamics.State source)
    (atom : Measure.Weighted (Best.Successor.Dynamics.State source))
    (member : atom ∈ (Best.Successor.Dynamics.regeneratedTransition seed state).atoms) :
    atom.item ∈ Best.Successor.Dynamics.successorStates state ∨
      Best.Successor.Dynamics.successorStates state = [] ∧ atom.item = seed := by
  by_cases positive : 0 < (Best.Successor.Dynamics.successorStates state).length
  · left
    unfold Best.Successor.Dynamics.regeneratedTransition at member
    simp only [dif_pos positive] at member
    exact Data.List.sampleContains_mem atom.item
      (Measure.empiricalDistribution_atom_sampleContains
        (Best.Successor.Dynamics.successorStates state) positive atom member)
  · right
    have empty : Best.Successor.Dynamics.successorStates state = [] :=
      List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos positive)
    refine ⟨empty, ?_⟩
    unfold Best.Successor.Dynamics.regeneratedTransition at member
    rw [dif_neg positive] at member
    have atomIdentity := Data.List.Membership.mem_singleton.mp member
    exact congrArg Measure.Weighted.item atomIdentity

open Purelib.NumberTheory.Approximation.Best.Successor.Dynamics in
/-- Thus the transition never leaves the displayed bounded transversal. -/
theorem regeneratedTransition_atom_mem_states {source : Best.Successor.Dynamics.Fraction}
    (seed state : Best.Successor.Dynamics.State source)
    (atom : Measure.Weighted (Best.Successor.Dynamics.State source))
    (member : atom ∈ (Best.Successor.Dynamics.regeneratedTransition seed state).atoms) :
    atom.item ∈ Best.Successor.Dynamics.states source := by
  rcases regeneratedTransition_atom seed state atom member with
      successor | reset
  · exact Best.Successor.Dynamics.mem_successorStates_mem_states successor
  · rw [reset.2]
    exact seed.mem_states

/-- Executable event identifying one supplied seed by its two displayed pair
coordinates.  Proof fields are deliberately ignored. -/
@[expose] def seedEvent {source : Best.Successor.Dynamics.Fraction} (seed : Best.Successor.Dynamics.State source) :
    Best.Successor.Dynamics.State source → Bool :=
  fun state => decide
    (state.previous = seed.previous ∧ state.current = seed.current)

/-- The executable seed test succeeds exactly on the retained seed state. -/
theorem seedEvent_eq_true_iff {source : Best.Successor.Dynamics.Fraction}
    (seed state : Best.Successor.Dynamics.State source) :
    Best.Successor.Dynamics.seedEvent seed state = true ↔ state = seed := by
  constructor
  · intro selected
    have equal : state.previous = seed.previous ∧ state.current = seed.current := of_decide_eq_true selected
    exact Best.Successor.Dynamics.State.ext equal.1 equal.2
  · intro equal
    subst state
    exact decide_eq_true ⟨rfl, rfl⟩

/-- Natural rank remaining before the source denominator bound is exhausted.
Every genuine local successor strictly decreases it. -/
@[expose] def remainingRank {source : Best.Successor.Dynamics.Fraction} (state : Best.Successor.Dynamics.State source) :
  Nat :=
  GaussianInt.normNat source.denominator -
    Best.Error.denominatorQuadrance state.current

/-- The remaining denominator rank is below the source quadrance plus one. -/
theorem remainingRank_lt_sourceBound {source : Best.Successor.Dynamics.Fraction}
    (state : Best.Successor.Dynamics.State source) :
    Best.Successor.Dynamics.remainingRank state <
      GaussianInt.normNat source.denominator +
        1 := by
  unfold Best.Successor.Dynamics.remainingRank
  omega

/-- Stopped regenerative dynamics: the seed is absorbing; away from it the
kernel follows genuine local successors until the terminal reset.  The seed
hold and terminal reset are the two explicit non-successor edges. -/
@[expose] def stoppedTransition {source : Best.Successor.Dynamics.Fraction} (seed : Best.Successor.Dynamics.State
  source) :
    Best.Successor.Dynamics.State source → Measure.Distribution (Best.Successor.Dynamics.State source) :=
  fun state =>
    if _selected : Best.Successor.Dynamics.seedEvent seed state = true then
      Measure.Distribution.pure seed
    else
      Best.Successor.Dynamics.regeneratedTransition seed state

open Purelib.NumberTheory.Approximation.Best.Successor.Dynamics in
/-- The stopped successor kernel is ranked absorbing.  Outside the seed,
each atom is either the terminal reset into the seed or a genuine successor
with strictly smaller remaining rank. -/
theorem stoppedTransition_rankedAbsorbing {source : Best.Successor.Dynamics.Fraction}
    (seed : Best.Successor.Dynamics.State source) :
    Measure.Distribution.RankedAbsorbing
      (Best.Successor.Dynamics.stoppedTransition seed) (Best.Successor.Dynamics.seedEvent seed) remainingRank := by
  constructor
  · intro state selected atom member
    unfold Best.Successor.Dynamics.stoppedTransition at member
    simp only [dif_pos selected] at member
    have atomIdentity := Data.List.Membership.mem_singleton.mp member
    apply (Best.Successor.Dynamics.seedEvent_eq_true_iff seed atom.item).mpr
    exact congrArg Measure.Weighted.item atomIdentity
  · intro state notSelected atom member
    have selectedNe : Best.Successor.Dynamics.seedEvent seed state ≠ true := by
      intro selected
      rw [notSelected] at selected
      cases selected
    unfold Best.Successor.Dynamics.stoppedTransition at member
    simp only [dif_neg selectedNe] at member
    rcases regeneratedTransition_atom seed state atom member with
        successor | reset
    · right
      have strict := Best.Successor.Dynamics.mem_successorStates_denominator_strict successor
      have bounded := Best.Successor.Dynamics.mem_successorStates_denominator_le_source successor
      unfold Best.Successor.Dynamics.remainingRank
      omega
    · left
      apply (Best.Successor.Dynamics.seedEvent_eq_true_iff seed atom.item).mpr
      exact reset.2

/-- One uniform block, bounded only by the displayed source denominator,
reaches the stopped seed with probability exactly one from every state. -/
@[expose] def stoppedBlockHitCertificate {source : Best.Successor.Dynamics.Fraction} (seed :
  Best.Successor.Dynamics.State source) :
    Measure.Distribution.UniformBlockHitCertificate
      (Best.Successor.Dynamics.stoppedTransition seed) (Best.Successor.Dynamics.seedEvent seed) :=
  (Best.Successor.Dynamics.stoppedTransition_rankedAbsorbing seed).blockHitCertificate
    (GaussianInt.normNat source.denominator + 1)
    (by omega)
    Best.Successor.Dynamics.remainingRank_lt_sourceBound

/-- The stopped hitting certificate uses the source denominator quadrance plus one steps. -/
theorem stoppedBlockLength {source : Best.Successor.Dynamics.Fraction} (seed : Best.Successor.Dynamics.State source) :
    (Best.Successor.Dynamics.stoppedBlockHitCertificate seed).blockLength =
      GaussianInt.normNat source.denominator +
        1 := by
  rfl

/-- The stopped hitting certificate has probability rate exactly one. -/
theorem stoppedBlockRate {source : Best.Successor.Dynamics.Fraction} (seed : Best.Successor.Dynamics.State source) :
    (Best.Successor.Dynamics.stoppedBlockHitCertificate seed).rate = 1 := by
  rfl

end Purelib.NumberTheory.Approximation.Best.Successor.Dynamics
