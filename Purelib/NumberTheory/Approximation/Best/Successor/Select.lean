module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.NumberTheory.Approximation.Best.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Best.Search
public import Purelib.NumberTheory.Approximation.Best.Successor.Exhaustive
import Purelib.NumberTheory.Approximation.Best.Successor.Local
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data

open Purelib.NumberTheory.Approximation

section
@[expose] public section

/-!
# Best approximations of finite RAT responses

A root-approximation track is a finite request-and-response object, not an
unnamed completed root.  One response contains a displayed rational sample
strictly inside its new winding-one box, together with a polynomial residual
bound.  This module converts that sample to the Gaussian-denominator format
used by the best-approximation calculation.

The resulting program emits only pairs satisfying the full two-tier best
predicate for the displayed RAT response.  From a supplied best pair it
selects one pair at the next occupied denominator level.  The selector is
empty exactly when the supplied pair already has zero error, so every call
constructively returns either a genuine next best pair or an exact terminal
certificate.

No assertion is made about an unrepresented limiting point of the track.
-/

namespace Purelib.NumberTheory.Approximation.Best.Successor.Select

/-! ## Exact finite successor selection -/

/-- Select one representative from the next occupied best denominator level.
The complete finite successor list may contain several tied representatives;
this program deterministically retains its first one. -/
def nextBest? (source : GaussianInt.Fraction) (lower :
  GaussianInt.Pair.Basic.ConvergentPair) : Option GaussianInt.Pair.Basic.ConvergentPair :=
  match Best.Successor.Exhaustive.consecutiveSuccessors source lower with
  | [] => none
  | next :: _ => some next

/-- Every pair emitted by `nextBest?` really is at the consecutive best level
above the supplied pair. -/
theorem nextBest?_sound
    {source : GaussianInt.Fraction} {lower next : GaussianInt.Pair.Basic.ConvergentPair}
    (selected : nextBest? source lower = some next) :
    Best.Consecutive.Basic.AreConsecutiveBest source.value lower next := by
  unfold nextBest? at selected
  cases listIdentity : Best.Successor.Exhaustive.consecutiveSuccessors source lower with
  | nil =>
      rw [listIdentity] at selected
      cases selected
  | cons head remaining =>
      rw [listIdentity] at selected
      have headIdentity : head = next := Option.some.inj selected
      subst next
      apply (Best.Successor.Exhaustive.mem_consecutiveSuccessors_iff source lower head).mp
      rw [listIdentity]
      exact List.mem_cons_self

/-- Finite descent from the displayed exact pair produces a best pair with
exactly zero error. -/
theorem exists_zeroErrorBest (source :
  GaussianInt.Fraction) :
    ∃ pair : GaussianInt.Pair.Basic.ConvergentPair,
      Best.Basic.IsBest source.value pair ∧ Best.Error.errorQuadrance source.value pair = 0 := by
  have exactSmall : Best.Error.errorQuadrance source.value (Best.Search.exactPair source) ≤ 1 / 2 := by
    rw [Best.Error.errorQuadrance, Best.Search.exactPair_error,
      Gaussian.Norm.Basic.normSq_zero]
    decide
  obtain ⟨pair, best, _, errorLe⟩ :=
    Best.Search.exists_best_below_of_small source.denominatorNonzero le_rfl exactSmall
  have exactZero : Best.Error.errorQuadrance source.value (Best.Search.exactPair source) = 0 := by
    rw [Best.Error.errorQuadrance, Best.Search.exactPair_error,
      Gaussian.Norm.Basic.normSq_zero]
  rw [exactZero] at errorLe
  have nonnegative : 0 ≤ Best.Error.errorQuadrance source.value pair := by
    unfold Best.Error.errorQuadrance
    exact Gaussian.Norm.Basic.normSq_nonneg _
  exact ⟨pair, best, le_antisymm errorLe nonnegative⟩

/-- Every nonterminal best pair has a computable next occupied best level.
The proof first constructs a zero-error terminal best pair and then performs
a finite minimum over the displayed best pairs lying strictly above `lower`.
-/
theorem exists_nextBest_of_error_ne_zero
    {source : GaussianInt.Fraction} {lower : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest source.value lower)
    (errorNonzero : Best.Error.errorQuadrance source.value lower ≠ 0) :
    ∃ next : GaussianInt.Pair.Basic.ConvergentPair,
      nextBest? source lower = some next ∧
        Best.Consecutive.Basic.AreConsecutiveBest source.value lower next := by
  obtain ⟨terminal, terminalBest, terminalZero⟩ :=
    exists_zeroErrorBest source
  have lowerBeforeTerminal :
      Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance terminal := by
    apply Nat.lt_of_not_ge
    intro terminalNoHigher
    have lowerErrorLeZero := lowerBest.2.2 terminal terminalBest.1
      terminalNoHigher
    rw [terminalZero] at lowerErrorLeZero
    have lowerErrorNonnegative :
        0 ≤ Best.Error.errorQuadrance source.value lower := by
      unfold Best.Error.errorQuadrance
      exact Gaussian.Norm.Basic.normSq_nonneg _
    exact errorNonzero (le_antisymm lowerErrorLeZero lowerErrorNonnegative)
  obtain ⟨witness, consecutive, _⟩ :=
    Best.Successor.Local.exists_consecutiveBest_below
      lowerBest terminalBest lowerBeforeTerminal
  have witnessMember : witness ∈ Best.Successor.Exhaustive.consecutiveSuccessors source lower :=
    (Best.Successor.Exhaustive.mem_consecutiveSuccessors_iff source lower witness).mpr consecutive
  cases listIdentity : Best.Successor.Exhaustive.consecutiveSuccessors source lower with
  | nil =>
      rw [listIdentity] at witnessMember
      exact (List.not_mem_nil witnessMember).elim
  | cons next remaining =>
      refine ⟨next, ?_, ?_⟩
      · simp only [-eq_self, -iff_self, nextBest?, listIdentity]
        rfl
      · apply (Best.Successor.Exhaustive.mem_consecutiveSuccessors_iff source lower next).mp
        rw [listIdentity]
        exact List.mem_cons_self

/-- A zero-error best pair has no later best denominator level. -/
theorem nextBest?_eq_none_of_error_eq_zero
    {source : GaussianInt.Fraction} {lower : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest source.value lower)
    (errorZero : Best.Error.errorQuadrance source.value lower = 0) :
    nextBest? source lower = none := by
  unfold nextBest?
  cases listIdentity : Best.Successor.Exhaustive.consecutiveSuccessors source lower with
  | nil => rfl
  | cons next remaining =>
      have nextConsecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower next := by
        apply (Best.Successor.Exhaustive.mem_consecutiveSuccessors_iff source lower next).mp
        rw [listIdentity]
        exact List.mem_cons_self
      have impossible := nextConsecutive.2.1.2.1 lower lowerBest.1
        nextConsecutive.2.2.1
      rw [errorZero] at impossible
      exact (not_lt_of_ge
        (Gaussian.Norm.Basic.normSq_nonneg _)
        impossible).elim

/-- Exact terminal specification of the executable next-best selector. -/
theorem nextBest?_eq_none_iff
    {source : GaussianInt.Fraction} {lower : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest source.value lower) :
    nextBest? source lower = none ↔
      Best.Error.errorQuadrance source.value lower = 0 := by
  constructor
  · intro selectedNone
    by_cases errorZero : Best.Error.errorQuadrance source.value lower = 0
    · exact errorZero
    · obtain ⟨next, selected, _⟩ :=
        exists_nextBest_of_error_ne_zero lowerBest errorZero
      rw [selectedNone] at selected
      cases selected
  · exact nextBest?_eq_none_of_error_eq_zero lowerBest

/-- Total finite alternative: a best pair has a certified consecutive
successor, or it is already an exact terminal for the displayed source. -/
theorem nextBest_or_exactTerminal
    {source : GaussianInt.Fraction} {lower : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest source.value lower) :
    (∃ next : GaussianInt.Pair.Basic.ConvergentPair,
      nextBest? source lower = some next ∧
        Best.Consecutive.Basic.AreConsecutiveBest source.value lower next) ∨
      Best.Error.errorQuadrance source.value lower = 0 := by
  by_cases errorZero : Best.Error.errorQuadrance source.value lower = 0
  · exact Or.inr errorZero
  · exact Or.inl (exists_nextBest_of_error_ne_zero lowerBest errorZero)
end Purelib.NumberTheory.Approximation.Best.Successor.Select

end
