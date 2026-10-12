module
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Nearest
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Measure.Distribution.Basic
import Purelib.NumberTheory.Approximation.Best.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Best.Search
import Purelib.NumberTheory.Approximation.Best.Successor.Dynamics
import Purelib.NumberTheory.Approximation.Best.Successor.Local
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
public import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.StoppedSuccessor
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Bounds
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Optimal
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Global finite Dirichlet requests for rational sources

The root-free consecutive-window bound becomes a genuine global request
theorem after selecting the last best denominator below a supplied natural
quadrance request.  A unit-denominator nearest pair supplies the first best
level.  Finite descent from the exact rational pair supplies a terminal best
level of zero error.  A finite maximum over `allBest` then either already has
zero error or is followed by a consecutive level bracketing the request.

This is the displayed-rational, squared, natural-request counterpart of the
universal half of Chevallier's complex Dirichlet theorem.  The final theorem
pairs it with the robust stopped-successor sharpness result on the opposite
side of the rational quadratic cut.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Theorem

/-- Best pairs whose denominator quadrance is strictly below the displayed
request. -/
@[expose] def bestBelowRequest (source : GaussianInt.Fraction) (request : Nat) : List
  GaussianInt.Pair.Basic.ConvergentPair :=
  (Best.Search.allBest source).filter fun pair =>
    decide (Best.Error.denominatorQuadrance pair < request)

/-- The filtered finite list contains exactly the best pairs with denominator quadrance strictly below the request. -/
theorem mem_bestBelowRequest_iff (source : GaussianInt.Fraction) (request : Nat)
    (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    pair ∈ Dirichlet.Theorem.bestBelowRequest source request ↔
      Best.Basic.IsBest source.value pair ∧ Best.Error.denominatorQuadrance pair < request := by
  constructor
  · intro member
    have retained := Data.List.Filter.mem_filter.mp member
    exact ⟨(Best.Search.mem_allBest_iff_isBest source pair).mp retained.1,
      of_decide_eq_true retained.2⟩
  · intro retained
    exact Data.List.Filter.mem_filter.mpr
      ⟨(Best.Search.mem_allBest_iff_isBest source pair).mpr retained.1, decide_eq_true retained.2⟩

/-- Select a pair of greatest denominator quadrance from a displayed finite
list.  Ties retain the earlier record. -/
@[expose] def selectDenominatorMaximum : List GaussianInt.Pair.Basic.ConvergentPair → Option
  GaussianInt.Pair.Basic.ConvergentPair
  | [] => none
  | candidate :: remaining =>
      match Purelib.NumberTheory.Approximation.Dirichlet.Theorem.selectDenominatorMaximum remaining with
      | none => some candidate
      | some selected =>
          if Best.Error.denominatorQuadrance selected ≤ Best.Error.denominatorQuadrance candidate then
            some candidate
          else
            some selected

/-- Every successful maximum-denominator selection is a member of the original finite list. -/
theorem selectDenominatorMaximum_mem
    {list : List GaussianInt.Pair.Basic.ConvergentPair} {selected : GaussianInt.Pair.Basic.ConvergentPair}
    (selection : Dirichlet.Theorem.selectDenominatorMaximum list = some selected) :
    selected ∈ list := by
  induction list with
  | nil =>
      simp only [Dirichlet.Theorem.selectDenominatorMaximum] at selection
      cases selection
  | cons candidate remaining inductionHypothesis =>
      simp only [Dirichlet.Theorem.selectDenominatorMaximum] at selection
      cases recursive : Dirichlet.Theorem.selectDenominatorMaximum remaining with
      | none =>
          rw [recursive] at selection
          cases selection
          exact List.mem_cons_self
      | some recursiveSelected =>
          by_cases selectedLeCandidate :
              Best.Error.denominatorQuadrance recursiveSelected ≤
                Best.Error.denominatorQuadrance candidate
          · simp only [recursive, if_pos selectedLeCandidate] at selection
            cases selection
            exact List.mem_cons_self
          · simp only [recursive, if_neg selectedLeCandidate] at selection
            cases selection
            exact List.mem_cons_of_mem _ (inductionHypothesis recursive)

/-- Maximum-denominator selection returns no pair exactly when its input list is empty. -/
theorem selectDenominatorMaximum_eq_none_iff (list : List GaussianInt.Pair.Basic.ConvergentPair) :
    Dirichlet.Theorem.selectDenominatorMaximum list = none ↔ list = [] := by
  cases list with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons candidate remaining =>
      constructor
      · intro impossible
        simp only [Dirichlet.Theorem.selectDenominatorMaximum] at impossible
        cases recursive : Dirichlet.Theorem.selectDenominatorMaximum remaining with
        | none =>
            simp only [recursive] at impossible
            cases impossible
        | some selected =>
            by_cases selectedLeCandidate :
                Best.Error.denominatorQuadrance selected ≤ Best.Error.denominatorQuadrance candidate
            · simp only [recursive, if_pos selectedLeCandidate] at impossible
              cases impossible
            · simp only [recursive, if_neg selectedLeCandidate] at impossible
              cases impossible
      · intro impossible
        cases impossible

/-- The selected pair has denominator quadrance at least that of every input member. -/
theorem selectDenominatorMaximum_ge_of_mem
    {list : List GaussianInt.Pair.Basic.ConvergentPair} {selected candidate : GaussianInt.Pair.Basic.ConvergentPair}
    (selection : Dirichlet.Theorem.selectDenominatorMaximum list = some selected)
    (member : candidate ∈ list) :
    Best.Error.denominatorQuadrance candidate ≤ Best.Error.denominatorQuadrance selected := by
  induction list generalizing selected candidate with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      simp only [Dirichlet.Theorem.selectDenominatorMaximum] at selection
      cases recursive : Dirichlet.Theorem.selectDenominatorMaximum remaining with
      | none =>
          have remainingEmpty :=
            (Dirichlet.Theorem.selectDenominatorMaximum_eq_none_iff remaining).mp recursive
          subst remaining
          simp only [Dirichlet.Theorem.selectDenominatorMaximum] at selection
          have selectedIdentity : head = selected := Option.some.inj selection
          subst selected
          have member := Data.List.Membership.mem_singleton.mp member
          subst candidate
          exact le_rfl
      | some recursiveSelected =>
          by_cases recursiveLeHead :
              Best.Error.denominatorQuadrance recursiveSelected ≤
                Best.Error.denominatorQuadrance head
          · simp only [recursive, if_pos recursiveLeHead] at selection
            have selectedIdentity : head = selected := Option.some.inj selection
            subst selected
            rcases Data.List.Membership.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact le_rfl
            · exact (inductionHypothesis recursive remainingMember).trans
                recursiveLeHead
          · simp only [recursive, if_neg recursiveLeHead] at selection
            have selectedIdentity : recursiveSelected = selected :=
              Option.some.inj selection
            subst selected
            rcases Data.List.Membership.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact Nat.le_of_not_ge recursiveLeHead
            · exact inductionHypothesis recursive remainingMember

/-- Finite descent from a unit-denominator nearest pair produces a best pair
at denominator quadrance exactly one. -/
theorem exists_unitDenominatorBest (source : GaussianInt.Fraction) :
    ∃ pair : GaussianInt.Pair.Basic.ConvergentPair,
      Best.Basic.IsBest source.value pair ∧ Best.Error.denominatorQuadrance pair = 1 := by
  let candidate := Best.Basic.nearestPair source.value 1
  have candidateNonzero : candidate.denominator ≠ 0 := by
    change (1 : GaussianInt) ≠ 0
    decide
  have candidateHeightEq : Best.Error.denominatorQuadrance candidate = 1 := by
    unfold Best.Error.denominatorQuadrance
    change GaussianInt.normNat
      (1 : GaussianInt) = 1
    decide
  have candidateHeight : Best.Error.denominatorQuadrance candidate ≤
      GaussianInt.normNat source.denominator := by
    rw [candidateHeightEq]
    have sourcePositive :=
      GaussianInt.normNat_pos
        source.denominatorNonzero
    exact sourcePositive
  have candidateSmall : Best.Error.errorQuadrance source.value candidate ≤ 1 / 2 := by
    dsimp only [candidate]
    rw [Best.Error.errorQuadrance, Best.Basic.nearestPair_error]
    exact GaussianInt.Nearest.remainder_normSq_le_half _
  obtain ⟨pair, best, heightLe, _⟩ :=
    Best.Search.exists_best_below_of_small candidateNonzero candidateHeight candidateSmall
  have heightPositive : 0 < Best.Error.denominatorQuadrance pair := by
    exact GaussianInt.normNat_pos best.1
  refine ⟨pair, best, ?_⟩
  rw [candidateHeightEq] at heightLe
  exact Nat.le_antisymm heightLe (Nat.succ_le_of_lt heightPositive)

/-- Finite descent from the displayed exact pair produces a terminal best
pair of exactly zero error. -/
theorem exists_zeroErrorBest (source : GaussianInt.Fraction) :
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

/-- Global rational-cut Dirichlet theorem for every displayed rational source
and every natural squared request strictly above one.  The returned pair has
nonzero denominator below the request and satisfies the root-free universal
scaled-error bound. -/
theorem globalDirichletRequest
    (gap : Fraction.Rational)
    (gapCertificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (source : GaussianInt.Fraction) (request : Nat) (requestAboveOne : 1 < request) :
    ∃ pair : GaussianInt.Pair.Basic.ConvergentPair,
      pair.denominator ≠ 0 ∧
        Best.Error.denominatorQuadrance pair < request ∧
        gap * (request : Fraction.Rational) * Best.Error.errorQuadrance source.value pair ≤ 1 := by
  obtain ⟨unitPair, unitBest, unitHeight⟩ :=
    Dirichlet.Theorem.exists_unitDenominatorBest source
  let list := Dirichlet.Theorem.bestBelowRequest source request
  have unitMember : unitPair ∈ list := by
    apply (Dirichlet.Theorem.mem_bestBelowRequest_iff source request unitPair).mpr
    exact ⟨unitBest, unitHeight.trans_lt requestAboveOne⟩
  cases selection : Dirichlet.Theorem.selectDenominatorMaximum list with
  | none =>
      have listEmpty := (Dirichlet.Theorem.selectDenominatorMaximum_eq_none_iff list).mp selection
      rw [listEmpty] at unitMember
      exact (List.not_mem_nil unitMember).elim
  | some selected =>
      have selectedMember := Dirichlet.Theorem.selectDenominatorMaximum_mem selection
      have selectedData :=
        (Dirichlet.Theorem.mem_bestBelowRequest_iff source request selected).mp selectedMember
      obtain ⟨terminal, terminalBest, terminalZero⟩ :=
        Dirichlet.Theorem.exists_zeroErrorBest source
      by_cases terminalBelow : Best.Error.denominatorQuadrance terminal < request
      · have terminalMember : terminal ∈ list :=
          (Dirichlet.Theorem.mem_bestBelowRequest_iff source request terminal).mpr
            ⟨terminalBest, terminalBelow⟩
        have terminalLeSelected :=
          Dirichlet.Theorem.selectDenominatorMaximum_ge_of_mem selection terminalMember
        have selectedErrorLeZero := selectedData.1.2.2 terminal terminalBest.1
          terminalLeSelected
        rw [terminalZero] at selectedErrorLeZero
        have selectedErrorNonnegative :
            0 ≤ Best.Error.errorQuadrance source.value selected := by
          unfold Best.Error.errorQuadrance
          exact Gaussian.Norm.Basic.normSq_nonneg _
        have selectedErrorZero : Best.Error.errorQuadrance source.value selected = 0 :=
          le_antisymm selectedErrorLeZero selectedErrorNonnegative
        refine ⟨selected, selectedData.1.1, selectedData.2, ?_⟩
        rw [selectedErrorZero]
        calc
          gap * (request : Fraction.Rational) * 0 = 0 := by ring1
          _ ≤ 1 := by decide
      · have requestLeTerminal : request ≤ Best.Error.denominatorQuadrance terminal :=
          Nat.le_of_not_gt terminalBelow
        have selectedLtTerminal :
            Best.Error.denominatorQuadrance selected < Best.Error.denominatorQuadrance terminal :=
          selectedData.2.trans_le requestLeTerminal
        obtain ⟨next, consecutive, _nextLeTerminal⟩ :=
          Best.Successor.Local.exists_consecutiveBest_below selectedData.1
            terminalBest selectedLtTerminal
        have requestLeNext : request ≤ Best.Error.denominatorQuadrance next := by
          apply Nat.le_of_not_gt
          intro nextBelow
          have nextMember : next ∈ list :=
            (Dirichlet.Theorem.mem_bestBelowRequest_iff source request next).mpr
              ⟨consecutive.2.1, nextBelow⟩
          have nextLeSelected :=
            Dirichlet.Theorem.selectDenominatorMaximum_ge_of_mem selection nextMember
          exact (Nat.not_le_of_gt consecutive.2.2.1) nextLeSelected
        have requestWitness := Dirichlet.Window.SourceBound.AreConsecutiveBest.lower_witnesses_dirichletWindow
          consecutive
          request selectedData.2 requestLeNext
        have windowBound :=
          Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
            gap gapCertificate consecutive
        have gapNonnegative : (0 : Fraction.Rational) ≤ gap :=
          (show (0 : Fraction.Rational) ≤ 3 / 4 by decide).trans gapCertificate.1
        have scaledRequest :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            requestWitness.2.2 gapNonnegative
        refine ⟨selected, selectedData.1.1, selectedData.2, ?_⟩
        calc
          gap * (request : Fraction.Rational) *
                Best.Error.errorQuadrance source.value selected =
              gap * ((request : Fraction.Rational) *
                Best.Error.errorQuadrance source.value selected) := by ring1
          _ ≤ gap * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value selected next :=
            scaledRequest
          _ ≤ 1 := windowBound

/-- Two-sided rational-cut analogue of Chevallier's Dirichlet theorem.  The
nonnegative side gives a global approximation for every displayed rational
source and natural squared request.  Every threshold on the strictly sharper
side has a positive robust source box and probability-one stopped-successor
returns to arbitrary finite runs of counterexample windows. -/
theorem chevallierBoundary
    (admissibleGap : Fraction.Rational)
    (admissible :
      Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold admissibleGap)
    {sharperGap : Fraction.Rational}
    (sharper :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold sharperGap)
    (requestedScale count : Nat) :
    (∀ (source : GaussianInt.Fraction) (request : Nat), 1 < request →
      ∃ pair : GaussianInt.Pair.Basic.ConvergentPair,
        pair.denominator ≠ 0 ∧
          Best.Error.denominatorQuadrance pair < request ∧
          admissibleGap * (request : Fraction.Rational) *
              Best.Error.errorQuadrance source.value pair ≤ 1) ∧
      (Dirichlet.Critical.Robust.Run.robustRunBox
          sharper requestedScale count).Proper ∧
      0 < Geometry.Rational.Box.Content.boxContent
        (Dirichlet.Critical.Robust.Run.robustRunBox
          sharper requestedScale count) ∧
      ∀ (source : GaussianInt.Fraction),
        (inside : (Dirichlet.Critical.Robust.Run.robustRunBox
          sharper requestedScale count).Contains source.value) →
        ∀ (offset : Fin count)
          (initial : Measure.Distribution
            (Best.Successor.Dynamics.State source))
          (burnIn blockCount : Nat),
          0 < blockCount →
          Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorReturnProbability
            sharper requestedScale count source inside offset initial burnIn
              blockCount = 1 := by
  refine ⟨fun source request requestAboveOne =>
      Dirichlet.Theorem.globalDirichletRequest admissibleGap admissible source request
        requestAboveOne,
    Dirichlet.Sharpness.StoppedSuccessor.chevallierAnalogue
      sharper requestedScale count⟩

end Purelib.NumberTheory.Approximation.Dirichlet.Theorem

end
