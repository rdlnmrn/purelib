import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.IndexOneWindow
import RFAP.Approximation.LocalSuccessor
import RFAP.Approximation.RobustSuccessorSharpness

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

namespace RFAP.FiniteDirichletGlobal

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation

/-- Best pairs whose denominator quadrance is strictly below the displayed
request. -/
def bestBelowRequest (source : Fraction) (request : Nat) : List Pair :=
  (allBest source).filter fun pair =>
    decide (denominatorQuadrance pair < request)

theorem mem_bestBelowRequest_iff (source : Fraction) (request : Nat)
    (pair : Pair) :
    pair ∈ bestBelowRequest source request ↔
      IsBest source.value pair ∧ denominatorQuadrance pair < request := by
  simp only [bestBelowRequest, List.mem_filter, decide_eq_true_eq,
    mem_allBest_iff_isBest]

/-- Select a pair of greatest denominator quadrance from a displayed finite
list.  Ties retain the earlier record. -/
def selectDenominatorMaximum : List Pair → Option Pair
  | [] => none
  | candidate :: remaining =>
      match selectDenominatorMaximum remaining with
      | none => some candidate
      | some selected =>
          if denominatorQuadrance selected ≤ denominatorQuadrance candidate then
            some candidate
          else
            some selected

theorem selectDenominatorMaximum_mem
    {list : List Pair} {selected : Pair}
    (selection : selectDenominatorMaximum list = some selected) :
    selected ∈ list := by
  induction list with
  | nil =>
      simp only [selectDenominatorMaximum] at selection
      cases selection
  | cons candidate remaining inductionHypothesis =>
      simp only [selectDenominatorMaximum] at selection
      cases recursive : selectDenominatorMaximum remaining with
      | none =>
          rw [recursive] at selection
          cases selection
          exact List.mem_cons_self
      | some recursiveSelected =>
          by_cases selectedLeCandidate :
              denominatorQuadrance recursiveSelected ≤
                denominatorQuadrance candidate
          · simp only [recursive, if_pos selectedLeCandidate] at selection
            cases selection
            exact List.mem_cons_self
          · simp only [recursive, if_neg selectedLeCandidate] at selection
            cases selection
            exact List.mem_cons_of_mem _ (inductionHypothesis recursive)

theorem selectDenominatorMaximum_eq_none_iff (list : List Pair) :
    selectDenominatorMaximum list = none ↔ list = [] := by
  cases list with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons candidate remaining =>
      constructor
      · intro impossible
        simp only [selectDenominatorMaximum] at impossible
        cases recursive : selectDenominatorMaximum remaining with
        | none =>
            simp only [recursive] at impossible
            cases impossible
        | some selected =>
            by_cases selectedLeCandidate :
                denominatorQuadrance selected ≤ denominatorQuadrance candidate
            · simp only [recursive, if_pos selectedLeCandidate] at impossible
              cases impossible
            · simp only [recursive, if_neg selectedLeCandidate] at impossible
              cases impossible
      · intro impossible
        cases impossible

theorem selectDenominatorMaximum_ge_of_mem
    {list : List Pair} {selected candidate : Pair}
    (selection : selectDenominatorMaximum list = some selected)
    (member : candidate ∈ list) :
    denominatorQuadrance candidate ≤ denominatorQuadrance selected := by
  induction list generalizing selected candidate with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      simp only [selectDenominatorMaximum] at selection
      cases recursive : selectDenominatorMaximum remaining with
      | none =>
          have remainingEmpty :=
            (selectDenominatorMaximum_eq_none_iff remaining).mp recursive
          subst remaining
          simp only [selectDenominatorMaximum] at selection
          have selectedIdentity : head = selected := Option.some.inj selection
          subst selected
          simp only [List.mem_singleton] at member
          subst candidate
          exact le_rfl
      | some recursiveSelected =>
          by_cases recursiveLeHead :
              denominatorQuadrance recursiveSelected ≤
                denominatorQuadrance head
          · simp only [recursive, if_pos recursiveLeHead] at selection
            have selectedIdentity : head = selected := Option.some.inj selection
            subst selected
            rcases List.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact le_rfl
            · exact (inductionHypothesis recursive remainingMember).trans
                recursiveLeHead
          · simp only [recursive, if_neg recursiveLeHead] at selection
            have selectedIdentity : recursiveSelected = selected :=
              Option.some.inj selection
            subst selected
            rcases List.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact Nat.le_of_not_ge recursiveLeHead
            · exact inductionHypothesis recursive remainingMember

/-- Finite descent from a unit-denominator nearest pair produces a best pair
at denominator quadrance exactly one. -/
theorem exists_unitDenominatorBest (source : Fraction) :
    ∃ pair : Pair,
      IsBest source.value pair ∧ denominatorQuadrance pair = 1 := by
  let candidate := nearestPair source.value 1
  have candidateNonzero : candidate.denominator ≠ 0 := by
    change (1 : RFAP.ConstructiveGaussianHeight.GaussianInt) ≠ 0
    decide
  have candidateHeightEq : denominatorQuadrance candidate = 1 := by
    unfold denominatorQuadrance
    change RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
      (1 : RFAP.ConstructiveGaussianHeight.GaussianInt) = 1
    decide
  have candidateHeight : denominatorQuadrance candidate ≤
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat source.denominator := by
    rw [candidateHeightEq]
    have sourcePositive :=
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos
        source.denominatorNonzero
    exact sourcePositive
  have candidateSmall : errorQuadrance source.value candidate ≤ 1 / 2 := by
    dsimp only [candidate]
    rw [errorQuadrance, nearestPair_error]
    exact RFAP.HurwitzNearest.remainder_normSq_le_half _
  obtain ⟨pair, best, heightLe, _⟩ :=
    exists_best_below_of_small candidateNonzero candidateHeight candidateSmall
  have heightPositive : 0 < denominatorQuadrance pair := by
    exact RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos best.1
  refine ⟨pair, best, ?_⟩
  rw [candidateHeightEq] at heightLe
  exact Nat.le_antisymm heightLe (Nat.succ_le_of_lt heightPositive)

/-- Finite descent from the displayed exact pair produces a terminal best
pair of exactly zero error. -/
theorem exists_zeroErrorBest (source : Fraction) :
    ∃ pair : Pair,
      IsBest source.value pair ∧ errorQuadrance source.value pair = 0 := by
  have exactSmall : errorQuadrance source.value (exactPair source) ≤ 1 / 2 := by
    rw [errorQuadrance, exactPair_error,
      RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
    decide
  obtain ⟨pair, best, _, errorLe⟩ :=
    exists_best_below_of_small source.denominatorNonzero le_rfl exactSmall
  have exactZero : errorQuadrance source.value (exactPair source) = 0 := by
    rw [errorQuadrance, exactPair_error,
      RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
  rw [exactZero] at errorLe
  have nonnegative : 0 ≤ errorQuadrance source.value pair := by
    unfold errorQuadrance
    exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  exact ⟨pair, best, le_antisymm errorLe nonnegative⟩

/-- Global rational-cut Dirichlet theorem for every displayed rational source
and every natural squared request strictly above one.  The returned pair has
nonzero denominator below the request and satisfies the root-free universal
scaled-error bound. -/
theorem globalDirichletRequest
    (gap : Coordinate)
    (gapCertificate : RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold gap)
    (source : Fraction) (request : Nat) (requestAboveOne : 1 < request) :
    ∃ pair : Pair,
      pair.denominator ≠ 0 ∧
        denominatorQuadrance pair < request ∧
        gap * (request : Coordinate) * errorQuadrance source.value pair ≤ 1 := by
  obtain ⟨unitPair, unitBest, unitHeight⟩ :=
    exists_unitDenominatorBest source
  let list := bestBelowRequest source request
  have unitMember : unitPair ∈ list := by
    apply (mem_bestBelowRequest_iff source request unitPair).mpr
    exact ⟨unitBest, unitHeight.trans_lt requestAboveOne⟩
  cases selection : selectDenominatorMaximum list with
  | none =>
      have listEmpty := (selectDenominatorMaximum_eq_none_iff list).mp selection
      rw [listEmpty] at unitMember
      exact (List.not_mem_nil unitMember).elim
  | some selected =>
      have selectedMember := selectDenominatorMaximum_mem selection
      have selectedData :=
        (mem_bestBelowRequest_iff source request selected).mp selectedMember
      obtain ⟨terminal, terminalBest, terminalZero⟩ :=
        exists_zeroErrorBest source
      by_cases terminalBelow : denominatorQuadrance terminal < request
      · have terminalMember : terminal ∈ list :=
          (mem_bestBelowRequest_iff source request terminal).mpr
            ⟨terminalBest, terminalBelow⟩
        have terminalLeSelected :=
          selectDenominatorMaximum_ge_of_mem selection terminalMember
        have selectedErrorLeZero := selectedData.1.2.2 terminal terminalBest.1
          terminalLeSelected
        rw [terminalZero] at selectedErrorLeZero
        have selectedErrorNonnegative :
            0 ≤ errorQuadrance source.value selected := by
          unfold errorQuadrance
          exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
        have selectedErrorZero : errorQuadrance source.value selected = 0 :=
          le_antisymm selectedErrorLeZero selectedErrorNonnegative
        refine ⟨selected, selectedData.1.1, selectedData.2, ?_⟩
        rw [selectedErrorZero]
        calc
          gap * (request : Coordinate) * 0 = 0 := by ring1
          _ ≤ 1 := by decide
      · have requestLeTerminal : request ≤ denominatorQuadrance terminal :=
          Nat.le_of_not_gt terminalBelow
        have selectedLtTerminal :
            denominatorQuadrance selected < denominatorQuadrance terminal :=
          selectedData.2.trans_le requestLeTerminal
        obtain ⟨next, consecutive, _nextLeTerminal⟩ :=
          RFAP.LocalSuccessor.exists_consecutiveBest_below selectedData.1
            terminalBest selectedLtTerminal
        have requestLeNext : request ≤ denominatorQuadrance next := by
          apply Nat.le_of_not_gt
          intro nextBelow
          have nextMember : next ∈ list :=
            (mem_bestBelowRequest_iff source request next).mpr
              ⟨consecutive.2.1, nextBelow⟩
          have nextLeSelected :=
            selectDenominatorMaximum_ge_of_mem selection nextMember
          exact (Nat.not_le_of_gt consecutive.2.2.1) nextLeSelected
        have requestWitness := consecutive.lower_witnesses_dirichletWindow
          request selectedData.2 requestLeNext
        have windowBound :=
          RFAP.IndexOneWindow.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
            gap gapCertificate consecutive
        have gapNonnegative : (0 : Coordinate) ≤ gap :=
          (show (0 : Coordinate) ≤ 3 / 4 by decide).trans gapCertificate.1
        have scaledRequest :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            requestWitness.2.2 gapNonnegative
        refine ⟨selected, selectedData.1.1, selectedData.2, ?_⟩
        calc
          gap * (request : Coordinate) *
                errorQuadrance source.value selected =
              gap * ((request : Coordinate) *
                errorQuadrance source.value selected) := by ring1
          _ ≤ gap * dirichletWindowQuadrance source.value selected next :=
            scaledRequest
          _ ≤ 1 := windowBound

/-- Two-sided rational-cut analogue of Chevallier's Dirichlet theorem.  The
nonnegative side gives a global approximation for every displayed rational
source and natural squared request.  Every threshold on the strictly sharper
side has a positive robust source box and probability-one stopped-successor
returns to arbitrary finite runs of counterexample windows. -/
theorem finiteChevallierBoundary
    (admissibleGap : Coordinate)
    (admissible :
      RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold admissibleGap)
    {sharperGap : Coordinate}
    (sharper :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold sharperGap)
    (requestedScale count : Nat) :
    (∀ (source : Fraction) (request : Nat), 1 < request →
      ∃ pair : Pair,
        pair.denominator ≠ 0 ∧
          denominatorQuadrance pair < request ∧
          admissibleGap * (request : Coordinate) *
              errorQuadrance source.value pair ≤ 1) ∧
      (RFAP.RobustCriticalRun.robustRunBox
          sharper requestedScale count).Proper ∧
      0 < RFAP.FiniteMeasure.boxContent
        (RFAP.RobustCriticalRun.robustRunBox
          sharper requestedScale count) ∧
      ∀ (source : Fraction),
        (inside : (RFAP.RobustCriticalRun.robustRunBox
          sharper requestedScale count).Contains source.value) →
        ∀ (offset : Fin count)
          (initial : _root_.FiniteMeasure.Distribution
            (RFAP.SuccessorDynamics.State source))
          (burnIn blockCount : Nat),
          0 < blockCount →
          RFAP.RobustSuccessorSharpness.robustSuccessorReturnProbability
            sharper requestedScale count source inside offset initial burnIn
              blockCount = 1 := by
  refine ⟨fun source request requestAboveOne =>
      globalDirichletRequest admissibleGap admissible source request
        requestAboveOne,
    RFAP.RobustSuccessorSharpness.finiteChevallierAnalogue
      sharper requestedScale count⟩

end RFAP.FiniteDirichletGlobal
