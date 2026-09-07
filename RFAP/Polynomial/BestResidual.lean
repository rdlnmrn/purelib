import mathlib.Data.ConstructiveList
import RFAP.Polynomial.DenominatorHeight
import mathlib.RFAP.ConstructiveRationalRootCandidates

/-!
# Exact finite best-residual search

For fixed numerator and denominator bounds there are only finitely many
displayed common-denominator Gaussian fractions.  This module enumerates that
finite rectangle and selects a sample of least polynomial residual by direct
comparison.
-/

namespace RFAP.BestResidual

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Fraction := RFAP.ConstructiveGaussianHeight.Fraction

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

/-- All common-denominator Gaussian fractions with positive denominator at
most `denominatorBound` and coordinate numerator magnitudes at most
`numeratorBound`.  Duplication of zero numerators is harmless. -/
def candidates (numeratorBound denominatorBound : Nat) : List Fraction :=
  (List.range denominatorBound).flatMap fun denominatorIndex =>
    (RFAP.ConstructiveRationalRootCandidates.signedNumerators
      numeratorBound).flatMap fun real =>
      (RFAP.ConstructiveRationalRootCandidates.signedNumerators
        numeratorBound).map fun imaginary =>
        RFAP.ConstructiveGaussianHeight.Fraction.grid real imaginary
          (denominatorIndex + 1) (Nat.zero_lt_succ denominatorIndex)

theorem mem_candidates {fraction : Fraction}
    {numeratorBound denominatorBound : Nat}
    (realBound : fraction.numerator.re.natAbs ≤ numeratorBound)
    (imaginaryBound : fraction.numerator.im.natAbs ≤ numeratorBound)
    (denominatorBounded : fraction.denominator ≤ denominatorBound) :
    fraction ∈ candidates numeratorBound denominatorBound := by
  let denominatorIndex := fraction.denominator - 1
  have denominatorIdentity : denominatorIndex + 1 = fraction.denominator := by
    dsimp only [denominatorIndex]
    exact Nat.sub_add_cancel
      (Nat.succ_le_iff.mpr fraction.denominatorPositive)
  have indexBound : denominatorIndex < denominatorBound := by
    calc
      denominatorIndex < denominatorIndex + 1 := Nat.lt_succ_self _
      _ = fraction.denominator := denominatorIdentity
      _ ≤ denominatorBound := denominatorBounded
  rw [candidates]
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨denominatorIndex, QuotientFreeList.mem_range.mpr indexBound, ?_⟩
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨fraction.numerator.re,
    RFAP.ConstructiveRationalRootCandidates.mem_signedNumerators realBound, ?_⟩
  apply QuotientFreeList.mem_map.mpr
  refine ⟨fraction.numerator.im,
    RFAP.ConstructiveRationalRootCandidates.mem_signedNumerators imaginaryBound,
    ?_⟩
  apply RFAP.ConstructiveGaussianHeight.Fraction.ext
  · apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;> rfl
  · exact denominatorIdentity

/-- Residual quadrance used by the exact comparison. -/
def score (p : GaussianPolynomial) (fraction : Fraction) : Coordinate :=
  normSq (p.eval fraction.value)

/-- Return a least-scoring element of a finite list, or `none` for the empty
list.  Ties retain the earlier displayed candidate. -/
def selectMinimum (p : GaussianPolynomial) : List Fraction → Option Fraction
  | [] => none
  | candidate :: remaining =>
      match selectMinimum p remaining with
      | none => some candidate
      | some selected =>
          if score p candidate ≤ score p selected then some candidate
          else some selected

theorem selectMinimum_mem {p : GaussianPolynomial} {list : List Fraction}
    {selected : Fraction} (selection : selectMinimum p list = some selected) :
    selected ∈ list := by
  induction list with
  | nil => simp [selectMinimum] at selection
  | cons candidate remaining inductionHypothesis =>
      simp only [selectMinimum] at selection
      cases recursive : selectMinimum p remaining with
      | none =>
          rw [recursive] at selection
          cases selection
          exact List.mem_cons_self
      | some recursiveSelected =>
          by_cases candidateLe : score p candidate ≤ score p recursiveSelected
          · simp only [recursive, if_pos candidateLe] at selection
            cases selection
            exact List.mem_cons_self
          · simp only [recursive, if_neg candidateLe] at selection
            cases selection
            exact List.mem_cons_of_mem _ (inductionHypothesis recursive)

theorem selectMinimum_eq_none_iff
    (p : GaussianPolynomial) (list : List Fraction) :
    selectMinimum p list = none ↔ list = [] := by
  cases list with
  | nil =>
      constructor <;> intro assumption
      · rfl
      · rfl
  | cons candidate remaining =>
      constructor
      · intro impossible
        simp only [selectMinimum] at impossible
        cases recursive : selectMinimum p remaining with
        | none =>
            simp only [recursive] at impossible
            cases impossible
        | some selected =>
            by_cases candidateLe : score p candidate ≤ score p selected
            · simp only [recursive, if_pos candidateLe] at impossible
              cases impossible
            · simp only [recursive, if_neg candidateLe] at impossible
              cases impossible
      · intro impossible
        cases impossible

theorem selectMinimum_le_of_mem
    {p : GaussianPolynomial} {list : List Fraction} {selected candidate : Fraction}
    (selection : selectMinimum p list = some selected)
    (member : candidate ∈ list) :
    score p selected ≤ score p candidate := by
  induction list generalizing selected candidate with
  | nil => simp only [List.not_mem_nil] at member
  | cons head remaining inductionHypothesis =>
      simp only [selectMinimum] at selection
      cases recursive : selectMinimum p remaining with
      | none =>
          have remainingEmpty :=
            (selectMinimum_eq_none_iff p remaining).mp recursive
          subst remaining
          simp only [selectMinimum] at selection
          have selectedIdentity : head = selected := Option.some.inj selection
          subst selected
          simp only [List.mem_singleton] at member
          subst candidate
          exact le_rfl
      | some recursiveSelected =>
          by_cases headLe : score p head ≤ score p recursiveSelected
          · simp only [recursive, if_pos headLe] at selection
            have selectedIdentity : head = selected := Option.some.inj selection
            subst selected
            rcases List.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact le_rfl
            · exact headLe.trans
                (inductionHypothesis recursive remainingMember)
          · simp only [recursive, if_neg headLe] at selection
            have selectedIdentity : recursiveSelected = selected :=
              Option.some.inj selection
            subst selected
            rcases List.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact le_of_not_ge headLe
            · exact inductionHypothesis recursive remainingMember

/-- Exact best residual in the displayed finite rectangle. -/
def best (p : GaussianPolynomial) (numeratorBound denominatorBound : Nat) :
    Option Fraction :=
  selectMinimum p (candidates numeratorBound denominatorBound)

theorem best_exists (p : GaussianPolynomial) (numeratorBound : Nat)
    {denominatorBound : Nat} (positive : 0 < denominatorBound) :
    ∃ selected, best p numeratorBound denominatorBound = some selected := by
  let zeroFraction := RFAP.ConstructiveGaussianHeight.Fraction.grid 0 0 1
    (by decide)
  have zeroMember : zeroFraction ∈ candidates numeratorBound denominatorBound := by
    apply mem_candidates
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.succ_le_iff.mpr positive
  cases selection : selectMinimum p
      (candidates numeratorBound denominatorBound) with
  | none =>
      have empty := (selectMinimum_eq_none_iff p
        (candidates numeratorBound denominatorBound)).mp selection
      rw [empty] at zeroMember
      exact (List.not_mem_nil zeroMember).elim
  | some selected =>
      refine ⟨selected, ?_⟩
      simpa only [best] using selection

theorem best_is_optimal
    {p : GaussianPolynomial} {numeratorBound denominatorBound : Nat}
    {selected candidate : Fraction}
    (selection : best p numeratorBound denominatorBound = some selected)
    (realBound : candidate.numerator.re.natAbs ≤ numeratorBound)
    (imaginaryBound : candidate.numerator.im.natAbs ≤ numeratorBound)
    (denominatorBounded : candidate.denominator ≤ denominatorBound) :
    score p selected ≤ score p candidate := by
  exact selectMinimum_le_of_mem selection
    (mem_candidates realBound imaginaryBound denominatorBounded)

end RFAP.BestResidual
