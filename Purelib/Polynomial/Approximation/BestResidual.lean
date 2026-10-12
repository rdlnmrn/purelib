module
import Purelib.Data.Gaussian.Fraction.NaturalDenominator
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator.Enumeration
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic

open Purelib.Data.Gaussian.Basic.Canonical.Fraction (NaturalDenominator)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Exact finite best-residual search

For fixed numerator and denominator bounds there are only finitely many
displayed common-denominator Gaussian fractions.  This module enumerates that
finite rectangle and selects a sample of least polynomial residual by direct
comparison.
-/

namespace Purelib.Polynomial.Approximation.BestResidual

/-- Residual quadrance used by the exact comparison. -/
def score (p :
  CoefficientPolynomial) (fraction :
  NaturalDenominator) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (p.eval fraction.value)

/-- Return a least-scoring element of a finite list, or `none` for the empty
list.  Ties retain the earlier displayed candidate. -/
def selectMinimum (p :
  CoefficientPolynomial) : List
  NaturalDenominator → Option NaturalDenominator
  | [] => none
  | candidate :: remaining =>
      match selectMinimum p remaining with
      | none => some candidate
      | some selected =>
          if score p candidate ≤ score p selected then some
            candidate
          else some selected

/-- A successful minimum scan returns an element of its original finite list. -/
theorem selectMinimum_mem {p :
  CoefficientPolynomial}
  {list : List NaturalDenominator}
    {selected : NaturalDenominator} (selection :
      selectMinimum p list = some selected) :
    selected ∈ list := by
  induction list with
  | nil =>
      change (none : Option NaturalDenominator) = some selected at selection
      cases selection
  | cons candidate remaining inductionHypothesis =>
      simp only [selectMinimum] at selection
      cases recursive : selectMinimum p remaining with
      | none =>
          rw [recursive] at selection
          cases selection
          exact List.mem_cons_self
      | some recursiveSelected =>
          by_cases candidateLe : score p candidate ≤ score p
            recursiveSelected
          · simp only [recursive, if_pos candidateLe] at selection
            cases selection
            exact List.mem_cons_self
          · simp only [recursive, if_neg candidateLe] at selection
            cases selection
            exact List.mem_cons_of_mem _ (inductionHypothesis recursive)

/-- The minimum scan returns none exactly when the candidate list is empty. -/
theorem selectMinimum_eq_none_iff
    (p : CoefficientPolynomial) (list : List
      NaturalDenominator) :
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
            by_cases candidateLe : score p candidate ≤ score p
              selected
            · simp only [recursive, if_pos candidateLe] at impossible
              cases impossible
            · simp only [recursive, if_neg candidateLe] at impossible
              cases impossible
      · intro impossible
        cases impossible

/-- The selected residual score is no larger than any listed candidate's score. -/
theorem selectMinimum_le_of_mem
    {p : CoefficientPolynomial} {list : List
      NaturalDenominator}
      {selected candidate : NaturalDenominator}
    (selection : selectMinimum p list = some selected)
    (member : candidate ∈ list) :
    score p selected ≤ score p candidate := by
  induction list generalizing selected candidate with
  | nil => nomatch member
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
          have candidateIdentity : candidate = head := by
            cases member with
            | head => rfl
            | tail _ impossible => nomatch impossible
          subst candidate
          exact le_rfl
      | some recursiveSelected =>
          by_cases headLe : score p head ≤ score p
            recursiveSelected
          · simp only [recursive, if_pos headLe] at selection
            have selectedIdentity : head = selected := Option.some.inj selection
            subst selected
            cases member with
            | head => exact le_rfl
            | tail _ remainingMember =>
                exact headLe.trans (inductionHypothesis recursive remainingMember)
          · simp only [recursive, if_neg headLe] at selection
            have selectedIdentity : recursiveSelected = selected :=
              Option.some.inj selection
            subst selected
            cases member with
            | head => exact le_of_not_ge headLe
            | tail _ remainingMember =>
                exact inductionHypothesis recursive remainingMember

/-- Exact best residual in the displayed finite rectangle. -/
def best (p :
  CoefficientPolynomial) (numeratorBound
  denominatorBound : Nat) :
    Option NaturalDenominator :=
  selectMinimum p (Gaussian.Fraction.NaturalDenominator.Enumeration.candidates numeratorBound
    denominatorBound)

/-- A positive denominator bound makes the finite search nonempty and yields a selected sample. -/
theorem best_exists (p :
  CoefficientPolynomial)
  (numeratorBound : Nat)
    {denominatorBound : Nat} (positive : 0 < denominatorBound) :
    ∃ selected, best p numeratorBound denominatorBound = some selected := by
  let zeroFraction := NaturalDenominator.grid 0 0 1
    (by decide)
  have zeroMember : zeroFraction ∈ Gaussian.Fraction.NaturalDenominator.Enumeration.candidates numeratorBound
    denominatorBound := by
    apply Gaussian.Fraction.NaturalDenominator.Enumeration.mem_candidates
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.succ_le_iff.mpr positive
  cases selection : selectMinimum p
      (Gaussian.Fraction.NaturalDenominator.Enumeration.candidates numeratorBound denominatorBound) with
  | none =>
      have empty := (selectMinimum_eq_none_iff p
        (Gaussian.Fraction.NaturalDenominator.Enumeration.candidates numeratorBound denominatorBound)).mp selection
      rw [empty] at zeroMember
      exact (List.not_mem_nil zeroMember).elim
  | some selected =>
      refine ⟨selected, ?_⟩
      simpa only [best] using selection

/-- The selected sample minimizes residual quadrance among all fractions within the supplied numerator and denominator
bounds. -/
theorem best_is_optimal
    {p : CoefficientPolynomial} {numeratorBound denominatorBound : Nat}
    {selected candidate : NaturalDenominator}
    (selection : best p numeratorBound denominatorBound = some selected)
    (realBound : candidate.numerator.re.natAbs ≤ numeratorBound)
    (imaginaryBound : candidate.numerator.im.natAbs ≤ numeratorBound)
    (denominatorBounded : candidate.denominator ≤ denominatorBound) :
    score p selected ≤ score p candidate := by
  exact selectMinimum_le_of_mem selection
    (Gaussian.Fraction.NaturalDenominator.Enumeration.mem_candidates realBound imaginaryBound denominatorBounded)

end Purelib.Polynomial.Approximation.BestResidual

end
