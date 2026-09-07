import FTA.CCLBranchEventOwner
import FTA.CCLFormulaStability

/-!
# Closed limits of finite parser formulas

Strict sign atoms may converge to equality along a shrinking rational root
track.  This file gives the purely finite logical operation used at such a
limit: positive and negative atoms become weak, while a nonzero atom imposes
no closed condition.  No topology or real-number completion is involved.
-/

namespace FTA
namespace CCLFormulaClosure

open CCL CCL.GaussianRat
open FTA.CCLBranchEventOwner
open FTA.CCLFormulaStability
open FTA.CCLGeometry
open FTA.CCLParserGeometry

abbrev QI := CCL.GaussianRat

/-- Closed weakening of one exact rational sign test. -/
def closedSignTest : SignTest → Option SignTest
  | .negative => some .nonpositive
  | .nonpositive => some .nonpositive
  | .zero => some .zero
  | .nonzero => none
  | .nonnegative => some .nonnegative
  | .positive => some .nonnegative

/-- Replace every atom by its closed weakening; a nonzero test closes to
`True`. -/
def closedFormula : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom atom =>
      match closedSignTest atom.sign with
      | none => .truth
      | some sign => .atom ⟨atom.form, sign⟩
  | .and left right => .and (closedFormula left) (closedFormula right)
  | .or left right => .or (closedFormula left) (closedFormula right)

/-- A strict rational witness transfers to the closed formula whenever each
classified value is either zero or has the witness's strict sign. -/
theorem closedFormula_eval_true_of_holds_of_zero_or_mul_pos
    (formula : Formula) (point : QI) (value : HermitianForm → ℚ)
    (holds : formula.Holds point)
    (classified : ∀ form ∈ formulaForms formula,
      value form = 0 ∨ 0 < value form * form.eval point) :
    formulaEvalWith (closedFormula formula) value = true := by
  induction formula with
  | truth => rfl
  | falsity => exact holds.elim
  | atom atom =>
      rcases atom with ⟨form, sign⟩
      change sign.Holds (form.eval point) at holds
      have relation := classified form (by simp [formulaForms])
      rcases relation with zero | sameSign
      · cases sign <;>
          simp_all [closedFormula, closedSignTest, formulaEvalWith,
            SignTest.Holds]
      · have sameSign' : 0 < form.eval point * value form := by
          rw [_root_.mul_comm]
          exact sameSign
        have transferred :=
          (SignTest.holds_iff_of_mul_pos sign sameSign').1 holds
        cases sign <;>
          simp_all [closedFormula, closedSignTest, formulaEvalWith,
            SignTest.Holds] <;> linarith
  | and left right leftIH rightIH =>
      have leftClassified : ∀ form ∈ formulaForms left,
          value form = 0 ∨ 0 < value form * form.eval point := by
        intro form member
        exact classified form (List.mem_append_left _ member)
      have rightClassified : ∀ form ∈ formulaForms right,
          value form = 0 ∨ 0 < value form * form.eval point := by
        intro form member
        exact classified form (List.mem_append_right _ member)
      simpa [closedFormula, formulaEvalWith] using And.intro
        (leftIH holds.1 leftClassified) (rightIH holds.2 rightClassified)
  | or left right leftIH rightIH =>
      have leftClassified : ∀ form ∈ formulaForms left,
          value form = 0 ∨ 0 < value form * form.eval point := by
        intro form member
        exact classified form (List.mem_append_left _ member)
      have rightClassified : ∀ form ∈ formulaForms right,
          value form = 0 ∨ 0 < value form * form.eval point := by
        intro form member
        exact classified form (List.mem_append_right _ member)
      rcases holds with leftHolds | rightHolds
      · simpa [closedFormula, formulaEvalWith] using
          Or.inl (leftIH leftHolds leftClassified)
      · simpa [closedFormula, formulaEvalWith] using
          Or.inr (rightIH rightHolds rightClassified)

end CCLFormulaClosure
end FTA
