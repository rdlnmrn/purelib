import FTA.CCLParserGeometry
import FTA.CCLOwnerGrid

/-!
# Stability of finite CCL parser formulas

Every parser formula exposes a finite list of Hermitian forms.  If all those
forms are nonzero at a point and their signs are preserved by an owner-grid
step, then all six strict or weak atom tests, every conjunction, and every
partial-sector disjunction keep the same truth value.  This connects the
bounded perturbation calculation directly to arbitrary raw-prefix formulas.
-/

namespace FTA
namespace CCLFormulaStability

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLParserGeometry
open FTA.CCLOwnerDirection
open FTA.CCLOwnerGrid

abbrev QI := CCL.GaussianRat

theorem SignTest.holds_iff_of_mul_pos (test : SignTest) {a b : ℚ}
    (sameSign : 0 < a * b) : test.Holds a ↔ test.Holds b := by
  rcases mul_pos_iff.mp sameSign with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have haNonzero : a ≠ 0 := ne_of_gt ha
    have hbNonzero : b ≠ 0 := ne_of_gt hb
    cases test <;> simp [SignTest.Holds, ha, hb, haNonzero, hbNonzero] <;>
      constructor <;> intro <;> linarith
  · have haNonzero : a ≠ 0 := ne_of_lt ha
    have hbNonzero : b ≠ 0 := ne_of_lt hb
    cases test <;> simp [SignTest.Holds, ha, hb, haNonzero, hbNonzero] <;>
      constructor <;> intro <;> linarith

/-- Finite list of all Hermitian forms occurring in a parser formula. -/
def formulaForms : Formula → List HermitianForm
  | .truth | .falsity => []
  | .atom atom => [atom.form]
  | .and left right | .or left right => formulaForms left ++ formulaForms right

theorem formula_holds_iff_of_all_mul_pos (formula : Formula) (z w : QI)
    (sameSigns : ∀ form ∈ formulaForms formula, 0 < form.eval z * form.eval w) :
    formula.Holds z ↔ formula.Holds w := by
  induction formula with
  | truth => simp [Formula.Holds]
  | falsity => simp [Formula.Holds]
  | atom atom =>
      apply SignTest.holds_iff_of_mul_pos atom.sign
      exact sameSigns atom.form (by simp [formulaForms])
  | and left right leftIH rightIH =>
      have leftSigns : ∀ form ∈ formulaForms left,
          0 < form.eval z * form.eval w := by
        intro form hform
        exact sameSigns form (List.mem_append_left _ hform)
      have rightSigns : ∀ form ∈ formulaForms right,
          0 < form.eval z * form.eval w := by
        intro form hform
        exact sameSigns form (List.mem_append_right _ hform)
      exact and_congr (leftIH leftSigns) (rightIH rightSigns)
  | or left right leftIH rightIH =>
      have leftSigns : ∀ form ∈ formulaForms left,
          0 < form.eval z * form.eval w := by
        intro form hform
        exact sameSigns form (List.mem_append_left _ hform)
      have rightSigns : ∀ form ∈ formulaForms right,
          0 < form.eval z * form.eval w := by
        intro form hform
        exact sameSigns form (List.mem_append_right _ hform)
      exact or_congr (leftIH leftSigns) (rightIH rightSigns)

/-- A positive-owner grid step preserves an arbitrary earlier parser formula
whose finitely many boundary forms are strict at the equality point. -/
theorem positiveOwner_preserves_formula
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (formula : Formula)
    (allNonzero : ∀ form ∈ formulaForms formula, form.eval z ≠ 0)
    (holds : formula.Holds z) :
    formula.Holds (step z
      (ownerEpsilon increasing (formulaForms formula) increasing.vector)
      increasing.vector) := by
  apply (formula_holds_iff_of_all_mul_pos formula z _
    (positiveOwner_preserves_strict_signs increasing
      (formulaForms formula) allNonzero)).mp
  exact holds

/-- The corresponding negative-owner grid step preserves the same formula. -/
theorem negativeOwner_preserves_formula
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (formula : Formula)
    (allNonzero : ∀ form ∈ formulaForms formula, form.eval z ≠ 0)
    (holds : formula.Holds z) :
    formula.Holds (step z
      (ownerEpsilon increasing (formulaForms formula) (-increasing.vector))
      (-increasing.vector)) := by
  apply (formula_holds_iff_of_all_mul_pos formula z _
    (negativeOwner_preserves_strict_signs increasing
      (formulaForms formula) allNonzero)).mp
  exact holds

/-- Direct arbitrary-parser-state specialization of the positive-owner step. -/
theorem positiveOwner_preserves_state
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (state : RawParser.State)
    (allNonzero : ∀ form ∈ formulaForms (stateFormula state), form.eval z ≠ 0)
    (holds : state.Holds z) :
    state.Holds (step z
      (ownerEpsilon increasing (formulaForms (stateFormula state))
        increasing.vector) increasing.vector) := by
  apply (stateFormula_iff state _).mp
  apply positiveOwner_preserves_formula increasing (stateFormula state) allNonzero
  exact (stateFormula_iff state z).mpr holds

/-- Direct arbitrary-parser-state specialization of the negative-owner step. -/
theorem negativeOwner_preserves_state
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (state : RawParser.State)
    (allNonzero : ∀ form ∈ formulaForms (stateFormula state), form.eval z ≠ 0)
    (holds : state.Holds z) :
    state.Holds (step z
      (ownerEpsilon increasing (formulaForms (stateFormula state))
        (-increasing.vector)) (-increasing.vector)) := by
  apply (stateFormula_iff state _).mp
  apply negativeOwner_preserves_formula increasing (stateFormula state) allNonzero
  exact (stateFormula_iff state z).mpr holds

end CCLFormulaStability
end FTA
