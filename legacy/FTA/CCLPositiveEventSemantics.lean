import FTA.CCLBranchController
import FTA.CCLBranchSampling

/-!
# Canonical semantics of a selected positive CCL event

The event-owner classifier evaluates both child formulas through one
canonical rational oracle: atom polynomials divisible by the isolated event
factor receive zero, while every coprime atom receives its certified stable
sign sample.  This small adapter exposes the selected component without
re-expanding the classified-event proof in the geometric sampler.
-/

namespace FTA
namespace CCLPositiveEventSemantics

open CCL
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchPlan
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLFormulaStability
open FTA.CCLGeometry
open FTA.CCLParserGeometry
open FTA.CCLIntersectionEventSigns
open FTA.CCLIntersectionSharedFactors
open FTA.CCLNextBitFormula
open FTA.CCLOwnerDirection
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Structural evaluation through actual Hermitian values is the ordinary
propositional formula semantics. -/
theorem formulaEvalWith_eval_eq_true_iff
    (formula : Formula) (point : QI) :
    formulaEvalWith formula (fun form => form.eval point) = true ↔
      formula.Holds point := by
  induction formula with
  | truth => simp [formulaEvalWith, Formula.Holds]
  | falsity => simp [formulaEvalWith, Formula.Holds]
  | atom atom =>
      simp only [formulaEvalWith, Formula.Holds, Atom.Holds, decide_eq_true_eq]
  | and left right leftInduction rightInduction =>
      simp only [formulaEvalWith, Formula.Holds, Bool.and_eq_true,
        leftInduction, rightInduction]
  | or left right leftInduction rightInduction =>
      simp only [formulaEvalWith, Formula.Holds, Bool.or_eq_true,
        leftInduction, rightInduction]

/-- A formula evaluator depends only on the sign-test outcome of each atom
that occurs in its syntax tree. -/
theorem formulaEvalWith_eq_of_atomTests
    (formula : Formula) (left right : HermitianForm → ℚ)
    (agree : ∀ atom ∈ formulaAtoms formula,
      (atom.sign.Holds (left atom.form) ↔
        atom.sign.Holds (right atom.form))) :
    formulaEvalWith formula left = formulaEvalWith formula right := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | atom atom =>
      apply Bool.decide_congr
      exact agree atom (by simp [formulaAtoms])
  | and first second firstInduction secondInduction =>
      have firstAgree : ∀ atom ∈ formulaAtoms first,
          atom.sign.Holds (left atom.form) ↔
            atom.sign.Holds (right atom.form) := by
        intro atom member
        exact agree atom (List.mem_append_left _ member)
      have secondAgree : ∀ atom ∈ formulaAtoms second,
          atom.sign.Holds (left atom.form) ↔
            atom.sign.Holds (right atom.form) := by
        intro atom member
        exact agree atom (List.mem_append_right _ member)
      simp only [formulaEvalWith]
      rw [firstInduction firstAgree, secondInduction secondAgree]
  | or first second firstInduction secondInduction =>
      have firstAgree : ∀ atom ∈ formulaAtoms first,
          atom.sign.Holds (left atom.form) ↔
            atom.sign.Holds (right atom.form) := by
        intro atom member
        exact agree atom (List.mem_append_left _ member)
      have secondAgree : ∀ atom ∈ formulaAtoms second,
          atom.sign.Holds (left atom.form) ↔
            atom.sign.Holds (right atom.form) := by
        intro atom member
        exact agree atom (List.mem_append_right _ member)
      simp only [formulaEvalWith]
      rw [firstInduction firstAgree, secondInduction secondAgree]

/-- At a true disjunction retain only its first true branch; conjunctions
retain both branches.  The result is the finite conjunction of atom outcomes
that a perturbation actually has to realize. -/
def satisfyingAtoms : Formula → (HermitianForm → ℚ) → List Atom
  | .truth, _ | .falsity, _ => []
  | .atom atom, _ => [atom]
  | .and first second, value =>
      satisfyingAtoms first value ++ satisfyingAtoms second value
  | .or first second, value =>
      if formulaEvalWith first value then satisfyingAtoms first value
      else satisfyingAtoms second value

/-- The selected true branch never introduces atoms that were absent from the
source formula, quantitatively as well as by membership. -/
theorem satisfyingAtoms_length_le_formulaAtoms
    (formula : Formula) (value : HermitianForm → ℚ) :
    (satisfyingAtoms formula value).length ≤ (formulaAtoms formula).length := by
  induction formula with
  | truth => simp [satisfyingAtoms, formulaAtoms]
  | falsity => simp [satisfyingAtoms, formulaAtoms]
  | atom atom => simp [satisfyingAtoms, formulaAtoms]
  | and left right leftInduction rightInduction =>
      simp only [satisfyingAtoms, formulaAtoms, List.length_append]
      omega
  | or left right leftInduction rightInduction =>
      by_cases leftTrue : formulaEvalWith left value
      · simp [satisfyingAtoms, formulaAtoms, leftTrue]
        omega
      · simp [satisfyingAtoms, formulaAtoms, leftTrue]
        omega

def pullbackAtom (matrix : Mat2 QI) (atom : Atom) : Atom :=
  ⟨pullbackForm matrix atom.form, atom.sign⟩

theorem formulaEvalWith_pullback
    (matrix : Mat2 QI) (formula : Formula)
    (value : HermitianForm → ℚ) :
    formulaEvalWith (Formula.pullback matrix formula) value =
      formulaEvalWith formula
        (fun form => value (pullbackForm matrix form)) := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | atom atom => rfl
  | and left right leftInduction rightInduction =>
      simp only [Formula.pullback, formulaEvalWith, leftInduction,
        rightInduction]
  | or left right leftInduction rightInduction =>
      simp only [Formula.pullback, formulaEvalWith, leftInduction,
        rightInduction]

/-- The selected conjunction of a pulled-back formula is exactly the mapped
selected conjunction of the local formula under the pulled-back oracle. -/
theorem satisfyingAtoms_pullback
    (matrix : Mat2 QI) (formula : Formula)
    (value : HermitianForm → ℚ) :
    satisfyingAtoms (Formula.pullback matrix formula) value =
      (satisfyingAtoms formula
        (fun form => value (pullbackForm matrix form))).map
          (pullbackAtom matrix) := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | atom atom => rfl
  | and left right leftInduction rightInduction =>
      simp only [Formula.pullback, satisfyingAtoms, leftInduction,
        rightInduction, List.map_append]
  | or left right leftInduction rightInduction =>
      simp only [Formula.pullback, satisfyingAtoms,
        formulaEvalWith_pullback]
      by_cases leftTrue : formulaEvalWith left
          (fun form => value (pullbackForm matrix form)) = true
      · simp [leftTrue, leftInduction]
      · simp [leftTrue, rightInduction]

theorem satisfyingAtoms_mem_formulaAtoms
    (formula : Formula) (value : HermitianForm → ℚ) {atom : Atom}
    (member : atom ∈ satisfyingAtoms formula value) :
    atom ∈ formulaAtoms formula := by
  induction formula with
  | truth => simp [satisfyingAtoms] at member
  | falsity => simp [satisfyingAtoms] at member
  | atom selected => simpa [satisfyingAtoms, formulaAtoms] using member
  | and first second firstInduction secondInduction =>
      rw [satisfyingAtoms, List.mem_append] at member
      rw [formulaAtoms, List.mem_append]
      exact member.imp firstInduction secondInduction
  | or first second firstInduction secondInduction =>
      by_cases firstTrue : formulaEvalWith first value = true
      · rw [satisfyingAtoms, if_pos firstTrue] at member
        exact List.mem_append_left _ (firstInduction member)
      · rw [satisfyingAtoms, if_neg firstTrue] at member
        exact List.mem_append_right _ (secondInduction member)

theorem satisfyingAtoms_tests
    (formula : Formula) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith formula value = true) :
    ∀ atom ∈ satisfyingAtoms formula value,
      atom.sign.Holds (value atom.form) := by
  induction formula with
  | truth => simp [satisfyingAtoms]
  | falsity => simp [formulaEvalWith] at evaluation
  | atom selected =>
      intro atom member
      simp only [satisfyingAtoms, List.mem_singleton] at member
      subst atom
      exact of_decide_eq_true evaluation
  | and first second firstInduction secondInduction =>
      simp only [formulaEvalWith, Bool.and_eq_true] at evaluation
      intro atom member
      rw [satisfyingAtoms, List.mem_append] at member
      rcases member with firstMember | secondMember
      · exact firstInduction evaluation.1 atom firstMember
      · exact secondInduction evaluation.2 atom secondMember
  | or first second firstInduction secondInduction =>
      by_cases firstTrue : formulaEvalWith first value = true
      · intro atom member
        rw [satisfyingAtoms, if_pos firstTrue] at member
        exact firstInduction firstTrue atom member
      · have rightTrue : formulaEvalWith second value = true := by
          simp only [formulaEvalWith, Bool.or_eq_true] at evaluation
          rcases evaluation with leftTrue | rightTrue
          · exact (firstTrue leftTrue).elim
          · exact rightTrue
        intro atom member
        rw [satisfyingAtoms, if_neg firstTrue] at member
        exact secondInduction rightTrue atom member

/-- Realizing the selected conjunction of atom outcomes suffices to realize
the complete Boolean formula.  Unused false disjuncts impose no obligations. -/
theorem formula_holds_of_satisfyingAtoms
    (formula : Formula) (value : HermitianForm → ℚ) (point : QI)
    (evaluation : formulaEvalWith formula value = true)
    (atomsHold : ∀ atom ∈ satisfyingAtoms formula value, atom.Holds point) :
    formula.Holds point := by
  induction formula with
  | truth => trivial
  | falsity => simp [formulaEvalWith] at evaluation
  | atom selected =>
      exact atomsHold selected (by simp [satisfyingAtoms])
  | and first second firstInduction secondInduction =>
      simp only [formulaEvalWith, Bool.and_eq_true] at evaluation
      constructor
      · apply firstInduction evaluation.1
        intro atom member
        exact atomsHold atom (List.mem_append_left _ member)
      · apply secondInduction evaluation.2
        intro atom member
        exact atomsHold atom (List.mem_append_right _ member)
  | or first second firstInduction secondInduction =>
      by_cases firstTrue : formulaEvalWith first value = true
      · left
        apply firstInduction firstTrue
        intro atom member
        apply atomsHold atom
        simpa only [satisfyingAtoms, if_pos firstTrue] using member
      · right
        have rightTrue : formulaEvalWith second value = true := by
          simp only [formulaEvalWith, Bool.or_eq_true] at evaluation
          rcases evaluation with leftTrue | rightTrue
          · exact (firstTrue leftTrue).elim
          · exact rightTrue
        apply secondInduction rightTrue
        intro atom member
        apply atomsHold atom
        simpa only [satisfyingAtoms, if_neg firstTrue] using member

/-- Parser formulas use open or closed inequalities, never an exact equality
test that a strict rational perturbation would have to preserve. -/
def formulaNoZeroTests : Formula → Prop
  | .truth | .falsity => True
  | .atom atom => atom.sign ≠ .zero
  | .and first second | .or first second =>
      formulaNoZeroTests first ∧ formulaNoZeroTests second

theorem formulaNoZeroTests_all (formulas : List Formula)
    (all : ∀ formula ∈ formulas, formulaNoZeroTests formula) :
    formulaNoZeroTests (Formula.all formulas) := by
  induction formulas with
  | nil => trivial
  | cons formula formulas inductionHypothesis =>
      exact ⟨all formula (by simp), inductionHypothesis (by
        intro item member
        exact all item (by simp [member]))⟩

theorem formulaNoZeroTests_any (formulas : List Formula)
    (all : ∀ formula ∈ formulas, formulaNoZeroTests formula) :
    formulaNoZeroTests (Formula.any formulas) := by
  induction formulas with
  | nil => trivial
  | cons formula formulas inductionHypothesis =>
      exact ⟨all formula (by simp), inductionHypothesis (by
        intro item member
        exact all item (by simp [member]))⟩

theorem formulaNoZeroTests_pullback (matrix : Mat2 QI) (formula : Formula)
    (noZero : formulaNoZeroTests formula) :
    formulaNoZeroTests
      (FTA.CCLFormulaPullback.Formula.pullback matrix formula) := by
  induction formula with
  | truth => trivial
  | falsity => trivial
  | atom atom => exact noZero
  | and first second firstInduction secondInduction =>
      exact ⟨firstInduction noZero.1, secondInduction noZero.2⟩
  | or first second firstInduction secondInduction =>
      exact ⟨firstInduction noZero.1, secondInduction noZero.2⟩

theorem satisfyingAtoms_noZeroTest
    (formula : Formula) (value : HermitianForm → ℚ)
    (noZero : formulaNoZeroTests formula) :
    ∀ atom ∈ satisfyingAtoms formula value, atom.sign ≠ .zero := by
  induction formula with
  | truth => simp [satisfyingAtoms]
  | falsity => simp [satisfyingAtoms]
  | atom selected =>
      intro atom member
      simp only [satisfyingAtoms, List.mem_singleton] at member
      subst atom
      exact noZero
  | and first second firstInduction secondInduction =>
      intro atom member
      rw [satisfyingAtoms, List.mem_append] at member
      rcases member with firstMember | secondMember
      · exact firstInduction noZero.1 atom firstMember
      · exact secondInduction noZero.2 atom secondMember
  | or first second firstInduction secondInduction =>
      by_cases firstTrue : formulaEvalWith first value = true
      · intro atom member
        rw [satisfyingAtoms, if_pos firstTrue] at member
        exact firstInduction noZero.1 atom member
      · intro atom member
        rw [satisfyingAtoms, if_neg firstTrue] at member
        exact secondInduction noZero.2 atom member

theorem denominatorFormula_noZeroTests (matrix : Mat2 QI) :
    formulaNoZeroTests (denominatorFormula matrix) := by
  simp [denominatorFormula, formulaNoZeroTests]

theorem radialFormula_noZeroTests
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    formulaNoZeroTests (radialFormula kind exponent matrix) := by
  cases kind <;> simp [radialFormula, formulaNoZeroTests]

theorem sectorFormula_noZeroTests (sector : Sector) (matrix : Mat2 QI) :
    formulaNoZeroTests (sectorFormula sector matrix) := by
  cases sector <;> simp [sectorFormula, formulaNoZeroTests]

theorem constraintFormula_noZeroTests (constraint : RawParser.Constraint) :
    formulaNoZeroTests (constraintFormula constraint) := by
  exact ⟨denominatorFormula_noZeroTests constraint.matrix,
    radialFormula_noZeroTests constraint.kind constraint.exponent
      constraint.matrix,
    sectorFormula_noZeroTests constraint.sector
      (normalizedMatrix constraint.kind constraint.exponent constraint.matrix)⟩

theorem sectorBitsFormula_noZeroTests
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (bits : RawParser.SectorBits) :
    formulaNoZeroTests (sectorBitsFormula kind exponent bits) := by
  cases bits with
  | zero =>
      apply formulaNoZeroTests_any
      intro formula member
      rcases List.mem_map.mp member with ⟨sector, _sectorMember, rfl⟩
      exact sectorFormula_noZeroTests sector
        (normalizedMatrix kind exponent RawParser.identityMatrix)
  | one first =>
      cases first <;> simp [sectorBitsFormula, formulaNoZeroTests]
  | two first second =>
      cases first <;> cases second <;>
        simp [sectorBitsFormula, formulaNoZeroTests]

theorem activeFormula_noZeroTests (phase : RawParser.Phase) :
    formulaNoZeroTests (activeFormula phase) := by
  cases phase with
  | initial => trivial
  | highUnary count => simp [activeFormula, formulaNoZeroTests]
  | lowUnary count =>
      cases count <;> simp [activeFormula, formulaNoZeroTests]
  | loopUnary count => simp [activeFormula, formulaNoZeroTests]
  | sector kind exponent bits =>
      exact ⟨radialFormula_noZeroTests kind exponent RawParser.identityMatrix,
        sectorBitsFormula_noZeroTests kind exponent bits⟩

theorem stateFormula_noZeroTests (state : RawParser.State) :
    formulaNoZeroTests (stateFormula state) := by
  constructor
  · apply formulaNoZeroTests_all
    intro formula member
    rcases List.mem_map.mp member with ⟨constraint, _constraintMember, rfl⟩
    exact constraintFormula_noZeroTests constraint
  · exact activeFormula_noZeroTests state.phase

theorem advanceFormula_noZeroTests (state : RawParser.State) (bit : Bool) :
    formulaNoZeroTests (FTA.CCLNextBitFormula.advanceFormula state bit) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial => exact stateFormula_noZeroTests _
  | highUnary count => exact stateFormula_noZeroTests _
  | lowUnary count => exact stateFormula_noZeroTests _
  | loopUnary count => exact stateFormula_noZeroTests _
  | sector kind exponent bits =>
      cases bits with
      | zero => exact stateFormula_noZeroTests _
      | one first => exact stateFormula_noZeroTests _
      | two first second =>
          exact ⟨radialFormula_noZeroTests kind exponent RawParser.identityMatrix,
            sectorFormula_noZeroTests (RawParser.sectorOfBits first second bit)
              (normalizedMatrix kind exponent RawParser.identityMatrix), by
                simp [formulaNoZeroTests]⟩

theorem inputAdvanceFormula_noZeroTests
    (state : RawParser.State) (bit : Bool) :
    formulaNoZeroTests (inputAdvanceFormula state bit) := by
  apply formulaNoZeroTests_pullback
  exact advanceFormula_noZeroTests state bit

theorem incrementalAdvanceFormula_noZeroTests
    (state : RawParser.State) (bit : Bool) :
    formulaNoZeroTests (incrementalAdvanceFormula state bit) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial => exact activeFormula_noZeroTests _
  | highUnary count => exact activeFormula_noZeroTests _
  | lowUnary count => exact activeFormula_noZeroTests _
  | loopUnary count => exact activeFormula_noZeroTests _
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa [incrementalAdvanceFormula] using
            (activeFormula_noZeroTests
              (RawParser.step
                ⟨.sector kind exponent .zero, matrix, history⟩ bit).phase)
      | one first =>
          simpa [incrementalAdvanceFormula] using
            (activeFormula_noZeroTests
              (RawParser.step
                ⟨.sector kind exponent (.one first), matrix, history⟩
                bit).phase)
      | two first second =>
          simpa [incrementalAdvanceFormula] using
            (advanceFormula_noZeroTests
              ⟨.sector kind exponent (.two first second), matrix, history⟩
              bit)

theorem inputIncrementalAdvanceFormula_noZeroTests
    (state : RawParser.State) (bit : Bool) :
    formulaNoZeroTests (inputIncrementalAdvanceFormula state bit) := by
  apply formulaNoZeroTests_pullback
  exact incrementalAdvanceFormula_noZeroTests state bit

/-- The two history-free child predicates are algebraically disjoint for
every coherent form-value oracle.  Historical constraints are absent from
the statement and proof; only the complementary local strict/weak tests are
used. -/
theorem formulaEvalWith_inputIncrementalAdvance_ne_both
    (state : RawParser.State) (value : HermitianForm → ℚ) :
    ¬(formulaEvalWith (inputIncrementalAdvanceFormula state false) value =
        true ∧
      formulaEvalWith (inputIncrementalAdvanceFormula state true) value =
        true) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      rintro ⟨falseCheck, trueCheck⟩
      simp [inputIncrementalAdvanceFormula, incrementalAdvanceFormula,
        RawParser.step, activeFormula, Formula.pullback, formulaEvalWith,
        SignTest.Holds] at falseCheck trueCheck
      linarith
  | highUnary count =>
      rintro ⟨falseCheck, trueCheck⟩
      simp [inputIncrementalAdvanceFormula, incrementalAdvanceFormula,
        RawParser.step, activeFormula, radialFormula, sectorBitsFormula,
        Formula.pullback, formulaEvalWith, normComparisonForm_identity,
        SignTest.Holds] at falseCheck trueCheck
      linarith
  | lowUnary count =>
      rintro ⟨falseCheck, trueCheck⟩
      cases count with
      | zero =>
          simp [inputIncrementalAdvanceFormula, incrementalAdvanceFormula,
            RawParser.step, activeFormula, radialFormula, sectorBitsFormula,
            Formula.pullback, formulaEvalWith, normComparisonForm_identity,
            SignTest.Holds] at falseCheck trueCheck
          linarith
      | succ count =>
          simp [inputIncrementalAdvanceFormula, incrementalAdvanceFormula,
            RawParser.step, activeFormula, radialFormula, sectorBitsFormula,
            Formula.pullback, formulaEvalWith, normComparisonForm_identity,
            SignTest.Holds] at falseCheck trueCheck
          linarith
  | loopUnary count =>
      rintro ⟨falseCheck, trueCheck⟩
      simp [inputIncrementalAdvanceFormula, incrementalAdvanceFormula,
        RawParser.step, activeFormula, radialFormula, sectorBitsFormula,
        Formula.pullback, formulaEvalWith, normComparisonForm_identity,
        SignTest.Holds] at falseCheck trueCheck
      linarith
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          rintro ⟨falseCheck, trueCheck⟩
          simp [inputIncrementalAdvanceFormula, incrementalAdvanceFormula,
            RawParser.step, activeFormula, radialFormula, sectorBitsFormula,
            Formula.pullback, formulaEvalWith, SignTest.Holds]
              at falseCheck trueCheck
          rcases falseCheck.2 with falseFirst | falseSecond
          · rcases trueCheck.2.1.1 with realNegative | imagNonpositive
            · linarith [falseFirst.1, realNegative]
            · linarith [falseFirst.2, imagNonpositive]
          · rcases trueCheck.2.1.2 with realNonnegative | imagNegative
            · linarith [falseSecond.1, realNonnegative]
            · linarith [falseSecond.2, imagNegative]
      | one first =>
          rintro ⟨falseCheck, trueCheck⟩
          cases first <;>
            simp [inputIncrementalAdvanceFormula, incrementalAdvanceFormula,
              RawParser.step, activeFormula, radialFormula, sectorBitsFormula,
              Formula.pullback, formulaEvalWith, SignTest.Holds]
                at falseCheck trueCheck <;>
            linarith
      | two first second =>
          rintro ⟨falseCheck, trueCheck⟩
          cases first <;> cases second <;>
            simp [inputIncrementalAdvanceFormula, incrementalAdvanceFormula,
              advanceFormula, radialFormula,
              sectorFormula, Formula.pullback, formulaEvalWith,
              RawParser.sectorOfBits, SignTest.Holds]
                at falseCheck trueCheck <;>
            linarith

/-- Every incremental atom occurs in the original complete child formula, so
the existing event classifier has already assigned it an equality or coprime
sign relation. -/
theorem inputIncrementalAdvanceFormula_atoms_subset
    (state : RawParser.State) (bit : Bool) :
    ∀ atom ∈ formulaAtoms (inputIncrementalAdvanceFormula state bit),
      atom ∈ formulaAtoms (inputAdvanceFormula state bit) := by
  intro atom member
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaAtoms] at member ⊢ <;>
        tauto
  | highUnary count =>
      cases bit <;>
        simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaAtoms] at member ⊢ <;>
        tauto
  | lowUnary count =>
      cases bit <;>
        simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaAtoms] at member ⊢ <;>
        tauto
  | loopUnary count =>
      cases bit <;>
        simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaAtoms] at member ⊢ <;>
        tauto
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          cases bit <;>
            simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
              incrementalAdvanceFormula, advanceFormula, Formula.pullback,
              stateFormula, RawParser.step, formulaAtoms] at member ⊢ <;>
            tauto
      | one first =>
          cases bit <;>
            simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
              incrementalAdvanceFormula, advanceFormula, Formula.pullback,
              stateFormula, RawParser.step, formulaAtoms] at member ⊢ <;>
            tauto
      | two first second =>
          simpa [inputIncrementalAdvanceFormula, inputAdvanceFormula,
            incrementalAdvanceFormula] using member

/-! ## Existing-prefix semantics in the original coordinate -/

/-- The complete current-state predicate pulled back from its affine tail to
the original winding-box coordinate. -/
def inputStateFormula (state : RawParser.State) : Formula :=
  FTA.CCLFormulaPullback.Formula.pullback (adjugate state.matrix)
    (stateFormula state)

theorem inputStateFormula_noZeroTests (state : RawParser.State) :
    formulaNoZeroTests (inputStateFormula state) := by
  apply formulaNoZeroTests_pullback
  exact stateFormula_noZeroTests state

theorem inputStateFormula_iff
    (state : RawParser.State) (input : QI)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0) :
    (inputStateFormula state).Holds input ↔
      state.Holds (RatBox.homographic (adjugate state.matrix) input) := by
  rw [inputStateFormula,
    FTA.CCLFormulaPullback.Formula.pullback_iff
      (adjugate state.matrix) (stateFormula state) input inverseDenominator]
  exact stateFormula_iff state _

/-- Any affine sample representing the current parser state satisfies the
pulled-back old-prefix formula at its original input coordinate. -/
theorem inputStateFormula_holds_of_represents
    (state : RawParser.State) (input tail : QI)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (represented : RawParserSemantics.Represents state input tail) :
    (inputStateFormula state).Holds input := by
  apply (inputStateFormula_iff state input inverseDenominator).2
  rw [CCLBranchSampling.inverse_tail_eq_of_represents state input tail
    determinantNonzero inverseDenominator represented]
  exact represented.2.2

/-- Conversely, the pulled-back old-prefix formula and affine denominator
construct the explicit inverse tail representing the original input. -/
theorem represents_of_inputStateFormula
    (state : RawParser.State) (input : QI)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (holds : (inputStateFormula state).Holds input) :
    RawParserSemantics.Represents state input
      (RatBox.homographic (adjugate state.matrix) input) :=
  represents_of_inverse_tail state input determinantNonzero inverseDenominator
    ((inputStateFormula_iff state input inverseDenominator).1 holds)

theorem represented_of_inputStateFormula
    (word : Prefix.Word) (input : QI)
    (inverseDenominator :
      (adjugate (RawParser.parse word).matrix).c * input +
        (adjugate (RawParser.parse word).matrix).d ≠ 0)
    (holds : (inputStateFormula (RawParser.parse word)).Holds input) :
    RawParserSemantics.Represented word input := by
  refine ⟨RatBox.homographic
    (adjugate (RawParser.parse word).matrix) input, ?_⟩
  apply represents_of_inputStateFormula
    (RawParser.parse word) input
    (by simpa only [determinant, Mat2.det] using RawParser.parse_det_ne word)
    inverseDenominator holds

/-- Canonically zero atoms in the selected true branch. -/
def activeSatisfyingAtoms
    (formula : Formula) (value : HermitianForm → ℚ) : List Atom :=
  (satisfyingAtoms formula value).filter fun atom =>
    decide (value atom.form = 0)

/-- Canonically strict atoms in the selected true branch. -/
def strictSatisfyingAtoms
    (formula : Formula) (value : HermitianForm → ℚ) : List Atom :=
  (satisfyingAtoms formula value).filter fun atom =>
    decide (value atom.form ≠ 0)

theorem activeSatisfyingAtoms_zero
    {formula : Formula} {value : HermitianForm → ℚ} {atom : Atom}
    (member : atom ∈ activeSatisfyingAtoms formula value) :
    value atom.form = 0 := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem activeSatisfyingAtoms_source
    {formula : Formula} {value : HermitianForm → ℚ} {atom : Atom}
    (member : atom ∈ activeSatisfyingAtoms formula value) :
    atom ∈ satisfyingAtoms formula value :=
  (List.mem_filter.mp member).1

theorem strictSatisfyingAtoms_ne
    {formula : Formula} {value : HermitianForm → ℚ} {atom : Atom}
    (member : atom ∈ strictSatisfyingAtoms formula value) :
    value atom.form ≠ 0 := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem strictSatisfyingAtoms_source
    {formula : Formula} {value : HermitianForm → ℚ} {atom : Atom}
    (member : atom ∈ strictSatisfyingAtoms formula value) :
    atom ∈ satisfyingAtoms formula value :=
  (List.mem_filter.mp member).1

/-- Orient either weak sign so its desired strict interior is positive. -/
def orientedWeakForm (atom : Atom) : HermitianForm :=
  match atom.sign with
  | .nonpositive => atom.form.neg
  | _ => atom.form

@[simp] theorem boundaryDiscriminant_orientedWeakForm (atom : Atom) :
    boundaryDiscriminant (orientedWeakForm atom) =
      boundaryDiscriminant atom.form := by
  cases atom with
  | mk form sign => cases sign <;> simp [orientedWeakForm]

@[simp] theorem orientedWeakForm_pullbackAtom
    (matrix : Mat2 QI) (atom : Atom) :
    orientedWeakForm (pullbackAtom matrix atom) =
      pullbackForm matrix (orientedWeakForm atom) := by
  cases atom with
  | mk form sign =>
      cases sign <;> simp [orientedWeakForm, pullbackAtom]

/-- Active weak inequalities, already oriented toward their required strict
side, in the exact list format consumed by the simultaneous owner grid. -/
def activeOwnerForms
    (formula : Formula) (value : HermitianForm → ℚ) : List HermitianForm :=
  (activeSatisfyingAtoms formula value).map orientedWeakForm

/-- Filtering to canonically active owner faces and orienting them cannot
increase the source formula's finite atom count. -/
theorem activeOwnerForms_length_le_formulaAtoms
    (formula : Formula) (value : HermitianForm → ℚ) :
    (activeOwnerForms formula value).length ≤
      (formulaAtoms formula).length := by
  calc
    (activeOwnerForms formula value).length =
        (activeSatisfyingAtoms formula value).length := by
      simp [activeOwnerForms]
    _ ≤ (satisfyingAtoms formula value).length := by
      exact List.length_filter_le _ _
    _ ≤ (formulaAtoms formula).length :=
      satisfyingAtoms_length_le_formulaAtoms formula value

theorem activeSatisfyingAtoms_pullback
    (matrix : Mat2 QI) (formula : Formula)
    (value : HermitianForm → ℚ) :
    activeSatisfyingAtoms (Formula.pullback matrix formula) value =
      (activeSatisfyingAtoms formula
        (fun form => value (pullbackForm matrix form))).map
          (pullbackAtom matrix) := by
  rw [activeSatisfyingAtoms, satisfyingAtoms_pullback,
    activeSatisfyingAtoms]
  let atoms := satisfyingAtoms formula
    (fun form => value (pullbackForm matrix form))
  change List.filter (fun atom => decide (value atom.form = 0))
      (atoms.map (pullbackAtom matrix)) =
    (List.filter (fun atom =>
      decide (value (pullbackForm matrix atom.form) = 0)) atoms).map
        (pullbackAtom matrix)
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      by_cases zero : value (pullbackForm matrix atom.form) = 0
      · simp [pullbackAtom, zero, inductionHypothesis]
      · simp [pullbackAtom, zero, inductionHypothesis]

/-- Active owner lists commute with homographic formula pullback. -/
theorem activeOwnerForms_pullback
    (matrix : Mat2 QI) (formula : Formula)
    (value : HermitianForm → ℚ) :
    activeOwnerForms (Formula.pullback matrix formula) value =
      (activeOwnerForms formula
        (fun form => value (pullbackForm matrix form))).map
          (pullbackForm matrix) := by
  simp [activeOwnerForms, activeSatisfyingAtoms_pullback, List.map_map]

/-- Canonically nonzero forms whose signs the owner grid must preserve. -/
def strictPriorForms
    (formula : Formula) (value : HermitianForm → ℚ) : List HermitianForm :=
  (strictSatisfyingAtoms formula value).map fun atom => atom.form

theorem activeOwnerForms_eval_zero_at_point
    (formula : Formula) (point : QI) {form : HermitianForm}
    (member : form ∈ activeOwnerForms formula (fun item => item.eval point)) :
    form.eval point = 0 := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  have zero := activeSatisfyingAtoms_zero atomMember
  rcases atom with ⟨form, sign⟩
  cases sign <;>
    simp [orientedWeakForm, HermitianForm.eval_neg] at zero ⊢ <;> linarith

theorem strictPriorForms_value_ne
    (formula : Formula) (value : HermitianForm → ℚ) {form : HermitianForm}
    (member : form ∈ strictPriorForms formula value) :
    value form ≠ 0 := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  exact strictSatisfyingAtoms_ne atomMember

/-- A canonically active atom in a true branch can only use one of the two
weak inequality tests, provided exact-zero tests are absent from the formula. -/
theorem activeSatisfyingAtom_sign_weak
    {formula : Formula} {value : HermitianForm → ℚ}
    (evaluation : formulaEvalWith formula value = true)
    (noZeroTest : ∀ atom ∈ satisfyingAtoms formula value,
      atom.sign ≠ .zero)
    {atom : Atom} (member : atom ∈ activeSatisfyingAtoms formula value) :
    atom.sign = .nonpositive ∨ atom.sign = .nonnegative := by
  have source := activeSatisfyingAtoms_source member
  have test := satisfyingAtoms_tests formula value evaluation atom source
  have zero := activeSatisfyingAtoms_zero member
  have notZero := noZeroTest atom source
  cases signEq : atom.sign with
  | negative => simp [signEq, SignTest.Holds, zero] at test
  | nonpositive => exact Or.inl rfl
  | zero => exact (notZero signEq).elim
  | nonzero => simp [signEq, SignTest.Holds, zero] at test
  | nonnegative => exact Or.inr rfl
  | positive => simp [signEq, SignTest.Holds, zero] at test

theorem activeSatisfyingAtom_holds_of_oriented_pos
    {formula : Formula} {value : HermitianForm → ℚ}
    (evaluation : formulaEvalWith formula value = true)
    (noZeroTest : ∀ atom ∈ satisfyingAtoms formula value,
      atom.sign ≠ .zero)
    {atom : Atom} (member : atom ∈ activeSatisfyingAtoms formula value)
    {point : QI} (positive : 0 < (orientedWeakForm atom).eval point) :
    atom.Holds point := by
  rcases activeSatisfyingAtom_sign_weak evaluation noZeroTest member with
      nonpositive | nonnegative
  · simp only [nonpositive, orientedWeakForm, HermitianForm.eval_neg] at positive
    simp only [Atom.Holds, nonpositive, SignTest.Holds]
    linarith
  · simpa only [Atom.Holds, nonnegative, SignTest.Holds, orientedWeakForm]
      using positive.le

theorem strictSatisfyingAtom_holds_of_mul_pos
    {formula : Formula} {value : HermitianForm → ℚ}
    (evaluation : formulaEvalWith formula value = true)
    {atom : Atom} (member : atom ∈ strictSatisfyingAtoms formula value)
    {point : QI} (sameSign : 0 < value atom.form * atom.form.eval point) :
    atom.Holds point := by
  have source := strictSatisfyingAtoms_source member
  have canonical := satisfyingAtoms_tests formula value evaluation atom source
  exact (SignTest.holds_iff_of_mul_pos atom.sign sameSign).mp canonical

/-- Complete active/strict realization principle used by the approximate
multi-owner grid. -/
theorem formula_holds_of_active_strict
    (formula : Formula) (value : HermitianForm → ℚ) (point : QI)
    (evaluation : formulaEvalWith formula value = true)
    (noZeroTest : ∀ atom ∈ satisfyingAtoms formula value,
      atom.sign ≠ .zero)
    (activePositive : ∀ atom ∈ activeSatisfyingAtoms formula value,
      0 < (orientedWeakForm atom).eval point)
    (strictSameSign : ∀ atom ∈ strictSatisfyingAtoms formula value,
      0 < value atom.form * atom.form.eval point) :
    formula.Holds point := by
  apply formula_holds_of_satisfyingAtoms formula value point evaluation
  intro atom source
  by_cases zero : value atom.form = 0
  · apply activeSatisfyingAtom_holds_of_oriented_pos evaluation noZeroTest
      (List.mem_filter.mpr ⟨source, by simpa only [decide_eq_true_eq]⟩)
    exact activePositive atom
      (List.mem_filter.mpr ⟨source, by simpa only [decide_eq_true_eq]⟩)
  · apply strictSatisfyingAtom_holds_of_mul_pos evaluation
      (List.mem_filter.mpr ⟨source, by simpa only [decide_eq_true_eq]⟩)
    exact strictSameSign atom
      (List.mem_filter.mpr ⟨source, by simpa only [decide_eq_true_eq]⟩)

/-- List-facing form of the realization principle, matching
`CCLMultiOwnerGrid.TangentDirection` and its protected prior list directly. -/
theorem formula_holds_of_owner_form_lists
    (formula : Formula) (value : HermitianForm → ℚ) (point : QI)
    (evaluation : formulaEvalWith formula value = true)
    (noZero : formulaNoZeroTests formula)
    (activePositive : ∀ form ∈ activeOwnerForms formula value,
      0 < form.eval point)
    (strictSameSign : ∀ form ∈ strictPriorForms formula value,
      0 < value form * form.eval point) :
    formula.Holds point := by
  apply formula_holds_of_active_strict formula value point evaluation
    (satisfyingAtoms_noZeroTest formula value noZero)
  · intro atom member
    apply activePositive (orientedWeakForm atom)
    exact List.mem_map.mpr ⟨atom, member, rfl⟩
  · intro atom member
    apply strictSameSign atom.form
    exact List.mem_map.mpr ⟨atom, member, rfl⟩

/-! ## Owner-independent event semantics -/

/-- Canonical Hermitian-form value at an arbitrary re-isolated parser event.
This is the common oracle underlying the selected-owner wrappers below, but
it remains available when both owner checks are false. -/
def inputEventCanonicalValue
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (form : HermitianForm) : ℚ :=
  canonicalEventValue cell.branch.factor.input (clearedForm form path)
    (cell.branch.computeEventSigns cell.parent).refined.interval.lower

/-- History-free two-child table at an arbitrary isolated input event.  The
same canonical oracle is used for both entries, so repeated local faces keep
one coherent algebraic sign. -/
def inputEventIncrementalChecks
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : Bool × Bool :=
  (formulaEvalWith (inputIncrementalAdvanceFormula state false)
      (inputEventCanonicalValue cell),
    formulaEvalWith (inputIncrementalAdvanceFormula state true)
      (inputEventCanonicalValue cell))

/-- The direct local table never selects both bits, independently of every
historical parser constraint. -/
theorem inputEventIncrementalChecks_ne_both
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    inputEventIncrementalChecks cell ≠ (true, true) := by
  intro both
  apply formulaEvalWith_inputIncrementalAdvance_ne_both state
    (inputEventCanonicalValue cell)
  constructor
  · exact congrArg Prod.fst both
  · exact congrArg Prod.snd both

/-- A false history-free child makes the corresponding complete child false.
In ordinary phases the complete formula is the conjunction of historical
constraints with this incremental predicate; at a completed sector the two
formulas coincide. -/
theorem formulaEvalWith_inputAdvance_false_of_incremental_false
    (state : RawParser.State) (bit : Bool)
    (value : HermitianForm → ℚ)
    (incrementalFalse : formulaEvalWith
      (inputIncrementalAdvanceFormula state bit) value = false) :
    formulaEvalWith (inputAdvanceFormula state bit) value = false := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, stateFormula,
          RawParser.step, Formula.pullback, formulaEvalWith]
          at incrementalFalse ⊢ <;>
        aesop
  | highUnary count =>
      cases bit <;>
        simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, stateFormula,
          RawParser.step, Formula.pullback, formulaEvalWith]
          at incrementalFalse ⊢ <;>
        aesop
  | lowUnary count =>
      cases bit <;>
        simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, stateFormula,
          RawParser.step, Formula.pullback, formulaEvalWith]
          at incrementalFalse ⊢ <;>
        aesop
  | loopUnary count =>
      cases bit <;>
        simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, stateFormula,
          RawParser.step, Formula.pullback, formulaEvalWith]
          at incrementalFalse ⊢ <;>
        aesop
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          cases bit <;>
            simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
              incrementalAdvanceFormula, advanceFormula, stateFormula,
              RawParser.step, Formula.pullback, formulaEvalWith]
              at incrementalFalse ⊢ <;>
            aesop
      | one first =>
          cases bit <;>
            simp [inputIncrementalAdvanceFormula, inputAdvanceFormula,
              incrementalAdvanceFormula, advanceFormula, stateFormula,
              RawParser.step, Formula.pullback, formulaEvalWith]
              at incrementalFalse ⊢ <;>
            aesop
      | two first second =>
          simpa [inputIncrementalAdvanceFormula, inputAdvanceFormula,
            incrementalAdvanceFormula] using incrementalFalse

/-- A canonically true current predicate and true history-free child combine
to make the corresponding complete child true.  This is the Boolean-oracle
counterpart of `advanceFormula_holds_of_current_incremental`; it is used when
an isolated algebraic event has been refined against the current formula. -/
theorem formulaEvalWith_inputAdvance_true_of_current_incremental_true
    (state : RawParser.State) (bit : Bool)
    (value : HermitianForm → ℚ)
    (current : formulaEvalWith (inputStateFormula state) value = true)
    (incremental : formulaEvalWith
      (inputIncrementalAdvanceFormula state bit) value = true) :
    formulaEvalWith (inputAdvanceFormula state bit) value = true := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simp [inputStateFormula, inputIncrementalAdvanceFormula,
          inputAdvanceFormula, incrementalAdvanceFormula, advanceFormula,
          stateFormula, RawParser.step, Formula.pullback, formulaEvalWith]
            at current incremental ⊢ <;>
        aesop
  | highUnary count =>
      cases bit <;>
        simp [inputStateFormula, inputIncrementalAdvanceFormula,
          inputAdvanceFormula, incrementalAdvanceFormula, advanceFormula,
          stateFormula, RawParser.step, Formula.pullback, formulaEvalWith]
            at current incremental ⊢ <;>
        aesop
  | lowUnary count =>
      cases bit <;>
        simp [inputStateFormula, inputIncrementalAdvanceFormula,
          inputAdvanceFormula, incrementalAdvanceFormula, advanceFormula,
          stateFormula, RawParser.step, Formula.pullback, formulaEvalWith]
            at current incremental ⊢ <;>
        aesop
  | loopUnary count =>
      cases bit <;>
        simp [inputStateFormula, inputIncrementalAdvanceFormula,
          inputAdvanceFormula, incrementalAdvanceFormula, advanceFormula,
          stateFormula, RawParser.step, Formula.pullback, formulaEvalWith]
            at current incremental ⊢ <;>
        aesop
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          cases bit <;>
            simp [inputStateFormula, inputIncrementalAdvanceFormula,
              inputAdvanceFormula, incrementalAdvanceFormula, advanceFormula,
              stateFormula, RawParser.step, Formula.pullback, formulaEvalWith]
                at current incremental ⊢ <;>
            aesop
      | one first =>
          cases bit <;>
            simp [inputStateFormula, inputIncrementalAdvanceFormula,
              inputAdvanceFormula, incrementalAdvanceFormula, advanceFormula,
              stateFormula, RawParser.step, Formula.pullback, formulaEvalWith]
                at current incremental ⊢ <;>
            aesop
      | two first second =>
          simpa [inputIncrementalAdvanceFormula, inputAdvanceFormula,
            incrementalAdvanceFormula] using incremental

/-- The computed owner pair of any parser event is exactly the pair obtained
by evaluating both complete child formulas in its canonical algebraic oracle.
No selected bit or event-family membership is required. -/
theorem inputEventPair_eq_canonical
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    cell.ownerChecks =
      (formulaEvalWith (inputAdvanceFormula state false)
          (inputEventCanonicalValue cell),
        formulaEvalWith (inputAdvanceFormula state true)
          (inputEventCanonicalValue cell)) := by
  change eventFormulaPairCheck cell.branch cell.parent = _
  unfold inputEventCanonicalValue
  exact eventFormulaPairCheck_eq_canonicalPair cell.branch cell.parent

/-- The history-free all-neither table therefore entails the legacy complete
all-neither table, without a represented point or a phase assumption. -/
theorem InputEventCell.ownerChecks_eq_neither_of_incrementalChecks
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (checks : inputEventIncrementalChecks cell = (false, false)) :
    cell.ownerChecks = (false, false) := by
  rw [inputEventPair_eq_canonical]
  apply Prod.ext
  · apply formulaEvalWith_inputAdvance_false_of_incremental_false
    exact congrArg Prod.fst checks
  · apply formulaEvalWith_inputAdvance_false_of_incremental_false
    exact congrArg Prod.snd checks

/-- A complete selected owner also selects the same history-free child.  The
chosen complete child forces its incremental component to be true, while the
incremental table's intrinsic exclusivity forces the other component false. -/
theorem InputEventCell.incrementalChecks_eq_ownerPair_of_ownerChecks
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (bit : Bool)
    (checks : cell.ownerChecks = ownerPair bit) :
    inputEventIncrementalChecks cell = ownerPair bit := by
  have pair := inputEventPair_eq_canonical cell
  have exclusive := inputEventIncrementalChecks_ne_both cell
  cases bitEq : bit with
  | false =>
      have completeTrue : formulaEvalWith (inputAdvanceFormula state false)
          (inputEventCanonicalValue cell) = true := by
        have component := congrArg Prod.fst (pair.symm.trans checks)
        simpa only [bitEq, ownerPair] using component
      have incrementalTrue : (inputEventIncrementalChecks cell).1 = true := by
        cases incrementalEq : (inputEventIncrementalChecks cell).1 with
        | false =>
            have completeFalse :=
              formulaEvalWith_inputAdvance_false_of_incremental_false state
                false (inputEventCanonicalValue cell) incrementalEq
            exact (Bool.false_ne_true
              (completeFalse.symm.trans completeTrue)).elim
        | true => rfl
      have incrementalFalse : (inputEventIncrementalChecks cell).2 = false := by
        cases secondEq : (inputEventIncrementalChecks cell).2 with
        | false => rfl
        | true =>
            exact (exclusive (Prod.ext incrementalTrue secondEq)).elim
      exact Prod.ext incrementalTrue incrementalFalse
  | true =>
      have completeTrue : formulaEvalWith (inputAdvanceFormula state true)
          (inputEventCanonicalValue cell) = true := by
        have component := congrArg Prod.snd (pair.symm.trans checks)
        simpa only [bitEq, ownerPair] using component
      have incrementalTrue : (inputEventIncrementalChecks cell).2 = true := by
        cases incrementalEq : (inputEventIncrementalChecks cell).2 with
        | false =>
            have completeFalse :=
              formulaEvalWith_inputAdvance_false_of_incremental_false state
                true (inputEventCanonicalValue cell) incrementalEq
            exact (Bool.false_ne_true
              (completeFalse.symm.trans completeTrue)).elim
        | true => rfl
      have incrementalFalse : (inputEventIncrementalChecks cell).1 = false := by
        cases firstEq : (inputEventIncrementalChecks cell).1 with
        | false => rfl
        | true =>
            exact (exclusive (Prod.ext firstEq incrementalTrue)).elim
      exact Prod.ext incrementalFalse incrementalTrue

/-- Residual atoms remain nonnegative in every event oracle.  After
homographic pullback and path denominator clearing, the atom is still the
squared norm of one explicit homogeneous affine numerator. -/
theorem inputEventCanonical_residual_nonneg
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) :
    0 ≤ inputEventCanonicalValue cell
      (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
        (residualForm kind exponent sector)) := by
  apply canonicalEventValue_nonneg_of_eval_nonneg
  intro t
  unfold residualForm
  rw [FTA.CCLFormulaPullback.pullbackForm_affineNorm,
    eval_clearedForm_affineNorm]
  exact CCL.GaussianRat.normSq_nonneg _

/-- Exact canonical meaning of an all-`neither` event cell: both complete
child formulas are false at the isolated algebraic event. -/
theorem inputEventCanonical_fails_of_neither
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (checks : cell.ownerChecks = (false, false)) :
    ∀ bit, formulaEvalWith (inputAdvanceFormula state bit)
      (inputEventCanonicalValue cell) = false := by
  have pair := inputEventPair_eq_canonical cell
  rw [checks] at pair
  intro bit
  cases bit with
  | false => exact (congrArg Prod.fst pair).symm
  | true => exact (congrArg Prod.snd pair).symm

/-- Once the parser is in a completed two-bit sector phase, a true current
predicate and two false children force the residual atom of one of the two
candidate sectors to be exactly zero.  The only analytic input is
nonnegativity of the two squared residual atoms. -/
theorem completedSector_residualZero_of_current_neither
    (state : RawParser.State) (value : HermitianForm → ℚ)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (current : formulaEvalWith (inputStateFormula state) value = true)
    (neither : ∀ bit,
      formulaEvalWith (inputAdvanceFormula state bit) value = false)
    (residualNonnegative : ∀ third,
      0 ≤ value (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
        (residualForm kind exponent
          (RawParser.sectorOfBits first second third)))) :
    ∃ third, value
      (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
        (residualForm kind exponent
          (RawParser.sectorOfBits first second third))) = 0 := by
  rcases state with ⟨statePhase, matrix, history⟩
  change statePhase = .sector kind exponent (.two first second) at phase
  subst statePhase
  have falseCheck := neither false
  have trueCheck := neither true
  cases first with
  | false =>
      cases second with
      | false =>
          simp [inputStateFormula, inputAdvanceFormula, advanceFormula,
            stateFormula, activeFormula, radialFormula, sectorBitsFormula,
            sectorFormula, Formula.pullback, formulaEvalWith, Formula.all,
            RawParser.sectorOfBits, SignTest.Holds] at current falseCheck trueCheck
          by_cases split : 0 ≤ value
              (FTA.CCLFormulaPullback.pullbackForm (adjugate matrix)
                (imagComparisonForm
                  (normalizedMatrix kind exponent RawParser.identityMatrix)
                  (2 : ℚ)⁻¹))
          · refine ⟨true, ?_⟩
            have nonnegative := residualNonnegative true
            have nonpositive := trueCheck current.2.1 current.2.2.1 split
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
          · refine ⟨false, ?_⟩
            have negative := lt_of_not_ge split
            have nonnegative := residualNonnegative false
            have nonpositive := falseCheck current.2.1 current.2.2.1
              current.2.2.2 negative
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
      | true =>
          simp [inputStateFormula, inputAdvanceFormula, advanceFormula,
            stateFormula, activeFormula, radialFormula, sectorBitsFormula,
            sectorFormula, Formula.pullback, formulaEvalWith, Formula.all,
            RawParser.sectorOfBits, SignTest.Holds] at current falseCheck trueCheck
          by_cases split : value
              (FTA.CCLFormulaPullback.pullbackForm (adjugate matrix)
                (realComparisonForm
                  (normalizedMatrix kind exponent RawParser.identityMatrix)
                  (-1 / 2))) ≤ 0
          · refine ⟨true, ?_⟩
            have nonnegative := residualNonnegative true
            have nonpositive := trueCheck current.2.1 split current.2.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
          · refine ⟨false, ?_⟩
            have positive := lt_of_not_ge split
            have nonnegative := residualNonnegative false
            have nonpositive := falseCheck current.2.1 positive
              current.2.2.1 current.2.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
  | true =>
      cases second with
      | false =>
          simp [inputStateFormula, inputAdvanceFormula, advanceFormula,
            stateFormula, activeFormula, radialFormula, sectorBitsFormula,
            sectorFormula, Formula.pullback, formulaEvalWith, Formula.all,
            RawParser.sectorOfBits, SignTest.Holds] at current falseCheck trueCheck
          by_cases split : value
              (FTA.CCLFormulaPullback.pullbackForm (adjugate matrix)
                (imagComparisonForm
                  (normalizedMatrix kind exponent RawParser.identityMatrix)
                  (-1 / 2))) ≤ 0
          · refine ⟨true, ?_⟩
            have nonnegative := residualNonnegative true
            have nonpositive := trueCheck current.2.1 current.2.2.1 split
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
          · refine ⟨false, ?_⟩
            have positive := lt_of_not_ge split
            have nonnegative := residualNonnegative false
            have nonpositive := falseCheck current.2.1 current.2.2.1 positive
              current.2.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
      | true =>
          simp [inputStateFormula, inputAdvanceFormula, advanceFormula,
            stateFormula, activeFormula, radialFormula, sectorBitsFormula,
            sectorFormula, Formula.pullback, formulaEvalWith, Formula.all,
            RawParser.sectorOfBits, SignTest.Holds] at current falseCheck trueCheck
          by_cases split : 0 ≤ value
              (FTA.CCLFormulaPullback.pullbackForm (adjugate matrix)
                (realComparisonForm
                  (normalizedMatrix kind exponent RawParser.identityMatrix)
                  (2 : ℚ)⁻¹))
          · refine ⟨true, ?_⟩
            have nonnegative := residualNonnegative true
            have nonpositive := trueCheck current.2.1 split current.2.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
          · refine ⟨false, ?_⟩
            have negative := lt_of_not_ge split
            have nonnegative := residualNonnegative false
            have nonpositive := falseCheck current.2.1 current.2.2.1 negative
              current.2.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative

/-- Event specialization of the completed-sector terminal core.  The event
classifier supplies both false children, and squared-residual nonnegativity
is automatic for its canonical oracle. -/
theorem inputEventCanonical_residualZero_of_completedSector
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (checks : cell.ownerChecks = (false, false))
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (current : formulaEvalWith (inputStateFormula state)
      (inputEventCanonicalValue cell) = true) :
    ∃ third, inputEventCanonicalValue cell
      (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
        (residualForm kind exponent
          (RawParser.sectorOfBits first second third))) = 0 := by
  apply completedSector_residualZero_of_current_neither state
    (inputEventCanonicalValue cell) kind exponent first second phase current
    (inputEventCanonical_fails_of_neither cell checks)
  intro third
  exact inputEventCanonical_residual_nonneg cell kind exponent
    (RawParser.sectorOfBits first second third)

/-- The residual atom of either completed-sector child occurs in the common
two-child polynomial list classified by every input event cell. -/
theorem completedSector_residualPolynomial_mem_inputEvent
    (state : RawParser.State) (path : ProjectivePath.Path)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second third : Bool)
    (phase : state.phase = .sector kind exponent (.two first second)) :
    clearedForm
        (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
          (residualForm kind exponent
            (RawParser.sectorOfBits first second third))) path ∈
      inputEventPolynomials state path := by
  rcases state with ⟨statePhase, matrix, history⟩
  change statePhase = .sector kind exponent (.two first second) at phase
  subst statePhase
  cases first <;> cases second <;> cases third <;>
    simp [inputEventPolynomials, eventFormulaPolynomials,
      inputAdvanceFormula, advanceFormula, Formula.pullback, formulaAtoms,
      RawParser.sectorOfBits]

/-- Canonical terminality is therefore an exact polynomial divisibility
statement: the isolated event factor divides the cleared squared residual of
one completed-sector child. -/
theorem inputEvent_residualPolynomial_dvd_of_completedSector
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (checks : cell.ownerChecks = (false, false))
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (current : formulaEvalWith (inputStateFormula state)
      (inputEventCanonicalValue cell) = true) :
    ∃ third,
      cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm
          (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
            (residualForm kind exponent
              (RawParser.sectorOfBits first second third))) path).toPolynomial := by
  rcases inputEventCanonical_residualZero_of_completedSector cell checks kind
      exponent first second phase current with ⟨third, residualZero⟩
  refine ⟨third, ConditionRelations.dvd_of_canonicalEventValue_eq_zero
    cell.branch.relations cell.parent
      (cell.branch.computeEventSigns cell.parent)
      (completedSector_residualPolynomial_mem_inputEvent state path kind
        exponent first second third phase) ?_⟩
  simpa only [inputEventCanonicalValue] using residualZero

/-- Canonical value of one Hermitian atom at the selected algebraic event. -/
def selectedEventCanonicalValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) (form : HermitianForm) : ℚ :=
  canonicalEventValue selected.candidate.inputCell.branch.factor.input
    (clearedForm form
      selected.candidate.sourceEvent.partition.entry.chart.path)
    (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined.interval.lower

/-- Active selected child boundaries, oriented toward the chosen bit. -/
def selectedActiveOwnerForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) : List HermitianForm :=
  activeOwnerForms (inputAdvanceFormula state selected.bit)
    (selectedEventCanonicalValue selected)

/-- Strict selected child forms whose canonical signs must be preserved. -/
def selectedStrictPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) : List HermitianForm :=
  strictPriorForms (inputAdvanceFormula state selected.bit)
    (selectedEventCanonicalValue selected)

/-- Active faces belonging only to the new phase predicate.  Historical
constraints are deliberately absent: the coupled state preserves them through
its strict prior neighbourhood. -/
def selectedIncrementalActiveOwnerForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) : List HermitianForm :=
  activeOwnerForms
    (inputIncrementalAdvanceFormula state selected.bit)
    (selectedEventCanonicalValue selected)

/-- Canonically strict forms in the new phase predicate. -/
def selectedIncrementalStrictPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) : List HermitianForm :=
  strictPriorForms
    (inputIncrementalAdvanceFormula state selected.bit)
    (selectedEventCanonicalValue selected)

theorem selectedIncrementalActiveOwnerForms_eq_selectedActiveOwnerForms_of_completedSector
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second)) :
    selectedIncrementalActiveOwnerForms selected =
      selectedActiveOwnerForms selected := by
  simp only [selectedIncrementalActiveOwnerForms, selectedActiveOwnerForms,
    inputIncrementalAdvanceFormula_eq_inputAdvanceFormula_of_completedSector
      state selected.bit phase]

theorem selectedIncrementalStrictPriorForms_eq_selectedStrictPriorForms_of_completedSector
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second)) :
    selectedIncrementalStrictPriorForms selected =
      selectedStrictPriorForms selected := by
  simp only [selectedIncrementalStrictPriorForms, selectedStrictPriorForms,
    inputIncrementalAdvanceFormula_eq_inputAdvanceFormula_of_completedSector
      state selected.bit phase]

/-- Both controller truth-table entries are the corresponding child formulas
evaluated through the selected event's canonical oracle. -/
theorem selectedEventPair_eq_canonical
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) :
    selected.candidate.inputCell.ownerChecks =
      (formulaEvalWith (inputAdvanceFormula state false)
          (selectedEventCanonicalValue selected),
        formulaEvalWith (inputAdvanceFormula state true)
          (selectedEventCanonicalValue selected)) := by
  change eventFormulaPairCheck selected.candidate.inputCell.branch
      selected.candidate.inputCell.parent = _
  unfold selectedEventCanonicalValue
  exact eventFormulaPairCheck_eq_canonicalPair
    selected.candidate.inputCell.branch
    selected.candidate.inputCell.parent

/-- The selected next-bit formula is true at the algebraic event oracle even
when the event parameter has no rational zero. -/
theorem selectedEventCanonical_holds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) :
    formulaEvalWith (inputAdvanceFormula state selected.bit)
      (selectedEventCanonicalValue selected) = true := by
  have pair := selectedEventPair_eq_canonical selected
  cases bitEq : selected.bit with
  | false =>
      have component := congrArg Prod.fst pair
      have check : selected.candidate.inputCell.ownerChecks.1 = true := by
        simpa only [bitEq, Bool.not_false] using selected.falseCheck
      simpa only [bitEq] using component.symm.trans check
  | true =>
      have component := congrArg Prod.snd pair
      have check : selected.candidate.inputCell.ownerChecks.2 = true := by
        simpa only [bitEq] using selected.trueCheck
      simpa only [bitEq] using component.symm.trans check

/-- The same canonical owner decision satisfies the history-free incremental
predicate.  In ordinary phases this is the active-form component of the full
child formula; on a third sector bit the two formulas coincide. -/
theorem selectedIncrementalEventCanonical_holds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) :
    formulaEvalWith
      (inputIncrementalAdvanceFormula state selected.bit)
      (selectedEventCanonicalValue selected) = true := by
  have complete := selectedEventCanonical_holds selected
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bitEq : selected.bit <;>
        simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
        exact complete.2
  | highUnary count =>
      cases bitEq : selected.bit <;>
        simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
        exact complete.2
  | lowUnary count =>
      cases bitEq : selected.bit <;>
        simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
        exact complete.2
  | loopUnary count =>
      cases bitEq : selected.bit <;>
        simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
        exact complete.2
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          cases bitEq : selected.bit <;>
            simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
              incrementalAdvanceFormula, advanceFormula, Formula.pullback,
              stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
            exact complete.2
      | one first =>
          cases bitEq : selected.bit <;>
            simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
              incrementalAdvanceFormula, advanceFormula, Formula.pullback,
              stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
            exact complete.2
      | two first second =>
          simpa [inputIncrementalAdvanceFormula, inputAdvanceFormula,
            incrementalAdvanceFormula] using complete
/-- The opposite next-bit formula is false at the same canonical event
oracle, recording the complete deterministic owner decision. -/
theorem otherEventCanonical_fails
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) :
    formulaEvalWith (inputAdvanceFormula state (!selected.bit))
      (selectedEventCanonicalValue selected) = false := by
  have pair := selectedEventPair_eq_canonical selected
  cases bitEq : selected.bit with
  | false =>
      have component := congrArg Prod.snd pair
      have check : selected.candidate.inputCell.ownerChecks.2 = false := by
        simpa only [bitEq] using selected.trueCheck
      simpa only [bitEq, Bool.not_false] using component.symm.trans check
  | true =>
      have component := congrArg Prod.fst pair
      have check : selected.candidate.inputCell.ownerChecks.1 = false := by
        simpa only [bitEq, Bool.not_true] using selected.falseCheck
      simpa only [bitEq, Bool.not_true] using component.symm.trans check

/-- Any rational point reproducing the selected formula's finite canonical
atom outcomes satisfies the genuine input-coordinate child formula. -/
theorem selectedEvent_holds_of_atomTests
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) (point : QI)
    (agree : ∀ atom ∈ formulaAtoms
        (inputAdvanceFormula state selected.bit),
      (atom.sign.Holds (selectedEventCanonicalValue selected atom.form) ↔
        atom.Holds point)) :
    (inputAdvanceFormula state selected.bit).Holds point := by
  have evaluationAgreement := formulaEvalWith_eq_of_atomTests
    (inputAdvanceFormula state selected.bit)
    (selectedEventCanonicalValue selected) (fun form => form.eval point) (by
      intro atom member
      simpa only [Atom.Holds] using agree atom member)
  apply (formulaEvalWith_eval_eq_true_iff
    (inputAdvanceFormula state selected.bit) point).mp
  rw [← evaluationAgreement]
  exact selectedEventCanonical_holds selected

/-- Sharper selected-event transfer: only the atoms in the canonical true
branch need to hold at the rational perturbation. -/
theorem selectedEvent_holds_of_satisfyingAtoms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) (point : QI)
    (atomsHold : ∀ atom ∈ satisfyingAtoms
        (inputAdvanceFormula state selected.bit)
        (selectedEventCanonicalValue selected), atom.Holds point) :
    (inputAdvanceFormula state selected.bit).Holds point :=
  formula_holds_of_satisfyingAtoms
    (inputAdvanceFormula state selected.bit)
    (selectedEventCanonicalValue selected) point
    (selectedEventCanonical_holds selected) atomsHold

/-- Final selected-event realization interface for the bounded grid: enter
the finitely many active oriented weak sides and preserve the signs of the
finitely many strict canonical atoms. -/
theorem selectedEvent_holds_of_active_strict
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) (point : QI)
    (activePositive : ∀ atom ∈ activeSatisfyingAtoms
        (inputAdvanceFormula state selected.bit)
        (selectedEventCanonicalValue selected),
      0 < (orientedWeakForm atom).eval point)
    (strictSameSign : ∀ atom ∈ strictSatisfyingAtoms
        (inputAdvanceFormula state selected.bit)
        (selectedEventCanonicalValue selected),
      0 < selectedEventCanonicalValue selected atom.form *
        atom.form.eval point) :
    (inputAdvanceFormula state selected.bit).Holds point := by
  apply formula_holds_of_active_strict
    (inputAdvanceFormula state selected.bit)
    (selectedEventCanonicalValue selected) point
    (selectedEventCanonical_holds selected)
    (satisfyingAtoms_noZeroTest
      (inputAdvanceFormula state selected.bit)
      (selectedEventCanonicalValue selected)
      (inputAdvanceFormula_noZeroTests state selected.bit))
    activePositive strictSameSign

theorem selectedEvent_holds_of_owner_form_lists
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) (point : QI)
    (activePositive : ∀ form ∈ selectedActiveOwnerForms selected,
      0 < form.eval point)
    (strictSameSign : ∀ form ∈ selectedStrictPriorForms selected,
      0 < selectedEventCanonicalValue selected form * form.eval point) :
    (inputAdvanceFormula state selected.bit).Holds point := by
  exact formula_holds_of_owner_form_lists
    (inputAdvanceFormula state selected.bit)
    (selectedEventCanonicalValue selected) point
    (selectedEventCanonical_holds selected)
    (inputAdvanceFormula_noZeroTests state selected.bit)
    activePositive strictSameSign

/-- Realization interface for the genuinely new phase predicate.  Combining
this result with a stable represented old prefix extends the raw word without
reintroducing any historical owner face. -/
theorem selectedIncrementalEvent_holds_of_owner_form_lists
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) (point : QI)
    (activePositive :
      ∀ form ∈ selectedIncrementalActiveOwnerForms selected,
        0 < form.eval point)
    (strictSameSign :
      ∀ form ∈ selectedIncrementalStrictPriorForms selected,
        0 < selectedEventCanonicalValue selected form * form.eval point) :
    (inputIncrementalAdvanceFormula state selected.bit).Holds point := by
  exact formula_holds_of_owner_form_lists
    (inputIncrementalAdvanceFormula state selected.bit)
    (selectedEventCanonicalValue selected) point
    (selectedIncrementalEventCanonical_holds selected)
    (inputIncrementalAdvanceFormula_noZeroTests state selected.bit)
    activePositive strictSameSign

/-! ## Common global/guarded selected-event semantics -/

/-- Shared payload for every history-free owner.  This is the exact evidence
used by the incremental tangent, localization, and grid constructions; it
does not assume that the current historical formula is true at the event. -/
structure IncrementalEventPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) where
  candidate : SelectedEventCandidate p output.state.box state
  bit : Bool
  checks : inputEventIncrementalChecks candidate.inputCell = ownerPair bit
  decision : CurveEventCountDecision p
    candidate.sourceEvent.partition.entry.chart.path output.state.box
    candidate.sourceEvent.event
  sourceMember : candidate.sourceEvent.partition.entry.source ∈ inputPlan state

/-- The chosen history-free child is true in the payload's event oracle. -/
theorem IncrementalEventPayload.selectedCanonical_holds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : IncrementalEventPayload output) :
    formulaEvalWith (inputIncrementalAdvanceFormula state selected.bit)
      (inputEventCanonicalValue selected.candidate.inputCell) = true := by
  cases bitEq : selected.bit with
  | false =>
      have component := congrArg Prod.fst selected.checks
      simpa only [inputEventIncrementalChecks, bitEq, ownerPair] using component
  | true =>
      have component := congrArg Prod.snd selected.checks
      simpa only [inputEventIncrementalChecks, bitEq, ownerPair] using component

/-- The opposite history-free child is false in the same event oracle. -/
theorem IncrementalEventPayload.otherCanonical_fails
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : IncrementalEventPayload output) :
    formulaEvalWith (inputIncrementalAdvanceFormula state (!selected.bit))
      (inputEventCanonicalValue selected.candidate.inputCell) = false := by
  cases bitEq : selected.bit with
  | false =>
      have component := congrArg Prod.snd selected.checks
      simpa only [inputEventIncrementalChecks, bitEq, ownerPair,
        Bool.not_false] using component
  | true =>
      have component := congrArg Prod.fst selected.checks
      simpa only [inputEventIncrementalChecks, bitEq, ownerPair,
        Bool.not_true] using component

/-- Forget the historical component of a complete owner while retaining the
same candidate, bit, curve-count decision, and finite-plan provenance. -/
def _root_.FTA.CCLBranchController.SelectedEventPayload.toIncrementalPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : IncrementalEventPayload output :=
  { candidate := selected.candidate
    bit := selected.bit
    checks := InputEventCell.incrementalChecks_eq_ownerPair_of_ownerChecks
      selected.candidate.inputCell selected.bit selected.checks
    decision := selected.decision
    sourceMember := selected.sourceMember }

@[simp] theorem toIncrementalPayload_candidate
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : SelectedEventPayload output) :
    selected.toIncrementalPayload.candidate = selected.candidate := rfl

@[simp] theorem toIncrementalPayload_bit
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : SelectedEventPayload output) :
    selected.toIncrementalPayload.bit = selected.bit := rfl

instance
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} :
    Coe (SelectedEventPayload output) (IncrementalEventPayload output) :=
  ⟨FTA.CCLBranchController.SelectedEventPayload.toIncrementalPayload⟩

/-- Canonical atom value exposed through the common selected-event payload. -/
def eventPayloadCanonicalValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (form : HermitianForm) : ℚ :=
  canonicalEventValue selected.candidate.inputCell.branch.factor.input
    (clearedForm form
      selected.candidate.sourceEvent.partition.entry.chart.path)
    (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined.interval.lower

theorem IncrementalEventPayload.canonical_holds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : IncrementalEventPayload output) :
    formulaEvalWith (inputIncrementalAdvanceFormula state selected.bit)
      (eventPayloadCanonicalValue selected) = true := by
  change formulaEvalWith (inputIncrementalAdvanceFormula state selected.bit)
    (inputEventCanonicalValue selected.candidate.inputCell) = true
  exact selected.selectedCanonical_holds

def eventPayloadActiveOwnerForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
  (selected : SelectedEventPayload output) : List HermitianForm :=
  activeOwnerForms (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue
      (SelectedEventPayload.toIncrementalPayload selected))

def eventPayloadStrictPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
  (selected : SelectedEventPayload output) : List HermitianForm :=
  strictPriorForms (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue
      (SelectedEventPayload.toIncrementalPayload selected))

def eventPayloadIncrementalActiveOwnerForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : List HermitianForm :=
  activeOwnerForms (inputIncrementalAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected)

def eventPayloadIncrementalStrictPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : List HermitianForm :=
  strictPriorForms (inputIncrementalAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected)

theorem eventPayloadIncrementalActiveOwnerForms_eq_active_of_completedSector
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second)) :
    eventPayloadIncrementalActiveOwnerForms
        (selected : IncrementalEventPayload output) =
      eventPayloadActiveOwnerForms selected := by
  simp only [eventPayloadIncrementalActiveOwnerForms,
    eventPayloadActiveOwnerForms,
    SelectedEventPayload.toIncrementalPayload,
    inputIncrementalAdvanceFormula_eq_inputAdvanceFormula_of_completedSector
      state selected.bit phase]

theorem eventPayloadIncrementalStrictPriorForms_eq_strict_of_completedSector
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second)) :
    eventPayloadIncrementalStrictPriorForms
        (selected : IncrementalEventPayload output) =
      eventPayloadStrictPriorForms selected := by
  simp only [eventPayloadIncrementalStrictPriorForms,
    eventPayloadStrictPriorForms,
    SelectedEventPayload.toIncrementalPayload,
    inputIncrementalAdvanceFormula_eq_inputAdvanceFormula_of_completedSector
      state selected.bit phase]

/-- The common payload's truth-table pair is its canonical formula pair. -/
theorem eventPayloadPair_eq_canonical
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    selected.candidate.inputCell.ownerChecks =
      (formulaEvalWith (inputAdvanceFormula state false)
          (eventPayloadCanonicalValue selected.toIncrementalPayload),
        formulaEvalWith (inputAdvanceFormula state true)
          (eventPayloadCanonicalValue selected.toIncrementalPayload)) := by
  change eventFormulaPairCheck selected.candidate.inputCell.branch
      selected.candidate.inputCell.parent = _
  unfold eventPayloadCanonicalValue
  exact eventFormulaPairCheck_eq_canonicalPair
    selected.candidate.inputCell.branch selected.candidate.inputCell.parent

theorem eventPayloadCanonical_holds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    formulaEvalWith (inputAdvanceFormula state selected.bit)
      (eventPayloadCanonicalValue selected.toIncrementalPayload) = true := by
  have pair := eventPayloadPair_eq_canonical selected
  cases bitEq : selected.bit with
  | false =>
      have component := congrArg Prod.fst pair
      have check : selected.candidate.inputCell.ownerChecks.1 = true := by
        simpa only [bitEq, Bool.not_false] using selected.falseCheck
      simpa only [bitEq] using component.symm.trans check
  | true =>
      have component := congrArg Prod.snd pair
      have check : selected.candidate.inputCell.ownerChecks.2 = true := by
        simpa only [bitEq] using selected.trueCheck
      simpa only [bitEq] using component.symm.trans check

theorem eventPayloadIncrementalCanonical_holds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    formulaEvalWith (inputIncrementalAdvanceFormula state selected.bit)
      (eventPayloadCanonicalValue selected.toIncrementalPayload) = true := by
  have complete := eventPayloadCanonical_holds selected
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bitEq : selected.bit <;>
        simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
        exact complete.2
  | highUnary count =>
      cases bitEq : selected.bit <;>
        simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
        exact complete.2
  | lowUnary count =>
      cases bitEq : selected.bit <;>
        simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
        exact complete.2
  | loopUnary count =>
      cases bitEq : selected.bit <;>
        simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
          incrementalAdvanceFormula, advanceFormula, Formula.pullback,
          stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
        exact complete.2
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          cases bitEq : selected.bit <;>
            simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
              incrementalAdvanceFormula, advanceFormula, Formula.pullback,
              stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
            exact complete.2
      | one first =>
          cases bitEq : selected.bit <;>
            simp [bitEq, inputIncrementalAdvanceFormula, inputAdvanceFormula,
              incrementalAdvanceFormula, advanceFormula, Formula.pullback,
              stateFormula, RawParser.step, formulaEvalWith] at complete ⊢ <;>
            exact complete.2
      | two first second =>
          simpa [inputIncrementalAdvanceFormula, inputAdvanceFormula,
            incrementalAdvanceFormula] using complete

theorem otherEventPayloadCanonical_fails
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    formulaEvalWith (inputAdvanceFormula state (!selected.bit))
      (eventPayloadCanonicalValue selected.toIncrementalPayload) = false := by
  have pair := eventPayloadPair_eq_canonical selected
  cases bitEq : selected.bit with
  | false =>
      have component := congrArg Prod.snd pair
      have check : selected.candidate.inputCell.ownerChecks.2 = false := by
        simpa only [bitEq] using selected.trueCheck
      simpa only [bitEq, Bool.not_false] using component.symm.trans check
  | true =>
      have component := congrArg Prod.fst pair
      have check : selected.candidate.inputCell.ownerChecks.1 = false := by
        simpa only [bitEq, Bool.not_true] using selected.falseCheck
      simpa only [bitEq, Bool.not_true] using component.symm.trans check

theorem eventPayload_holds_of_atomTests
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (point : QI)
    (agree : ∀ atom ∈ formulaAtoms
        (inputAdvanceFormula state selected.bit),
      (atom.sign.Holds
          (eventPayloadCanonicalValue selected.toIncrementalPayload atom.form) ↔
        atom.Holds point)) :
    (inputAdvanceFormula state selected.bit).Holds point := by
  have evaluationAgreement := formulaEvalWith_eq_of_atomTests
    (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected.toIncrementalPayload)
      (fun form => form.eval point) (by
      intro atom member
      simpa only [Atom.Holds] using agree atom member)
  apply (formulaEvalWith_eval_eq_true_iff
    (inputAdvanceFormula state selected.bit) point).mp
  rw [← evaluationAgreement]
  exact eventPayloadCanonical_holds selected

theorem eventPayload_holds_of_satisfyingAtoms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (point : QI)
    (atomsHold : ∀ atom ∈ satisfyingAtoms
        (inputAdvanceFormula state selected.bit)
        (eventPayloadCanonicalValue selected.toIncrementalPayload),
      atom.Holds point) :
    (inputAdvanceFormula state selected.bit).Holds point :=
  formula_holds_of_satisfyingAtoms
    (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected.toIncrementalPayload) point
    (eventPayloadCanonical_holds selected) atomsHold

theorem eventPayload_holds_of_active_strict
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (point : QI)
    (activePositive : ∀ atom ∈ activeSatisfyingAtoms
        (inputAdvanceFormula state selected.bit)
        (eventPayloadCanonicalValue selected.toIncrementalPayload),
      0 < (orientedWeakForm atom).eval point)
    (strictSameSign : ∀ atom ∈ strictSatisfyingAtoms
        (inputAdvanceFormula state selected.bit)
        (eventPayloadCanonicalValue selected.toIncrementalPayload),
      0 < eventPayloadCanonicalValue selected.toIncrementalPayload atom.form *
        atom.form.eval point) :
    (inputAdvanceFormula state selected.bit).Holds point := by
  apply formula_holds_of_active_strict
    (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected.toIncrementalPayload) point
    (eventPayloadCanonical_holds selected)
    (satisfyingAtoms_noZeroTest
      (inputAdvanceFormula state selected.bit)
      (eventPayloadCanonicalValue selected.toIncrementalPayload)
      (inputAdvanceFormula_noZeroTests state selected.bit))
    activePositive strictSameSign

theorem eventPayload_holds_of_owner_form_lists
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (point : QI)
    (activePositive : ∀ form ∈ eventPayloadActiveOwnerForms selected,
      0 < form.eval point)
    (strictSameSign : ∀ form ∈ eventPayloadStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected.toIncrementalPayload form *
        form.eval point) :
    (inputAdvanceFormula state selected.bit).Holds point := by
  exact formula_holds_of_owner_form_lists
    (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected.toIncrementalPayload) point
    (eventPayloadCanonical_holds selected)
    (inputAdvanceFormula_noZeroTests state selected.bit)
    activePositive strictSameSign

theorem eventPayloadIncremental_holds_of_owner_form_lists
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (point : QI)
    (activePositive :
      ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
        0 < form.eval point)
    (strictSameSign :
      ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
        0 < eventPayloadCanonicalValue selected form * form.eval point) :
    (inputIncrementalAdvanceFormula state selected.bit).Holds point := by
  exact formula_holds_of_owner_form_lists
    (inputIncrementalAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected) point
    (by
      change formulaEvalWith
        (inputIncrementalAdvanceFormula state selected.bit)
          (inputEventCanonicalValue selected.candidate.inputCell) = true
      exact selected.selectedCanonical_holds)
    (inputIncrementalAdvanceFormula_noZeroTests state selected.bit)
    activePositive strictSameSign

/-! The legacy global interface is definitionally the global projection of
the common payload.  These equations let dependent downstream records migrate
without re-proving any semantic fact. -/

theorem selectedEventCanonicalValue_eq_payload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) (form : HermitianForm) :
    selectedEventCanonicalValue selected form =
      eventPayloadCanonicalValue selected.toPayload.toIncrementalPayload form :=
  rfl

theorem selectedActiveOwnerForms_eq_payload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) :
    selectedActiveOwnerForms selected =
      eventPayloadActiveOwnerForms selected.toPayload := rfl

theorem selectedStrictPriorForms_eq_payload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) :
    selectedStrictPriorForms selected =
      eventPayloadStrictPriorForms selected.toPayload := rfl

theorem selectedIncrementalActiveOwnerForms_eq_payload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) :
    selectedIncrementalActiveOwnerForms selected =
      eventPayloadIncrementalActiveOwnerForms
        selected.toPayload.toIncrementalPayload := rfl

theorem selectedIncrementalStrictPriorForms_eq_payload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output) :
    selectedIncrementalStrictPriorForms selected =
      eventPayloadIncrementalStrictPriorForms
        selected.toPayload.toIncrementalPayload := rfl

end CCLPositiveEventSemantics
end FTA
