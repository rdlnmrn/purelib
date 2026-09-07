import FTA.CCLIncrementalOwnerShapes

/-!
# Shapes of complete parser owner faces

The complete next-bit formula contains both the newly introduced phase
predicate and every retained historical block.  This module proves that the
weak boundary atoms of those historical constraints are nondegenerate for
states produced by the finite raw parser.  It then transports the result
through the current decoder's adjugate to the original root coordinate.
-/

namespace FTA
namespace CCLCompleteOwnerShapes

open CCL CCL.GaussianRat
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLBranchPlan
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLIncrementalOwnerShapes
open FTA.CCLNextBitFormula
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventSemantics
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Every retained historical constraint has an invertible homography. -/
def HistoryMatricesInvertible (state : RawParser.State) : Prop :=
  ∀ constraint ∈ state.history, determinant constraint.matrix ≠ 0

theorem historyMatricesInvertible_initial :
    HistoryMatricesInvertible RawParser.initialState := by
  simp [HistoryMatricesInvertible, RawParser.initialState]

/-- One parser bit preserves invertibility of every retained historical
homography, including precomposition when a block completes. -/
theorem historyMatricesInvertible_step
    (state : RawParser.State) (bit : Bool)
    (valid : HistoryMatricesInvertible state) :
    HistoryMatricesInvertible (RawParser.step state bit) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simpa [RawParser.step, HistoryMatricesInvertible] using valid
  | highUnary count =>
      cases bit <;>
        simpa [RawParser.step, HistoryMatricesInvertible] using valid
  | lowUnary count =>
      cases bit <;>
        simpa [RawParser.step, HistoryMatricesInvertible] using valid
  | loopUnary count =>
      cases bit <;>
        simpa [RawParser.step, HistoryMatricesInvertible] using valid
  | sector kind exponent bits =>
      cases bits with
      | zero => simpa [RawParser.step, HistoryMatricesInvertible] using valid
      | one first =>
          simpa [RawParser.step, HistoryMatricesInvertible] using valid
      | two first second =>
          let sector := RawParser.sectorOfBits first second bit
          let block := RawParser.blockMatrix kind exponent sector
          have blockDeterminant : determinant block ≠ 0 := by
            simpa only [determinant, Mat2.det, block, sector] using
              RawParser.blockMatrix_det_ne kind exponent sector
          intro constraint member
          change constraint ∈
              (⟨block, kind, exponent, sector⟩ : RawParser.Constraint) ::
                history.map (fun item => item.precompose block) at member
          rcases List.mem_cons.mp member with newest | previous
          · subst constraint
            exact blockDeterminant
          · rcases List.mem_map.mp previous with
              ⟨prior, priorMember, rfl⟩
            change determinant (Mat2.mul prior.matrix block) ≠ 0
            rw [determinant_mul]
            exact mul_ne_zero (valid prior priorMember) blockDeterminant

/-- Every constraint matrix stored by a finite parser run is invertible. -/
theorem parse_historyMatricesInvertible (word : Prefix.Word) :
    HistoryMatricesInvertible (RawParser.parse word) := by
  induction word using List.reverseRecOn with
  | nil => exact historyMatricesInvertible_initial
  | append_singleton word bit inductionHypothesis =>
      rw [RawParser.parse, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact historyMatricesInvertible_step (RawParser.parse word) bit
        inductionHypothesis

/-- Normalization preserves invertibility for an arbitrary historical
homography, not only for the identity matrix used by the active phase. -/
theorem normalizedMatrix_determinant_ne_of
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (matrixDeterminant : determinant matrix ≠ 0) :
    determinant (normalizedMatrix kind exponent matrix) ≠ 0 := by
  have identityNormalized := normalizedMatrix_determinant_ne kind exponent
  rw [normalizedMatrix, determinant_mul] at identityNormalized ⊢
  exact mul_ne_zero (left_ne_zero_of_mul identityNormalized)
    matrixDeterminant

/-- Every weak face of one retained completed-block constraint is a genuine
circle or line when its historical homography is invertible. -/
theorem constraintFormula_weakAtomsNondegenerate
    (constraint : RawParser.Constraint)
    (matrixDeterminant : determinant constraint.matrix ≠ 0) :
    WeakAtomsNondegenerate (constraintFormula constraint) := by
  exact (weakAtomsNondegenerate_atom_strict _ _ (by simp)).and
    ((radialFormula_weakAtomsNondegenerate constraint.kind constraint.exponent
      constraint.matrix matrixDeterminant).and
      (sectorFormula_weakAtomsNondegenerate constraint.sector
        (normalizedMatrix constraint.kind constraint.exponent
          constraint.matrix)
        (normalizedMatrix_determinant_ne_of constraint.kind
          constraint.exponent constraint.matrix matrixDeterminant)))

theorem weakAtomsNondegenerate_all
    (formulas : List Formula)
    (each : ∀ formula ∈ formulas, WeakAtomsNondegenerate formula) :
    WeakAtomsNondegenerate (Formula.all formulas) := by
  induction formulas with
  | nil => exact weakAtomsNondegenerate_truth
  | cons formula formulas inductionHypothesis =>
      apply WeakAtomsNondegenerate.and
      · exact each formula (by simp)
      · apply inductionHypothesis
        intro item member
        exact each item (by simp [member])

/-- The complete formula of any state with valid history has only
nondegenerate weak atoms. -/
theorem stateFormula_weakAtomsNondegenerate
    (state : RawParser.State) (historyValid : HistoryMatricesInvertible state) :
    WeakAtomsNondegenerate (stateFormula state) := by
  apply WeakAtomsNondegenerate.and
  · apply weakAtomsNondegenerate_all
    intro formula member
    rcases List.mem_map.mp member with ⟨constraint, constraintMember, rfl⟩
    exact constraintFormula_weakAtomsNondegenerate constraint
      (historyValid constraint constraintMember)
  · exact activeFormula_weakAtomsNondegenerate state.phase

/-- Every active owner selected from the complete current-state formula is a
genuine circle or line when the retained parser history is valid. -/
theorem stateActiveOwner_boundaryDiscriminant_ne
    (state : RawParser.State)
    (historyValid : HistoryMatricesInvertible state)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (stateFormula state) value = true)
    {form : HermitianForm}
    (member : form ∈ activeOwnerForms (stateFormula state) value) :
    boundaryDiscriminant form ≠ 0 := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  rw [boundaryDiscriminant_orientedWeakForm]
  apply stateFormula_weakAtomsNondegenerate state historyValid atom
  · exact satisfyingAtoms_mem_formulaAtoms _ _
      (activeSatisfyingAtoms_source atomMember)
  · apply activeSatisfyingAtom_sign_weak evaluation
      (satisfyingAtoms_noZeroTest _ _ (stateFormula_noZeroTests state))
    exact atomMember

/-- Pulling a current-state active owner through an invertible decoder
preserves nondegeneracy. -/
theorem inputStateActiveOwner_boundaryDiscriminant_ne
    (state : RawParser.State)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible state)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (inputStateFormula state) value = true)
    {form : HermitianForm}
    (member : form ∈ activeOwnerForms (inputStateFormula state) value) :
    boundaryDiscriminant form ≠ 0 := by
  rw [inputStateFormula, activeOwnerForms_pullback] at member
  rcases List.mem_map.mp member with ⟨localForm, localMember, rfl⟩
  have localEvaluation : formulaEvalWith (stateFormula state)
      (fun item => value (pullbackForm (adjugate state.matrix) item)) =
        true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  have localNondegenerate := stateActiveOwner_boundaryDiscriminant_ne state
    historyValid _ localEvaluation localMember
  rw [boundaryDiscriminant_pullbackForm]
  exact mul_ne_zero
    (normSq_pos (by
      rw [determinant_adjugate]
      exact stateDeterminant)).ne'
    localNondegenerate

/-- A complete proposed child of a state with valid history has only
nondegenerate weak atoms.  A completed sector is handled directly by its
local formula; every other phase uses the next state's preserved history. -/
theorem advanceFormula_weakAtomsNondegenerate
    (state : RawParser.State) (bit : Bool)
    (historyValid : HistoryMatricesInvertible state) :
    WeakAtomsNondegenerate (advanceFormula state bit) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      exact stateFormula_weakAtomsNondegenerate _
        (historyMatricesInvertible_step _ bit historyValid)
  | highUnary count =>
      exact stateFormula_weakAtomsNondegenerate _
        (historyMatricesInvertible_step _ bit historyValid)
  | lowUnary count =>
      exact stateFormula_weakAtomsNondegenerate _
        (historyMatricesInvertible_step _ bit historyValid)
  | loopUnary count =>
      exact stateFormula_weakAtomsNondegenerate _
        (historyMatricesInvertible_step _ bit historyValid)
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          exact stateFormula_weakAtomsNondegenerate _
            (historyMatricesInvertible_step _ bit historyValid)
      | one first =>
          exact stateFormula_weakAtomsNondegenerate _
            (historyMatricesInvertible_step _ bit historyValid)
      | two first second =>
          exact completedSectorAdvance_weakAtomsNondegenerate kind exponent
            first second bit matrix history

/-- Every active owner selected from a complete affine child formula is
nondegenerate when the parser history is valid. -/
theorem advanceActiveOwner_boundaryDiscriminant_ne
    (state : RawParser.State) (bit : Bool)
    (historyValid : HistoryMatricesInvertible state)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (advanceFormula state bit) value = true)
    {form : HermitianForm}
    (member : form ∈ activeOwnerForms (advanceFormula state bit) value) :
    boundaryDiscriminant form ≠ 0 := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  rw [boundaryDiscriminant_orientedWeakForm]
  apply advanceFormula_weakAtomsNondegenerate state bit historyValid atom
  · exact satisfyingAtoms_mem_formulaAtoms _ _
      (activeSatisfyingAtoms_source atomMember)
  · apply activeSatisfyingAtom_sign_weak evaluation
      (satisfyingAtoms_noZeroTest _ _
        (advanceFormula_noZeroTests state bit))
    exact atomMember

/-- Pulling a complete active owner through an invertible decoder preserves
its nondegenerate boundary. -/
theorem inputAdvanceActiveOwner_boundaryDiscriminant_ne
    (state : RawParser.State) (bit : Bool)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible state)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (inputAdvanceFormula state bit) value = true)
    {form : HermitianForm}
    (member : form ∈ activeOwnerForms (inputAdvanceFormula state bit) value) :
    boundaryDiscriminant form ≠ 0 := by
  rw [inputAdvanceFormula, activeOwnerForms_pullback] at member
  rcases List.mem_map.mp member with ⟨localForm, localMember, rfl⟩
  have localEvaluation :
      formulaEvalWith (advanceFormula state bit)
        (fun item => value (pullbackForm (adjugate state.matrix) item)) =
          true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  have localNondegenerate := advanceActiveOwner_boundaryDiscriminant_ne state
    bit historyValid _ localEvaluation localMember
  rw [boundaryDiscriminant_pullbackForm]
  exact mul_ne_zero
    (normSq_pos (by
      rw [determinant_adjugate]
      exact stateDeterminant)).ne'
    localNondegenerate

/-- Selected active faces of the complete child formula are nondegenerate for
every state whose decoder and retained history are invertible. -/
theorem selectedCompleteActiveOwner_boundaryDiscriminant_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible state)
    {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    boundaryDiscriminant form ≠ 0 := by
  exact inputAdvanceActiveOwner_boundaryDiscriminant_ne state selected.bit
    stateDeterminant historyValid
    (eventPayloadCanonicalValue selected.toIncrementalPayload)
    (eventPayloadCanonical_holds selected) member

/-- In particular, every complete owner face selected from an actual parsed
word has a nondegenerate boundary. -/
theorem selectedParsedCompleteActiveOwner_boundaryDiscriminant_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    boundaryDiscriminant form ≠ 0 := by
  apply selectedCompleteActiveOwner_boundaryDiscriminant_ne selected
  · simpa only [determinant, Mat2.det] using RawParser.parse_det_ne word
  · exact parse_historyMatricesInvertible word
  · exact member

end CCLCompleteOwnerShapes
end FTA
