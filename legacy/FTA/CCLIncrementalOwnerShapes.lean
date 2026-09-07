import FTA.CCLPositiveEventSemantics

/-!
# Shapes of incremental parser owner faces

Every weak boundary atom introduced by one raw parser transition is a
nondegenerate pulled-back circle or line.  The proof is compositional over
formula syntax and keeps the finite sector enumeration separate from the
selected-event algebra.
-/

namespace FTA
namespace CCLIncrementalOwnerShapes

open CCL CCL.GaussianRat
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLBranchPlan
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLNextBitFormula
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventSemantics
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Every weak inequality atom in a formula has a nondegenerate boundary. -/
def WeakAtomsNondegenerate (formula : Formula) : Prop :=
  ∀ atom ∈ formulaAtoms formula,
    atom.sign = .nonpositive ∨ atom.sign = .nonnegative →
      boundaryDiscriminant atom.form ≠ 0

theorem WeakAtomsNondegenerate.and
    {left right : Formula} (leftValid : WeakAtomsNondegenerate left)
    (rightValid : WeakAtomsNondegenerate right) :
    WeakAtomsNondegenerate (.and left right) := by
  intro atom member weak
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact leftValid atom leftMember weak
  · exact rightValid atom rightMember weak

theorem WeakAtomsNondegenerate.or
    {left right : Formula} (leftValid : WeakAtomsNondegenerate left)
    (rightValid : WeakAtomsNondegenerate right) :
    WeakAtomsNondegenerate (.or left right) := by
  intro atom member weak
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact leftValid atom leftMember weak
  · exact rightValid atom rightMember weak

theorem weakAtomsNondegenerate_truth :
    WeakAtomsNondegenerate .truth := by
  simp [WeakAtomsNondegenerate, formulaAtoms]

theorem weakAtomsNondegenerate_falsity :
    WeakAtomsNondegenerate .falsity := by
  simp [WeakAtomsNondegenerate, formulaAtoms]

theorem weakAtomsNondegenerate_atom_strict
    (form : HermitianForm) (sign : SignTest)
    (strict : sign ≠ .nonpositive ∧ sign ≠ .nonnegative) :
    WeakAtomsNondegenerate (.atom ⟨form, sign⟩) := by
  intro atom member weak
  simp only [formulaAtoms, List.mem_singleton] at member
  subst atom
  exact (weak.elim strict.1 strict.2).elim

theorem weakAtomsNondegenerate_atom
    (form : HermitianForm) (sign : SignTest)
    (nondegenerate : boundaryDiscriminant form ≠ 0) :
    WeakAtomsNondegenerate (.atom ⟨form, sign⟩) := by
  intro atom member _weak
  simp only [formulaAtoms, List.mem_singleton] at member
  subst atom
  exact nondegenerate

theorem radialFormula_weakAtomsNondegenerate
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (determinantNonzero : determinant matrix ≠ 0) :
    WeakAtomsNondegenerate (radialFormula kind exponent matrix) := by
  cases kind with
  | initialHigh =>
      apply WeakAtomsNondegenerate.and
      · apply weakAtomsNondegenerate_atom
        apply boundaryDiscriminant_normComparisonForm_ne _ _
          determinantNonzero
        positivity
      · exact weakAtomsNondegenerate_atom_strict _ _ (by simp)
  | initialLow =>
      apply WeakAtomsNondegenerate.and
      · apply weakAtomsNondegenerate_atom
        apply boundaryDiscriminant_normComparisonForm_ne _ _
          determinantNonzero
        positivity
      · exact weakAtomsNondegenerate_atom_strict _ _ (by simp)
  | loop =>
      apply WeakAtomsNondegenerate.and
      · exact weakAtomsNondegenerate_atom_strict _ _ (by simp)
      · apply weakAtomsNondegenerate_atom
        apply boundaryDiscriminant_normComparisonForm_ne _ _
          determinantNonzero
        positivity

theorem weakAtomsNondegenerate_any
    (formulas : List Formula)
    (each : ∀ formula ∈ formulas, WeakAtomsNondegenerate formula) :
    WeakAtomsNondegenerate (Formula.any formulas) := by
  induction formulas with
  | nil => exact weakAtomsNondegenerate_falsity
  | cons head tail inductionHypothesis =>
      apply WeakAtomsNondegenerate.or
      · exact each head (by simp)
      · apply inductionHypothesis
        intro formula member
        exact each formula (by simp [member])

theorem sectorFormula_weakAtomsNondegenerate
    (sector : Sector) (matrix : Mat2 QI)
    (determinantNonzero : determinant matrix ≠ 0) :
    WeakAtomsNondegenerate (sectorFormula sector matrix) := by
  have realValid (threshold : ℚ) (sign : SignTest) :
      WeakAtomsNondegenerate
        (.atom ⟨realComparisonForm matrix threshold, sign⟩) :=
    weakAtomsNondegenerate_atom _ _
      (boundaryDiscriminant_realComparisonForm_ne matrix threshold
        determinantNonzero)
  have imagValid (threshold : ℚ) (sign : SignTest) :
      WeakAtomsNondegenerate
        (.atom ⟨imagComparisonForm matrix threshold, sign⟩) :=
    weakAtomsNondegenerate_atom _ _
      (boundaryDiscriminant_imagComparisonForm_ne matrix threshold
        determinantNonzero)
  have strictReal (threshold : ℚ) (sign : SignTest)
      (strict : sign ≠ .nonpositive ∧ sign ≠ .nonnegative) :
      WeakAtomsNondegenerate
        (.atom ⟨realComparisonForm matrix threshold, sign⟩) :=
    weakAtomsNondegenerate_atom_strict _ _ strict
  have strictImag (threshold : ℚ) (sign : SignTest)
      (strict : sign ≠ .nonpositive ∧ sign ≠ .nonnegative) :
      WeakAtomsNondegenerate
        (.atom ⟨imagComparisonForm matrix threshold, sign⟩) :=
    weakAtomsNondegenerate_atom_strict _ _ strict
  cases sector with
  | east =>
      exact (realValid _ _).and
        ((strictImag _ _ (by simp)).and (strictImag _ _ (by simp)))
  | northEast => exact (realValid _ _).and (imagValid _ _)
  | north =>
      exact (strictReal _ _ (by simp)).and
        ((strictReal _ _ (by simp)).and (imagValid _ _))
  | northWest => exact (realValid _ _).and (imagValid _ _)
  | west =>
      exact (realValid _ _).and
        ((strictImag _ _ (by simp)).and (strictImag _ _ (by simp)))
  | southWest => exact (realValid _ _).and (imagValid _ _)
  | south =>
      exact (strictReal _ _ (by simp)).and
        ((strictReal _ _ (by simp)).and (imagValid _ _))
  | southEast => exact (realValid _ _).and (imagValid _ _)

theorem sectorBitsFormula_zero_weakAtomsNondegenerate
    (kind : RawParser.BlockKind) (exponent : ℕ) :
    WeakAtomsNondegenerate (sectorBitsFormula kind exponent .zero) := by
  let matrix := normalizedMatrix kind exponent RawParser.identityMatrix
  apply weakAtomsNondegenerate_any
  intro formula member
  rcases List.mem_map.mp member with ⟨sector, _sectorMember, rfl⟩
  exact sectorFormula_weakAtomsNondegenerate sector matrix
    (normalizedMatrix_determinant_ne kind exponent)

theorem sectorBitsFormula_weakAtomsNondegenerate
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (bits : RawParser.SectorBits) :
    WeakAtomsNondegenerate (sectorBitsFormula kind exponent bits) := by
  let matrix := normalizedMatrix kind exponent RawParser.identityMatrix
  have determinantNonzero : determinant matrix ≠ 0 :=
    normalizedMatrix_determinant_ne kind exponent
  have realValid (threshold : ℚ) (sign : SignTest) :
      WeakAtomsNondegenerate
        (.atom ⟨realComparisonForm matrix threshold, sign⟩) :=
    weakAtomsNondegenerate_atom _ _
      (boundaryDiscriminant_realComparisonForm_ne matrix threshold
        determinantNonzero)
  have imagValid (threshold : ℚ) (sign : SignTest) :
      WeakAtomsNondegenerate
        (.atom ⟨imagComparisonForm matrix threshold, sign⟩) :=
    weakAtomsNondegenerate_atom _ _
      (boundaryDiscriminant_imagComparisonForm_ne matrix threshold
        determinantNonzero)
  have strictReal (threshold : ℚ) (sign : SignTest)
      (strict : sign ≠ .nonpositive ∧ sign ≠ .nonnegative) :
      WeakAtomsNondegenerate
        (.atom ⟨realComparisonForm matrix threshold, sign⟩) :=
    weakAtomsNondegenerate_atom_strict _ _ strict
  have strictImag (threshold : ℚ) (sign : SignTest)
      (strict : sign ≠ .nonpositive ∧ sign ≠ .nonnegative) :
      WeakAtomsNondegenerate
        (.atom ⟨imagComparisonForm matrix threshold, sign⟩) :=
    weakAtomsNondegenerate_atom_strict _ _ strict
  cases bits with
  | zero =>
      exact sectorBitsFormula_zero_weakAtomsNondegenerate kind exponent
  | one first =>
      cases first with
      | false =>
          simpa [sectorBitsFormula, matrix] using
            ((realValid (1 / 2) .nonnegative).and
                (strictImag (-1 / 2) .positive (by simp))).or
              ((strictReal (1 / 2) .negative (by simp)).and
                (imagValid (1 / 2) .nonnegative))
      | true =>
          simpa [sectorBitsFormula, matrix] using
            (((strictReal (1 / 2) .negative (by simp)).or
                (imagValid (-1 / 2) .nonpositive)).and
              ((realValid (1 / 2) .nonnegative).or
                (strictImag (1 / 2) .negative (by simp)))).and
              ((realValid (1 / 2) .nonnegative).or
                ((realValid (-1 / 2) .nonpositive).or
                  ((imagValid (1 / 2) .nonnegative).or
                    (imagValid (-1 / 2) .nonpositive))))
  | two first second =>
      cases first <;> cases second
      · simpa [sectorBitsFormula, matrix] using
          (realValid (1 / 2) .nonnegative).and
            (strictImag (-1 / 2) .positive (by simp))
      · simpa [sectorBitsFormula, matrix] using
          (strictReal (1 / 2) .negative (by simp)).and
            (imagValid (1 / 2) .nonnegative)
      · simpa [sectorBitsFormula, matrix] using
          (realValid (-1 / 2) .nonpositive).and
            (strictImag (1 / 2) .negative (by simp))
      · simpa [sectorBitsFormula, matrix] using
          (strictReal (-1 / 2) .positive (by simp)).and
            (imagValid (-1 / 2) .nonpositive)

theorem activeFormula_weakAtomsNondegenerate
    (phase : RawParser.Phase) :
    WeakAtomsNondegenerate (activeFormula phase) := by
  have identityDeterminant :
      determinant RawParser.identityMatrix ≠ 0 := by
    norm_num [determinant, RawParser.identityMatrix]
  cases phase with
  | initial => exact weakAtomsNondegenerate_truth
  | highUnary count =>
      apply weakAtomsNondegenerate_atom
      have nondegenerate := boundaryDiscriminant_normComparisonForm_ne
        RawParser.identityMatrix ((2 : ℚ) ^ count) identityDeterminant
        (by positivity)
      simpa [normComparisonForm_identity] using nondegenerate
  | lowUnary count =>
      cases count <;> exact weakAtomsNondegenerate_atom_strict _ _ (by simp)
  | loopUnary count =>
      exact weakAtomsNondegenerate_atom_strict _ _ (by simp)
  | sector kind exponent bits =>
      exact (radialFormula_weakAtomsNondegenerate kind exponent
        RawParser.identityMatrix identityDeterminant).and
          (sectorBitsFormula_weakAtomsNondegenerate kind exponent bits)

theorem completedSectorAdvance_weakAtomsNondegenerate
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second bit : Bool) (matrix : Mat2 QI)
    (history : List RawParser.Constraint) :
    WeakAtomsNondegenerate
      (advanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit) := by
  have identityDeterminant :
      determinant RawParser.identityMatrix ≠ 0 := by
    norm_num [determinant, RawParser.identityMatrix]
  let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
  let sector := RawParser.sectorOfBits first second bit
  have radialValid := radialFormula_weakAtomsNondegenerate kind exponent
    RawParser.identityMatrix identityDeterminant
  have sectorValid := sectorFormula_weakAtomsNondegenerate sector normalized
    (normalizedMatrix_determinant_ne kind exponent)
  have residualValid := weakAtomsNondegenerate_atom_strict
    (residualForm kind exponent sector) .positive (by simp)
  simpa [advanceFormula, normalized, sector] using
    radialValid.and (sectorValid.and residualValid)

/-- Every weak atom introduced by one incremental parser transition is a
nondegenerate local circle or line. -/
theorem incrementalAdvanceFormula_weakAtomsNondegenerate
    (state : RawParser.State) (bit : Bool) :
    WeakAtomsNondegenerate (incrementalAdvanceFormula state bit) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simpa [incrementalAdvanceFormula] using
        activeFormula_weakAtomsNondegenerate
          (RawParser.step ⟨.initial, matrix, history⟩ bit).phase
  | highUnary count =>
      simpa [incrementalAdvanceFormula] using
        activeFormula_weakAtomsNondegenerate
          (RawParser.step ⟨.highUnary count, matrix, history⟩ bit).phase
  | lowUnary count =>
      simpa [incrementalAdvanceFormula] using
        activeFormula_weakAtomsNondegenerate
          (RawParser.step ⟨.lowUnary count, matrix, history⟩ bit).phase
  | loopUnary count =>
      simpa [incrementalAdvanceFormula] using
        activeFormula_weakAtomsNondegenerate
          (RawParser.step ⟨.loopUnary count, matrix, history⟩ bit).phase
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa [incrementalAdvanceFormula] using
            activeFormula_weakAtomsNondegenerate
              (RawParser.step
                ⟨.sector kind exponent .zero, matrix, history⟩ bit).phase
      | one first =>
          simpa [incrementalAdvanceFormula] using
            activeFormula_weakAtomsNondegenerate
              (RawParser.step
                ⟨.sector kind exponent (.one first), matrix, history⟩
                bit).phase
      | two first second =>
          exact completedSectorAdvance_weakAtomsNondegenerate kind exponent
            first second bit matrix history

theorem incrementalActiveOwner_boundaryDiscriminant_ne
    (state : RawParser.State) (bit : Bool)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (incrementalAdvanceFormula state bit)
      value = true) {form : HermitianForm}
    (member : form ∈ activeOwnerForms
      (incrementalAdvanceFormula state bit) value) :
    boundaryDiscriminant form ≠ 0 := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  rw [boundaryDiscriminant_orientedWeakForm]
  apply incrementalAdvanceFormula_weakAtomsNondegenerate state bit atom
  · exact satisfyingAtoms_mem_formulaAtoms _ _
      (activeSatisfyingAtoms_source atomMember)
  · apply activeSatisfyingAtom_sign_weak evaluation
      (satisfyingAtoms_noZeroTest _ _
        (incrementalAdvanceFormula_noZeroTests state bit))
    exact atomMember

/-- Pulling the transition back through an invertible decoder preserves
nondegeneracy of every active owner face. -/
theorem inputIncrementalActiveOwner_boundaryDiscriminant_ne
    (state : RawParser.State) (bit : Bool)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (inputIncrementalAdvanceFormula state bit)
      value = true) {form : HermitianForm}
    (member : form ∈ activeOwnerForms
      (inputIncrementalAdvanceFormula state bit) value) :
    boundaryDiscriminant form ≠ 0 := by
  rw [inputIncrementalAdvanceFormula, activeOwnerForms_pullback] at member
  rcases List.mem_map.mp member with ⟨localForm, localMember, rfl⟩
  have localEvaluation :
      formulaEvalWith (incrementalAdvanceFormula state bit)
        (fun item => value (pullbackForm (adjugate state.matrix) item)) =
          true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  have localNondegenerate := incrementalActiveOwner_boundaryDiscriminant_ne
    state bit _ localEvaluation localMember
  rw [boundaryDiscriminant_pullbackForm]
  exact mul_ne_zero
    (normSq_pos (by
      rw [determinant_adjugate]
      exact stateDeterminant)).ne'
    localNondegenerate

/-- Selected incremental owner faces are therefore nondegenerate whenever
the parser state comes from an invertible decoder. -/
theorem selectedIncrementalActiveOwner_boundaryDiscriminant_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (stateDeterminant : determinant state.matrix ≠ 0)
    {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    boundaryDiscriminant form ≠ 0 := by
  exact inputIncrementalActiveOwner_boundaryDiscriminant_ne state selected.bit
    stateDeterminant (eventPayloadCanonicalValue selected)
    (by
      change formulaEvalWith
        (inputIncrementalAdvanceFormula state selected.bit)
          (inputEventCanonicalValue selected.candidate.inputCell) = true
      exact selected.selectedCanonical_holds) member

end CCLIncrementalOwnerShapes
end FTA
