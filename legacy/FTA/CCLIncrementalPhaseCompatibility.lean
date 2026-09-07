import FTA.CCLIncrementalAngleGap

/-!
# Compatibility of unfinished incremental parser phases

The zero-bit sector fragment is represented by a finite disjunction of all
eight deterministic sector rows.  Its canonical satisfying-atom traversal
chooses one true row.  These lemmas expose that row so the radial/sector
compatibility theorems can be reused before the third sector bit.
-/

namespace FTA
namespace CCLIncrementalPhaseCompatibility

open CCL CCL.GaussianRat
open FTA.CCLBranchEventOwner
open FTA.CCLBranchController
open FTA.CCLBranchPlan
open FTA.CCLCompleteOwnerCompatibility
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLCompleteOwnerShapes
open FTA.CCLEventTangentSigns
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLIncrementalAngleGap
open FTA.CCLIncrementalOwnerShapes
open FTA.CCLNextBitFormula
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventSemantics
open FTA.CCLSectorTangent
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- A true finite disjunction's satisfying-atom list is exactly the list of
one true member formula (the first such member in list order). -/
theorem activeOwnerForms_any_eq_some
    (formulas : List Formula) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (Formula.any formulas) value = true) :
    ∃ formula ∈ formulas,
      formulaEvalWith formula value = true ∧
        activeOwnerForms (Formula.any formulas) value =
          activeOwnerForms formula value := by
  induction formulas with
  | nil => simp [Formula.any, formulaEvalWith] at evaluation
  | cons head tail inductionHypothesis =>
      by_cases headTrue : formulaEvalWith head value = true
      · refine ⟨head, by simp, headTrue, ?_⟩
        simp [Formula.any, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, headTrue]
      · have tailTrue :
            formulaEvalWith (Formula.any tail) value = true := by
          simpa [Formula.any, formulaEvalWith, headTrue] using evaluation
        rcases inductionHypothesis tailTrue with
          ⟨formula, member, formulaTrue, forms⟩
        refine ⟨formula, by simp [member], formulaTrue, ?_⟩
        simpa [Formula.any, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, headTrue] using forms

/-- At a true zero-bit sector formula, the active owner list comes from one
of the eight exact deterministic sector rows. -/
theorem sectorBitsFormula_zero_activeOwnerForms_eq_sector
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (value : HermitianForm → ℚ)
    (evaluation :
      formulaEvalWith (sectorBitsFormula kind exponent .zero) value = true) :
    ∃ sector ∈ RawParser.sectorCandidates .zero,
      formulaEvalWith
          (sectorFormula sector
            (normalizedMatrix kind exponent RawParser.identityMatrix))
          value = true ∧
        activeOwnerForms (sectorBitsFormula kind exponent .zero) value =
          activeOwnerForms
            (sectorFormula sector
              (normalizedMatrix kind exponent RawParser.identityMatrix))
            value := by
  let formulas := RawParser.sectorCandidates .zero |>.map fun sector =>
    sectorFormula sector
      (normalizedMatrix kind exponent RawParser.identityMatrix)
  have source : sectorBitsFormula kind exponent .zero = Formula.any formulas :=
    rfl
  have anyTrue : formulaEvalWith (Formula.any formulas) value = true := by
    simpa only [source] using evaluation
  rcases activeOwnerForms_any_eq_some formulas value anyTrue with
    ⟨formula, formulaMember, formulaTrue, forms⟩
  rcases List.mem_map.mp formulaMember with ⟨sector, sectorMember, rfl⟩
  exact ⟨sector, sectorMember, formulaTrue, by simpa only [source] using forms⟩

/-- A true zero-bit active phase has the same selected owner list as one
radial-and-exact-sector core. -/
theorem sectorZeroActiveFormula_activeOwnerForms_eq_radialSector
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (activeFormula (.sector kind exponent .zero)) value = true) :
    ∃ sector ∈ RawParser.sectorCandidates .zero,
      formulaEvalWith
          (.and
            (radialFormula kind exponent RawParser.identityMatrix)
            (sectorFormula sector
              (normalizedMatrix kind exponent RawParser.identityMatrix)))
          value = true ∧
        activeOwnerForms (activeFormula (.sector kind exponent .zero)) value =
          activeOwnerForms
            (.and
              (radialFormula kind exponent RawParser.identityMatrix)
              (sectorFormula sector
                (normalizedMatrix kind exponent RawParser.identityMatrix)))
            value := by
  have evaluated :
      formulaEvalWith
          (radialFormula kind exponent RawParser.identityMatrix) value = true ∧
        formulaEvalWith (sectorBitsFormula kind exponent .zero) value = true := by
    simpa [activeFormula, formulaEvalWith] using evaluation
  rcases sectorBitsFormula_zero_activeOwnerForms_eq_sector kind exponent value
      evaluated.2 with ⟨sector, member, sectorTrue, forms⟩
  refine ⟨sector, member, ?_, ?_⟩
  · simpa [formulaEvalWith] using And.intro evaluated.1 sectorTrue
  · rw [activeFormula, activeOwnerForms_and, activeOwnerForms_and, forms]

/-- Pulling a zero-bit sector phase back through an invertible decoder
preserves the orthogonal-or-positive-angle-gap classification of every
two-face active cone. -/
theorem pullbackSectorZeroActiveFormula_activeOwnerForms_pair_angleGap
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (pullbackMatrix : Mat2 QI)
    (pullbackDeterminantNonzero : determinant pullbackMatrix ≠ 0)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent .zero))) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent .zero))) value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2 := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (activeFormula (.sector kind exponent .zero)) localValue = true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback] at forms
  change (activeOwnerForms (activeFormula (.sector kind exponent .zero))
      localValue).map (pullbackForm pullbackMatrix) = [left, right] at forms
  cases localForms : activeOwnerForms
      (activeFormula (.sector kind exponent .zero)) localValue with
  | nil => simp [localForms] at forms
  | cons localLeft tail =>
      cases tail with
      | nil => simp [localForms] at forms
      | cons localRight rest =>
          cases rest with
          | nil =>
              simp only [localForms, List.map_cons, List.map_nil,
                List.cons.injEq] at forms
              rcases
                  sectorZeroActiveFormula_activeOwnerForms_eq_radialSector
                    kind exponent localValue localEvaluation with
                ⟨sector, _member, coreTrue, coreForms⟩
              have localShape :=
                radialSectorFormula_activeOwnerForms_pair_angleGap kind
                  exponent sector RawParser.identityMatrix (by
                    norm_num [determinant, RawParser.identityMatrix])
                  localValue coreTrue (by
                    rw [← coreForms]
                    exact localForms)
              rw [← forms.1, ← forms.2.1,
                gradientPairingConstant_pullbackForm,
                boundaryDiscriminant_pullbackForm,
                boundaryDiscriminant_pullbackForm]
              rcases localShape with localZero | localPositive
              · left
                rw [localZero]
                exact mul_zero _
              · right
                let factor := normSq (determinant pullbackMatrix)
                have factorPositive : 0 < factor :=
                  normSq_pos pullbackDeterminantNonzero
                calc
                  0 < factor ^ 2 *
                      (boundaryDiscriminant localLeft *
                          boundaryDiscriminant localRight -
                        2 * gradientPairingConstant localLeft localRight ^ 2) :=
                    mul_pos (sq_pos_of_pos factorPositive) localPositive
                  _ = factor * boundaryDiscriminant localLeft *
                        (factor * boundaryDiscriminant localRight) -
                      2 * (factor *
                        gradientPairingConstant localLeft localRight) ^ 2 := by
                    ring
          | cons third rest => simp [localForms] at forms

/-- A true pulled-back zero-bit sector phase has at most one radial face and
two faces from its selected deterministic sector row. -/
theorem pullbackSectorZeroActiveFormula_activeOwnerForms_length_le_three
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (pullbackMatrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent .zero))) value = true) :
    (activeOwnerForms
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent .zero))) value).length ≤ 3 := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (activeFormula (.sector kind exponent .zero)) localValue = true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback, List.length_map]
  rcases sectorZeroActiveFormula_activeOwnerForms_eq_radialSector kind exponent
      localValue localEvaluation with ⟨sector, _member, coreTrue, forms⟩
  rw [forms]
  exact radialSectorFormula_activeOwnerForms_length_le_three kind exponent
    sector RawParser.identityMatrix localValue coreTrue

/-- If the zero-bit phase reaches three active faces, they are the radial
owner followed by the real and imaginary sides of a diagonal sector row. -/
theorem sectorZeroActiveFormula_activeOwnerForms_triple_exact
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (activeFormula (.sector kind exponent .zero)) value = true)
    {first second third : HermitianForm}
    (forms : activeOwnerForms (activeFormula (.sector kind exponent .zero))
      value = [first, second, third]) :
    first = radialOwnerForm kind exponent RawParser.identityMatrix ∧
      ((second = positiveRealOwner
            (normalizedMatrix kind exponent RawParser.identityMatrix) ∧
          third = positiveImagOwner
            (normalizedMatrix kind exponent RawParser.identityMatrix)) ∨
        (second = negativeRealOwner
            (normalizedMatrix kind exponent RawParser.identityMatrix) ∧
          third = positiveImagOwner
            (normalizedMatrix kind exponent RawParser.identityMatrix)) ∨
        (second = negativeRealOwner
            (normalizedMatrix kind exponent RawParser.identityMatrix) ∧
          third = negativeImagOwner
            (normalizedMatrix kind exponent RawParser.identityMatrix)) ∨
        (second = positiveRealOwner
            (normalizedMatrix kind exponent RawParser.identityMatrix) ∧
          third = negativeImagOwner
            (normalizedMatrix kind exponent RawParser.identityMatrix))) := by
  rcases sectorZeroActiveFormula_activeOwnerForms_eq_radialSector kind exponent
      value evaluation with ⟨sector, _member, coreTrue, coreForms⟩
  have coreTriple : activeOwnerForms
      (.and (radialFormula kind exponent RawParser.identityMatrix)
        (sectorFormula sector
          (normalizedMatrix kind exponent RawParser.identityMatrix))) value =
        [first, second, third] := by
    rw [← coreForms]
    exact forms
  have evaluated := coreTrue
  simp only [formulaEvalWith, Bool.and_eq_true] at evaluated
  rw [activeOwnerForms_and] at coreTriple
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      RawParser.identityMatrix value evaluated.1 with radialNil | radialSingleton
  · rw [radialNil, List.nil_append] at coreTriple
    have sectorLength := sectorFormula_activeOwnerForms_length_le_two sector
      (normalizedMatrix kind exponent RawParser.identityMatrix) value evaluated.2
    rw [coreTriple] at sectorLength
    norm_num at sectorLength
  · rw [radialSingleton, List.singleton_append, List.cons.injEq] at coreTriple
    refine ⟨coreTriple.1.symm, ?_⟩
    rcases sectorFormula_activeOwnerForms_pair_exact sector
        (normalizedMatrix kind exponent RawParser.identityMatrix) value
        evaluated.2 coreTriple.2 with
      northEast | northWest | southWest | southEast
    · exact Or.inl ⟨northEast.2.1, northEast.2.2⟩
    · exact Or.inr (Or.inl ⟨northWest.2.1, northWest.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨southWest.2.1, southWest.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨southEast.2.1, southEast.2.2⟩))

/-- Exact three-face zero-bit shape after the decoder pullback into the input
coordinate. -/
theorem pullbackSectorZeroActiveFormula_activeOwnerForms_triple_exact
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (pullbackMatrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent .zero))) value = true)
    {first second third : HermitianForm}
    (forms : activeOwnerForms
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent .zero))) value =
      [first, second, third]) :
    first = radialOwnerForm kind exponent pullbackMatrix ∧
      ((second = positiveRealOwner
            (normalizedMatrix kind exponent pullbackMatrix) ∧
          third = positiveImagOwner
            (normalizedMatrix kind exponent pullbackMatrix)) ∨
        (second = negativeRealOwner
            (normalizedMatrix kind exponent pullbackMatrix) ∧
          third = positiveImagOwner
            (normalizedMatrix kind exponent pullbackMatrix)) ∨
        (second = negativeRealOwner
            (normalizedMatrix kind exponent pullbackMatrix) ∧
          third = negativeImagOwner
            (normalizedMatrix kind exponent pullbackMatrix)) ∨
        (second = positiveRealOwner
            (normalizedMatrix kind exponent pullbackMatrix) ∧
          third = negativeImagOwner
            (normalizedMatrix kind exponent pullbackMatrix))) := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (activeFormula (.sector kind exponent .zero)) localValue = true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback] at forms
  change (activeOwnerForms (activeFormula (.sector kind exponent .zero))
      localValue).map (pullbackForm pullbackMatrix) =
        [first, second, third] at forms
  cases localForms : activeOwnerForms
      (activeFormula (.sector kind exponent .zero)) localValue with
  | nil => simp [localForms] at forms
  | cons localFirst tail =>
      cases tail with
      | nil => simp [localForms] at forms
      | cons localSecond rest =>
          cases rest with
          | nil => simp [localForms] at forms
          | cons localThird remaining =>
              cases remaining with
              | nil =>
                  simp only [localForms, List.map_cons, List.map_nil,
                    List.cons.injEq] at forms
                  rcases
                      sectorZeroActiveFormula_activeOwnerForms_triple_exact
                        kind exponent localValue localEvaluation localForms with
                    ⟨rfl, corner⟩
                  refine ⟨?_, ?_⟩
                  · simpa only [pullbackForm_radialOwnerForm,
                      identityMatrix_mul] using forms.1.symm
                  · rcases corner with
                      northEast | northWest | southWest | southEast
                    · rcases northEast with ⟨rfl, rfl⟩
                      exact Or.inl ⟨by
                        simpa only [pullbackForm_positiveRealOwner,
                          normalizedMatrix_identity_mul] using forms.2.1.symm,
                        by simpa only [pullbackForm_positiveImagOwner,
                          normalizedMatrix_identity_mul] using
                            forms.2.2.1.symm⟩
                    · rcases northWest with ⟨rfl, rfl⟩
                      exact Or.inr (Or.inl ⟨by
                        simpa only [pullbackForm_negativeRealOwner,
                          normalizedMatrix_identity_mul] using forms.2.1.symm,
                        by simpa only [pullbackForm_positiveImagOwner,
                          normalizedMatrix_identity_mul] using
                            forms.2.2.1.symm⟩)
                    · rcases southWest with ⟨rfl, rfl⟩
                      exact Or.inr (Or.inr (Or.inl ⟨by
                        simpa only [pullbackForm_negativeRealOwner,
                          normalizedMatrix_identity_mul] using forms.2.1.symm,
                        by simpa only [pullbackForm_negativeImagOwner,
                          normalizedMatrix_identity_mul] using
                            forms.2.2.1.symm⟩))
                    · rcases southEast with ⟨rfl, rfl⟩
                      exact Or.inr (Or.inr (Or.inr ⟨by
                        simpa only [pullbackForm_positiveRealOwner,
                          normalizedMatrix_identity_mul] using forms.2.1.symm,
                        by simpa only [pullbackForm_negativeImagOwner,
                          normalizedMatrix_identity_mul] using
                            forms.2.2.1.symm⟩))
              | cons fourth remaining => simp [localForms] at forms

/-- The structural three-face zero-bit cone cannot occur at a selected
incremental event: its normalized radial boundary misses every coordinate
corner by a fixed nonzero squared-radius gap. -/
theorem selectedSectorZeroActiveOwnerForms_ne_triple
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (stateDeterminantNonzero : determinant state.matrix ≠ 0)
    (formulaIdentity : inputIncrementalAdvanceFormula state selected.bit =
      Formula.pullback (adjugate state.matrix)
        (activeFormula (.sector kind exponent .zero)))
    {first second third : HermitianForm}
    (forms : eventPayloadIncrementalActiveOwnerForms selected =
      [first, second, third]) :
    False := by
  let normalized := normalizedMatrix kind exponent (adjugate state.matrix)
  have evaluation : formulaEvalWith
      (Formula.pullback (adjugate state.matrix)
        (activeFormula (.sector kind exponent .zero)))
      (eventPayloadCanonicalValue selected) = true := by
    rw [← formulaIdentity]
    exact selected.canonical_holds
  have pulledForms : activeOwnerForms
      (Formula.pullback (adjugate state.matrix)
        (activeFormula (.sector kind exponent .zero)))
      (eventPayloadCanonicalValue selected) = [first, second, third] := by
    rw [← formulaIdentity]
    simpa only [eventPayloadIncrementalActiveOwnerForms] using forms
  rcases pullbackSectorZeroActiveFormula_activeOwnerForms_triple_exact
      kind exponent (adjugate state.matrix)
      (eventPayloadCanonicalValue selected) evaluation pulledForms with
    ⟨rfl, corner⟩
  let decoderLower := selectedSlopeDecoderDenominatorPositiveLowerBound
    selected stateDeterminantNonzero
  have normalizedLower : FTA.PositiveLowerBound.Certificate
      (clearedForm (affineNormForm normalized.c normalized.d)
        (selectedPath selected))
      (selectedSlopeSigns selected).refined.interval := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent
      (adjugate state.matrix)
    dsimp only [normalized]
    rw [lowerRow.1, lowerRow.2]
    exact decoderLower
  have radialMember :
      HermitianForm.scale (normalizedRadialOwnerScale kind exponent)
          (normComparisonForm normalized (normalizedRadialRadius kind)) ∈
        eventPayloadIncrementalActiveOwnerForms selected := by
    rw [← radialOwnerForm_eq_scale_normalized]
    simp [forms]
  rcases corner with northEast | northWest | southWest | southEast
  · rcases northEast with ⟨rfl, rfl⟩
    apply selectedSlope_scaled_norm_real_imag_not_all_active selected
      normalized (normalizedRadialRadius kind) (1 / 2) (1 / 2)
      (normalizedRadialOwnerScale kind exponent) 1 1
    · exact normalizedRadialOwnerScale_ne kind exponent
    · norm_num
    · norm_num
    · exact normalizedCorner_radius_gap_ne kind
    · exact normalizedLower
    · exact radialMember
    · simp [normalized, forms, positiveRealOwner]
    · simp [normalized, forms, positiveImagOwner]
  · rcases northWest with ⟨rfl, rfl⟩
    apply selectedSlope_scaled_norm_real_imag_not_all_active selected
      normalized (normalizedRadialRadius kind) (-1 / 2) (1 / 2)
      (normalizedRadialOwnerScale kind exponent) (-1) 1
    · exact normalizedRadialOwnerScale_ne kind exponent
    · norm_num
    · norm_num
    · have gap := normalizedCorner_radius_gap_ne kind
      norm_num at gap ⊢
      exact gap
    · exact normalizedLower
    · exact radialMember
    · simp [normalized, forms, negativeRealOwner]
    · simp [normalized, forms, positiveImagOwner]
  · rcases southWest with ⟨rfl, rfl⟩
    apply selectedSlope_scaled_norm_real_imag_not_all_active selected
      normalized (normalizedRadialRadius kind) (-1 / 2) (-1 / 2)
      (normalizedRadialOwnerScale kind exponent) (-1) (-1)
    · exact normalizedRadialOwnerScale_ne kind exponent
    · norm_num
    · norm_num
    · have gap := normalizedCorner_radius_gap_ne kind
      norm_num at gap ⊢
      exact gap
    · exact normalizedLower
    · exact radialMember
    · simp [normalized, forms, negativeRealOwner]
    · simp [normalized, forms, negativeImagOwner]
  · rcases southEast with ⟨rfl, rfl⟩
    apply selectedSlope_scaled_norm_real_imag_not_all_active selected
      normalized (normalizedRadialRadius kind) (1 / 2) (-1 / 2)
      (normalizedRadialOwnerScale kind exponent) 1 (-1)
    · exact normalizedRadialOwnerScale_ne kind exponent
    · norm_num
    · norm_num
    · have gap := normalizedCorner_radius_gap_ne kind
      norm_num at gap ⊢
      exact gap
    · exact normalizedLower
    · exact radialMember
    · simp [normalized, forms, positiveRealOwner]
    · simp [normalized, forms, negativeImagOwner]

/-- Whenever an incremental child formula is a pulled-back zero-bit sector
phase, the finite classified tangent search succeeds. -/
theorem classifiedTangentDirection?_isSome_of_sectorZeroFormula
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (stateDeterminantNonzero : determinant state.matrix ≠ 0)
    (formulaIdentity : inputIncrementalAdvanceFormula state selected.bit =
      Formula.pullback (adjugate state.matrix)
        (activeFormula (.sector kind exponent .zero))) :
    (classifiedTangentDirection? selected).isSome := by
  have evaluation : formulaEvalWith
      (Formula.pullback (adjugate state.matrix)
        (activeFormula (.sector kind exponent .zero)))
      (eventPayloadCanonicalValue selected) = true := by
    rw [← formulaIdentity]
    exact selected.canonical_holds
  have lengthLeThree :
      (eventPayloadIncrementalActiveOwnerForms selected).length ≤ 3 := by
    have localLength :=
      pullbackSectorZeroActiveFormula_activeOwnerForms_length_le_three
        kind exponent (adjugate state.matrix)
        (eventPayloadCanonicalValue selected) evaluation
    rw [← formulaIdentity] at localLength
    simpa only [eventPayloadIncrementalActiveOwnerForms] using localLength
  have lengthLeTwo :
      (eventPayloadIncrementalActiveOwnerForms selected).length ≤ 2 := by
    cases forms : eventPayloadIncrementalActiveOwnerForms selected with
    | nil => simp
    | cons first tail =>
        cases tail with
        | nil => simp
        | cons second rest =>
            cases rest with
            | nil => simp
            | cons third remaining =>
                cases remaining with
                | nil =>
                    exact (selectedSectorZeroActiveOwnerForms_ne_triple
                      selected kind exponent stateDeterminantNonzero
                      formulaIdentity (by simpa using forms)).elim
                | cons fourth remaining =>
                    simp [forms] at lengthLeThree
                    omega
  cases forms : eventPayloadIncrementalActiveOwnerForms selected with
  | nil => exact classifiedTangentDirection?_isSome_of_nil selected forms
  | cons first tail =>
      cases tail with
      | nil =>
          exact classifiedTangentDirection?_isSome_of_singleton selected
            stateDeterminantNonzero forms
      | cons second rest =>
          cases rest with
          | nil =>
              have pulledForms : activeOwnerForms
                  (Formula.pullback (adjugate state.matrix)
                    (activeFormula (.sector kind exponent .zero)))
                  (eventPayloadCanonicalValue selected) = [first, second] := by
                rw [← formulaIdentity]
                simpa only [eventPayloadIncrementalActiveOwnerForms] using forms
              rcases
                  pullbackSectorZeroActiveFormula_activeOwnerForms_pair_angleGap
                    kind exponent (adjugate state.matrix) (by
                      rw [determinant_adjugate]
                      exact stateDeterminantNonzero)
                    (eventPayloadCanonicalValue selected) evaluation pulledForms
                with pairingZero | angleGapPositive
              · exact classifiedTangentDirection?_isSome_of_pairingConstant_zero
                  selected stateDeterminantNonzero forms pairingZero
              · exact classifiedTangentDirection?_isSome_of_pair_angleGap
                  selected forms angleGapPositive
          | cons third remaining => simp [forms] at lengthLeTwo

theorem classifiedTangentDirection?_isSome_highUnary_false
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {count : ℕ} {matrix : Mat2 QI}
    {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output) (selectedFalse : selected.bit = false)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.highUnary count, matrix, history⟩) selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_sectorZeroFormula selected
    .initialHigh count stateDeterminant
  simp [selectedFalse, inputIncrementalAdvanceFormula,
    incrementalAdvanceFormula, RawParser.step]

theorem classifiedTangentDirection?_isSome_lowUnary_false
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {count : ℕ} {matrix : Mat2 QI}
    {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output) (selectedFalse : selected.bit = false)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.lowUnary count, matrix, history⟩) selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_sectorZeroFormula selected
    .initialLow count stateDeterminant
  simp [selectedFalse, inputIncrementalAdvanceFormula,
    incrementalAdvanceFormula, RawParser.step]

theorem classifiedTangentDirection?_isSome_loopUnary_false
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {count : ℕ} {matrix : Mat2 QI}
    {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output) (selectedFalse : selected.bit = false)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.loopUnary count, matrix, history⟩) selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_sectorZeroFormula selected
    .loop count stateDeterminant
  simp [selectedFalse, inputIncrementalAdvanceFormula,
    incrementalAdvanceFormula, RawParser.step]

/-- A true two-bit sector predicate has no active face or exactly its one
weak coordinate side; its other displayed comparison is strict. -/
theorem sectorBitsFormula_two_activeOwnerForms_eq_nil_or_singleton
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (sectorBitsFormula kind exponent (.two first second)) value = true) :
    let matrix := normalizedMatrix kind exponent RawParser.identityMatrix
    match first, second with
    | false, false =>
        activeOwnerForms (sectorBitsFormula kind exponent (.two false false))
            value = [] ∨
          activeOwnerForms
            (sectorBitsFormula kind exponent (.two false false)) value =
              [positiveRealOwner matrix]
    | false, true =>
        activeOwnerForms (sectorBitsFormula kind exponent (.two false true))
            value = [] ∨
          activeOwnerForms
            (sectorBitsFormula kind exponent (.two false true)) value =
              [positiveImagOwner matrix]
    | true, false =>
        activeOwnerForms (sectorBitsFormula kind exponent (.two true false))
            value = [] ∨
          activeOwnerForms
            (sectorBitsFormula kind exponent (.two true false)) value =
              [negativeRealOwner matrix]
    | true, true =>
        activeOwnerForms (sectorBitsFormula kind exponent (.two true true))
            value = [] ∨
          activeOwnerForms
            (sectorBitsFormula kind exponent (.two true true)) value =
              [negativeImagOwner matrix] := by
  let matrix := normalizedMatrix kind exponent RawParser.identityMatrix
  cases first <;> cases second
  · have evaluated :
        0 ≤ value (realComparisonForm matrix ((2 : ℚ)⁻¹)) ∧
          0 < value (imagComparisonForm matrix (-1 / 2)) := by
      simpa [sectorBitsFormula, matrix, formulaEvalWith,
        SignTest.Holds] using evaluation
    have strictNonzero := evaluated.2.ne'
    by_cases weakZero :
        value (realComparisonForm matrix ((2 : ℚ)⁻¹)) = 0
    · right
      dsimp only [matrix] at weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, weakZero, strictNonzero,
        positiveRealOwner, orientedWeakForm]
    · left
      dsimp only [matrix] at weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, weakZero, strictNonzero]

  · have evaluated :
        value (realComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 ∧
          0 ≤ value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) := by
      simpa [sectorBitsFormula, matrix, formulaEvalWith,
        SignTest.Holds] using evaluation
    have strictNonzero := evaluated.1.ne
    by_cases weakZero :
        value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) = 0
    · right
      dsimp only [matrix] at weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, weakZero, strictNonzero,
        positiveImagOwner, orientedWeakForm]
    · left
      dsimp only [matrix] at weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, weakZero, strictNonzero]

  · have evaluated :
        value (realComparisonForm matrix (-1 / 2)) ≤ 0 ∧
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 := by
      simpa [sectorBitsFormula, matrix, formulaEvalWith,
        SignTest.Holds] using evaluation
    have strictNonzero := evaluated.2.ne
    by_cases weakZero : value (realComparisonForm matrix (-1 / 2)) = 0
    · right
      dsimp only [matrix] at weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, weakZero, strictNonzero,
        negativeRealOwner, orientedWeakForm]
    · left
      dsimp only [matrix] at weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, weakZero, strictNonzero]
  · have evaluated :
        0 < value (realComparisonForm matrix (-1 / 2)) ∧
          value (imagComparisonForm matrix (-1 / 2)) ≤ 0 := by
      simpa [sectorBitsFormula, matrix, formulaEvalWith,
        SignTest.Holds] using evaluation
    have strictNonzero := evaluated.1.ne'
    by_cases weakZero : value (imagComparisonForm matrix (-1 / 2)) = 0
    · right
      dsimp only [matrix] at weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, weakZero, strictNonzero,
        negativeImagOwner, orientedWeakForm]
    · left
      dsimp only [matrix] at weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, weakZero, strictNonzero]

theorem sectorBitsFormula_two_activeOwnerForms_eq_nil_or_sectorSingleton
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (sectorBitsFormula kind exponent (.two first second)) value = true) :
    activeOwnerForms (sectorBitsFormula kind exponent (.two first second))
        value = [] ∨
      ∃ sector form,
        activeOwnerForms (sectorBitsFormula kind exponent (.two first second))
            value = [form] ∧
          form ∈ sectorOwnerForms sector
            (normalizedMatrix kind exponent RawParser.identityMatrix) := by
  cases first <;> cases second
  · rcases sectorBitsFormula_two_activeOwnerForms_eq_nil_or_singleton kind
        exponent false false value evaluation with forms | forms
    · exact Or.inl forms
    · exact Or.inr ⟨.east, positiveRealOwner
        (normalizedMatrix kind exponent RawParser.identityMatrix), forms, by
          simp [sectorOwnerForms]⟩
  · rcases sectorBitsFormula_two_activeOwnerForms_eq_nil_or_singleton kind
        exponent false true value evaluation with forms | forms
    · exact Or.inl forms
    · exact Or.inr ⟨.north, positiveImagOwner
        (normalizedMatrix kind exponent RawParser.identityMatrix), forms, by
          simp [sectorOwnerForms]⟩
  · rcases sectorBitsFormula_two_activeOwnerForms_eq_nil_or_singleton kind
        exponent true false value evaluation with forms | forms
    · exact Or.inl forms
    · exact Or.inr ⟨.west, negativeRealOwner
        (normalizedMatrix kind exponent RawParser.identityMatrix), forms, by
          simp [sectorOwnerForms]⟩
  · rcases sectorBitsFormula_two_activeOwnerForms_eq_nil_or_singleton kind
        exponent true true value evaluation with forms | forms
    · exact Or.inl forms
    · exact Or.inr ⟨.south, negativeImagOwner
        (normalizedMatrix kind exponent RawParser.identityMatrix), forms, by
          simp [sectorOwnerForms]⟩

/-- Exactly two active faces in a two-bit unfinished sector phase are its
radial owner and its sole weak coordinate side, hence have positive angle
gap. -/
theorem sectorTwoActiveFormula_activeOwnerForms_pair_angleGap
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (activeFormula (.sector kind exponent (.two first second))) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (activeFormula (.sector kind exponent (.two first second))) value =
        [left, right]) :
    0 < boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2 := by
  have evaluated :
      formulaEvalWith
          (radialFormula kind exponent RawParser.identityMatrix) value = true ∧
        formulaEvalWith
          (sectorBitsFormula kind exponent (.two first second)) value = true := by
    simpa [activeFormula, formulaEvalWith] using evaluation
  rw [activeFormula, activeOwnerForms_and] at forms
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      RawParser.identityMatrix value evaluated.1 with radialNil | radialSingleton
  · rw [radialNil, List.nil_append] at forms
    rcases sectorBitsFormula_two_activeOwnerForms_eq_nil_or_sectorSingleton kind
        exponent first second value evaluated.2 with sectorNil |
          ⟨sector, sectorForm, sectorSingleton, sectorMember⟩
    · simp [sectorNil] at forms
    · simp [sectorSingleton] at forms
  · rw [radialSingleton] at forms
    rcases sectorBitsFormula_two_activeOwnerForms_eq_nil_or_sectorSingleton kind
        exponent first second value evaluated.2 with sectorNil |
          ⟨sector, sectorForm, sectorSingleton, sectorMember⟩
    · simp [sectorNil] at forms
    · rw [sectorSingleton] at forms
      simp only [List.singleton_append, List.cons.injEq, and_true] at forms
      rw [← forms.1, ← forms.2]
      exact radialOwner_sectorOwner_angleGap_pos kind exponent sector
        RawParser.identityMatrix (by
          norm_num [determinant, RawParser.identityMatrix]) sectorMember

/-- A true two-bit active phase has at most its radial face and one weak
coordinate face. -/
theorem sectorTwoActiveFormula_activeOwnerForms_length_le_two
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (activeFormula (.sector kind exponent (.two first second))) value = true) :
    (activeOwnerForms
      (activeFormula (.sector kind exponent (.two first second))) value).length
        ≤ 2 := by
  have evaluated :
      formulaEvalWith
          (radialFormula kind exponent RawParser.identityMatrix) value = true ∧
        formulaEvalWith
          (sectorBitsFormula kind exponent (.two first second)) value = true := by
    simpa [activeFormula, formulaEvalWith] using evaluation
  rw [activeFormula, activeOwnerForms_and]
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      RawParser.identityMatrix value evaluated.1 with radialNil | radialSingleton
  · rw [radialNil, List.nil_append]
    rcases sectorBitsFormula_two_activeOwnerForms_eq_nil_or_sectorSingleton kind
        exponent first second value evaluated.2 with sectorNil |
          ⟨sector, sectorForm, sectorSingleton, sectorMember⟩
    · simp [sectorNil]
    · simp [sectorSingleton]
  · rw [radialSingleton]
    rcases sectorBitsFormula_two_activeOwnerForms_eq_nil_or_sectorSingleton kind
        exponent first second value evaluated.2 with sectorNil |
          ⟨sector, sectorForm, sectorSingleton, sectorMember⟩
    · simp [sectorNil]
    · simp [sectorSingleton]

/-- Pullback preserves the positive angle gap of a two-face unfinished
two-bit sector cone. -/
theorem pullbackSectorTwoActiveFormula_activeOwnerForms_pair_angleGap
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (pullbackMatrix : Mat2 QI)
    (pullbackDeterminantNonzero : determinant pullbackMatrix ≠ 0)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent (.two first second))))
      value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent (.two first second)))) value =
      [left, right]) :
    0 < boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2 := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (activeFormula (.sector kind exponent (.two first second))) localValue =
        true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback] at forms
  change (activeOwnerForms
      (activeFormula (.sector kind exponent (.two first second)))
      localValue).map (pullbackForm pullbackMatrix) = [left, right] at forms
  cases localForms : activeOwnerForms
      (activeFormula (.sector kind exponent (.two first second))) localValue with
  | nil => simp [localForms] at forms
  | cons localLeft tail =>
      cases tail with
      | nil => simp [localForms] at forms
      | cons localRight rest =>
          cases rest with
          | nil =>
              simp only [localForms, List.map_cons, List.map_nil,
                List.cons.injEq] at forms
              have localPositive :=
                sectorTwoActiveFormula_activeOwnerForms_pair_angleGap kind
                  exponent first second localValue localEvaluation localForms
              rw [← forms.1, ← forms.2.1,
                gradientPairingConstant_pullbackForm,
                boundaryDiscriminant_pullbackForm,
                boundaryDiscriminant_pullbackForm]
              let factor := normSq (determinant pullbackMatrix)
              have factorPositive : 0 < factor :=
                normSq_pos pullbackDeterminantNonzero
              calc
                0 < factor ^ 2 *
                    (boundaryDiscriminant localLeft *
                        boundaryDiscriminant localRight -
                      2 * gradientPairingConstant localLeft localRight ^ 2) :=
                  mul_pos (sq_pos_of_pos factorPositive) localPositive
                _ = factor * boundaryDiscriminant localLeft *
                      (factor * boundaryDiscriminant localRight) -
                    2 * (factor *
                      gradientPairingConstant localLeft localRight) ^ 2 := by
                  ring
          | cons third rest => simp [localForms] at forms

theorem pullbackSectorTwoActiveFormula_activeOwnerForms_length_le_two
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (pullbackMatrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent (.two first second))))
      value = true) :
    (activeOwnerForms
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent (.two first second))))
      value).length ≤ 2 := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (activeFormula (.sector kind exponent (.two first second))) localValue =
        true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback, List.length_map]
  exact sectorTwoActiveFormula_activeOwnerForms_length_le_two kind exponent
    first second localValue localEvaluation

/-- Whenever an incremental child is a pulled-back unfinished two-bit sector
phase, the compass search succeeds unconditionally. -/
theorem classifiedTangentDirection?_isSome_of_sectorTwoFormula
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (stateDeterminantNonzero : determinant state.matrix ≠ 0)
    (formulaIdentity : inputIncrementalAdvanceFormula state selected.bit =
      Formula.pullback (adjugate state.matrix)
        (activeFormula (.sector kind exponent (.two first second)))) :
    (classifiedTangentDirection? selected).isSome := by
  have evaluation : formulaEvalWith
      (Formula.pullback (adjugate state.matrix)
        (activeFormula (.sector kind exponent (.two first second))))
      (eventPayloadCanonicalValue selected) = true := by
    rw [← formulaIdentity]
    exact selected.canonical_holds
  have lengthLeTwo :
      (eventPayloadIncrementalActiveOwnerForms selected).length ≤ 2 := by
    have localLength :=
      pullbackSectorTwoActiveFormula_activeOwnerForms_length_le_two kind
        exponent first second (adjugate state.matrix)
        (eventPayloadCanonicalValue selected) evaluation
    rw [← formulaIdentity] at localLength
    simpa only [eventPayloadIncrementalActiveOwnerForms] using localLength
  cases forms : eventPayloadIncrementalActiveOwnerForms selected with
  | nil => exact classifiedTangentDirection?_isSome_of_nil selected forms
  | cons firstForm tail =>
      cases tail with
      | nil =>
          exact classifiedTangentDirection?_isSome_of_singleton selected
            stateDeterminantNonzero forms
      | cons secondForm rest =>
          cases rest with
          | nil =>
              have pulledForms : activeOwnerForms
                  (Formula.pullback (adjugate state.matrix)
                    (activeFormula
                      (.sector kind exponent (.two first second))))
                  (eventPayloadCanonicalValue selected) =
                    [firstForm, secondForm] := by
                rw [← formulaIdentity]
                simpa only [eventPayloadIncrementalActiveOwnerForms] using forms
              have angleGapPositive :=
                pullbackSectorTwoActiveFormula_activeOwnerForms_pair_angleGap
                  kind exponent first second (adjugate state.matrix) (by
                    rw [determinant_adjugate]
                    exact stateDeterminantNonzero)
                  (eventPayloadCanonicalValue selected) evaluation pulledForms
              exact classifiedTangentDirection?_isSome_of_pair_angleGap
                selected forms angleGapPositive
          | cons third remaining => simp [forms] at lengthLeTwo

theorem classifiedTangentDirection?_isSome_sector_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.sector kind exponent (.one first), matrix, history⟩) selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_sectorTwoFormula selected
    kind exponent first selected.bit stateDeterminant
  simp [inputIncrementalAdvanceFormula, incrementalAdvanceFormula,
    RawParser.step]

/-- The false first-sector-bit predicate selects one of two conjunctions,
each containing exactly one weak coordinate comparison. -/
theorem sectorBitsFormula_one_false_activeOwnerForms_eq_nil_or_sectorSingleton
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (sectorBitsFormula kind exponent (.one false)) value = true) :
    activeOwnerForms (sectorBitsFormula kind exponent (.one false)) value =
        [] ∨
      ∃ sector form,
        activeOwnerForms (sectorBitsFormula kind exponent (.one false)) value =
            [form] ∧
          form ∈ sectorOwnerForms sector
            (normalizedMatrix kind exponent RawParser.identityMatrix) := by
  let matrix := normalizedMatrix kind exponent RawParser.identityMatrix
  let left : Formula := .and
    (.atom ⟨realComparisonForm matrix (1 / 2), .nonnegative⟩)
    (.atom ⟨imagComparisonForm matrix (-1 / 2), .positive⟩)
  have source : sectorBitsFormula kind exponent (.one false) =
      .or left
        (.and (.atom ⟨realComparisonForm matrix (1 / 2), .negative⟩)
          (.atom ⟨imagComparisonForm matrix (1 / 2), .nonnegative⟩)) :=
    rfl
  by_cases leftTrue : formulaEvalWith left value = true
  · have evaluated :
        0 ≤ value (realComparisonForm matrix ((2 : ℚ)⁻¹)) ∧
          0 < value (imagComparisonForm matrix (-1 / 2)) := by
      simpa [left, formulaEvalWith, SignTest.Holds] using leftTrue
    have strictNonzero := evaluated.2.ne'
    by_cases weakZero :
        value (realComparisonForm matrix ((2 : ℚ)⁻¹)) = 0
    · right
      refine ⟨.east, positiveRealOwner matrix, ?_, by
        dsimp only [matrix]
        simp [sectorOwnerForms]⟩
      dsimp only [matrix] at evaluated weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, formulaEvalWith, SignTest.Holds, evaluated.2,
        weakZero, strictNonzero,
        positiveRealOwner, orientedWeakForm]
    · left
      dsimp only [matrix] at evaluated weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, formulaEvalWith, SignTest.Holds, evaluated.1,
        evaluated.2, weakZero, strictNonzero]
  · have rightTrue : formulaEvalWith
        (.and (.atom ⟨realComparisonForm matrix (1 / 2), .negative⟩)
          (.atom ⟨imagComparisonForm matrix (1 / 2), .nonnegative⟩))
        value = true := by
      simpa [source, formulaEvalWith, leftTrue] using evaluation
    have evaluated :
        value (realComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 ∧
          0 ≤ value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) := by
      simpa [formulaEvalWith, SignTest.Holds] using rightTrue
    have strictNonzero := evaluated.1.ne
    have leftFalse : ¬(0 ≤ value
          (realComparisonForm matrix ((2 : ℚ)⁻¹)) ∧
        0 < value (imagComparisonForm matrix (-1 / 2))) := by
      intro leftCondition
      apply leftTrue
      simpa [left, formulaEvalWith, SignTest.Holds] using leftCondition
    by_cases weakZero :
        value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) = 0
    · right
      refine ⟨.north, positiveImagOwner matrix, ?_, by
        dsimp only [matrix]
        simp [sectorOwnerForms]⟩
      dsimp only [matrix] at evaluated leftFalse weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, formulaEvalWith, SignTest.Holds, leftFalse,
        weakZero, strictNonzero,
        positiveImagOwner, orientedWeakForm]
    · left
      dsimp only [matrix] at evaluated leftFalse weakZero strictNonzero ⊢
      simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
        satisfyingAtoms, formulaEvalWith, SignTest.Holds, leftFalse,
        weakZero, strictNonzero]

theorem sectorOneFalseActiveFormula_activeOwnerForms_pair_angleGap
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (activeFormula (.sector kind exponent (.one false))) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (activeFormula (.sector kind exponent (.one false))) value =
        [left, right]) :
    0 < boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2 := by
  have evaluated :
      formulaEvalWith
          (radialFormula kind exponent RawParser.identityMatrix) value = true ∧
        formulaEvalWith
          (sectorBitsFormula kind exponent (.one false)) value = true := by
    simpa [activeFormula, formulaEvalWith] using evaluation
  rw [activeFormula, activeOwnerForms_and] at forms
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      RawParser.identityMatrix value evaluated.1 with radialNil | radialSingleton
  · rw [radialNil, List.nil_append] at forms
    rcases
        sectorBitsFormula_one_false_activeOwnerForms_eq_nil_or_sectorSingleton
          kind exponent value evaluated.2 with sectorNil |
          ⟨sector, sectorForm, sectorSingleton, sectorMember⟩
    · simp [sectorNil] at forms
    · simp [sectorSingleton] at forms
  · rw [radialSingleton] at forms
    rcases
        sectorBitsFormula_one_false_activeOwnerForms_eq_nil_or_sectorSingleton
          kind exponent value evaluated.2 with sectorNil |
          ⟨sector, sectorForm, sectorSingleton, sectorMember⟩
    · simp [sectorNil] at forms
    · rw [sectorSingleton] at forms
      simp only [List.singleton_append, List.cons.injEq, and_true] at forms
      rw [← forms.1, ← forms.2]
      exact radialOwner_sectorOwner_angleGap_pos kind exponent sector
        RawParser.identityMatrix (by
          norm_num [determinant, RawParser.identityMatrix]) sectorMember

theorem sectorOneFalseActiveFormula_activeOwnerForms_length_le_two
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (activeFormula (.sector kind exponent (.one false))) value = true) :
    (activeOwnerForms (activeFormula (.sector kind exponent (.one false)))
      value).length ≤ 2 := by
  have evaluated :
      formulaEvalWith
          (radialFormula kind exponent RawParser.identityMatrix) value = true ∧
        formulaEvalWith
          (sectorBitsFormula kind exponent (.one false)) value = true := by
    simpa [activeFormula, formulaEvalWith] using evaluation
  rw [activeFormula, activeOwnerForms_and]
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      RawParser.identityMatrix value evaluated.1 with radialNil | radialSingleton
  · rw [radialNil, List.nil_append]
    rcases
        sectorBitsFormula_one_false_activeOwnerForms_eq_nil_or_sectorSingleton
          kind exponent value evaluated.2 with sectorNil |
          ⟨sector, sectorForm, sectorSingleton, sectorMember⟩
    · simp [sectorNil]
    · simp [sectorSingleton]
  · rw [radialSingleton]
    rcases
        sectorBitsFormula_one_false_activeOwnerForms_eq_nil_or_sectorSingleton
          kind exponent value evaluated.2 with sectorNil |
          ⟨sector, sectorForm, sectorSingleton, sectorMember⟩
    · simp [sectorNil]
    · simp [sectorSingleton]

/-- Generic transfer of a local two-face angle gap through a homographic
formula pullback. -/
theorem pullback_activeOwnerForms_pair_angleGap_of_local
    (formula : Formula) (pullbackMatrix : Mat2 QI)
    (pullbackDeterminantNonzero : determinant pullbackMatrix ≠ 0)
    (value : HermitianForm → ℚ)
    (_evaluation : formulaEvalWith (Formula.pullback pullbackMatrix formula)
      value = true)
    (localPair : ∀ {left right : HermitianForm},
      activeOwnerForms formula
          (fun form => value (pullbackForm pullbackMatrix form)) = [left, right] →
        0 < boundaryDiscriminant left * boundaryDiscriminant right -
          2 * gradientPairingConstant left right ^ 2)
    {left right : HermitianForm}
    (forms : activeOwnerForms (Formula.pullback pullbackMatrix formula) value =
      [left, right]) :
    0 < boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2 := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  rw [activeOwnerForms_pullback] at forms
  change (activeOwnerForms formula localValue).map
      (pullbackForm pullbackMatrix) = [left, right] at forms
  cases localForms : activeOwnerForms formula localValue with
  | nil => simp [localForms] at forms
  | cons localLeft tail =>
      cases tail with
      | nil => simp [localForms] at forms
      | cons localRight rest =>
          cases rest with
          | nil =>
              simp only [localForms, List.map_cons, List.map_nil,
                List.cons.injEq] at forms
              have localPositive := localPair localForms
              rw [← forms.1, ← forms.2.1,
                gradientPairingConstant_pullbackForm,
                boundaryDiscriminant_pullbackForm,
                boundaryDiscriminant_pullbackForm]
              let factor := normSq (determinant pullbackMatrix)
              have factorPositive : 0 < factor :=
                normSq_pos pullbackDeterminantNonzero
              calc
                0 < factor ^ 2 *
                    (boundaryDiscriminant localLeft *
                        boundaryDiscriminant localRight -
                      2 * gradientPairingConstant localLeft localRight ^ 2) :=
                  mul_pos (sq_pos_of_pos factorPositive) localPositive
                _ = factor * boundaryDiscriminant localLeft *
                      (factor * boundaryDiscriminant localRight) -
                    2 * (factor *
                      gradientPairingConstant localLeft localRight) ^ 2 := by
                  ring
          | cons third rest => simp [localForms] at forms

theorem pullbackSectorOneFalseActiveFormula_activeOwnerForms_pair_angleGap
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (pullbackMatrix : Mat2 QI)
    (pullbackDeterminantNonzero : determinant pullbackMatrix ≠ 0)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent (.one false)))) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent (.one false)))) value =
      [left, right]) :
    0 < boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2 := by
  apply pullback_activeOwnerForms_pair_angleGap_of_local
    (activeFormula (.sector kind exponent (.one false))) pullbackMatrix
    pullbackDeterminantNonzero value evaluation
  · intro left right localForms
    apply sectorOneFalseActiveFormula_activeOwnerForms_pair_angleGap kind
      exponent (fun form => value (pullbackForm pullbackMatrix form))
    · rw [← formulaEvalWith_pullback]
      exact evaluation
    · exact localForms
  · exact forms

theorem pullbackSectorOneFalseActiveFormula_activeOwnerForms_length_le_two
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (pullbackMatrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent (.one false)))) value = true) :
    (activeOwnerForms
      (Formula.pullback pullbackMatrix
        (activeFormula (.sector kind exponent (.one false)))) value).length ≤
      2 := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (activeFormula (.sector kind exponent (.one false))) localValue = true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback, List.length_map]
  exact sectorOneFalseActiveFormula_activeOwnerForms_length_le_two kind
    exponent localValue localEvaluation

theorem classifiedTangentDirection?_isSome_sector_zero_false
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output) (selectedFalse : selected.bit = false)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.sector kind exponent .zero, matrix, history⟩) selected).isSome := by
  let formula := Formula.pullback (adjugate matrix)
    (activeFormula (.sector kind exponent (.one false)))
  have formulaIdentity : inputIncrementalAdvanceFormula
      ⟨.sector kind exponent .zero, matrix, history⟩ selected.bit =
        formula := by
    simp [formula, selectedFalse, inputIncrementalAdvanceFormula,
      incrementalAdvanceFormula, RawParser.step]
  have evaluation : formulaEvalWith formula
      (eventPayloadCanonicalValue (state :=
        ⟨.sector kind exponent .zero, matrix, history⟩) selected) = true := by
    rw [← formulaIdentity]
    exact selected.canonical_holds
  have lengthLeTwo :
      (eventPayloadIncrementalActiveOwnerForms (state :=
        ⟨.sector kind exponent .zero, matrix, history⟩) selected).length ≤
          2 := by
    have localLength :=
      pullbackSectorOneFalseActiveFormula_activeOwnerForms_length_le_two kind
        exponent (adjugate matrix)
        (eventPayloadCanonicalValue (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected)
        (by simpa only [formula] using evaluation)
    rw [eventPayloadIncrementalActiveOwnerForms, formulaIdentity]
    simpa only [formula] using localLength
  cases forms : eventPayloadIncrementalActiveOwnerForms (state :=
      ⟨.sector kind exponent .zero, matrix, history⟩) selected with
  | nil => exact classifiedTangentDirection?_isSome_of_nil selected forms
  | cons first tail =>
      cases tail with
      | nil =>
          exact classifiedTangentDirection?_isSome_of_singleton selected
            stateDeterminant forms
      | cons second rest =>
          cases rest with
          | nil =>
              have pulledForms : activeOwnerForms formula
                  (eventPayloadCanonicalValue (state :=
                    ⟨.sector kind exponent .zero, matrix, history⟩) selected) =
                    [first, second] := by
                rw [← formulaIdentity]
                simpa only [eventPayloadIncrementalActiveOwnerForms] using forms
              have angleGapPositive :=
                pullbackSectorOneFalseActiveFormula_activeOwnerForms_pair_angleGap
                  kind exponent (adjugate matrix) (by
                    rw [determinant_adjugate]
                    exact stateDeterminant)
                  (eventPayloadCanonicalValue (state :=
                    ⟨.sector kind exponent .zero, matrix, history⟩) selected)
                  (by simpa only [formula] using evaluation)
                  (by simpa only [formula] using pulledForms)
              exact classifiedTangentDirection?_isSome_of_pair_angleGap
                selected forms angleGapPositive
          | cons third remaining => simp [forms] at lengthLeTwo

/-- The true first-sector-bit formula can repeat its positive-real weak face,
but its complete active list has only five possible shapes. -/
theorem sectorBitsFormula_one_true_activeOwnerForms_shapes
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (sectorBitsFormula kind exponent (.one true)) value = true) :
    let matrix := normalizedMatrix kind exponent RawParser.identityMatrix
    activeOwnerForms (sectorBitsFormula kind exponent (.one true)) value = [] ∨
      activeOwnerForms (sectorBitsFormula kind exponent (.one true)) value =
        [negativeRealOwner matrix] ∨
      activeOwnerForms (sectorBitsFormula kind exponent (.one true)) value =
        [negativeImagOwner matrix] ∨
      activeOwnerForms (sectorBitsFormula kind exponent (.one true)) value =
        [positiveRealOwner matrix, positiveRealOwner matrix] ∨
      activeOwnerForms (sectorBitsFormula kind exponent (.one true)) value =
        [negativeImagOwner matrix, positiveRealOwner matrix,
          positiveRealOwner matrix] := by
  let matrix := normalizedMatrix kind exponent RawParser.identityMatrix
  let positiveReal := realComparisonForm matrix ((2 : ℚ)⁻¹)
  let negativeReal := realComparisonForm matrix (-1 / 2)
  let positiveImag := imagComparisonForm matrix ((2 : ℚ)⁻¹)
  let negativeImag := imagComparisonForm matrix (-1 / 2)
  have evaluated :
      ((value positiveReal < 0 ∨ value negativeImag ≤ 0) ∧
        (0 ≤ value positiveReal ∨ value positiveImag < 0)) ∧
      (0 ≤ value positiveReal ∨ value negativeReal ≤ 0 ∨
        0 ≤ value positiveImag ∨ value negativeImag ≤ 0) := by
    simpa [sectorBitsFormula, matrix, positiveReal, negativeReal,
      positiveImag, negativeImag, formulaEvalWith, SignTest.Holds] using
        evaluation
  by_cases positiveRealNegative : value positiveReal < 0
  · have positiveRealNotNonnegative : ¬0 ≤ value positiveReal := by
      linarith
    have positiveImagNegative : value positiveImag < 0 := by
      rcases evaluated.1.2 with nonnegative | negative
      · linarith
      · exact negative
    have positiveImagNotNonnegative : ¬0 ≤ value positiveImag := by
      linarith
    have positiveRealNonzero : value positiveReal ≠ 0 :=
      positiveRealNegative.ne
    have positiveImagNonzero : value positiveImag ≠ 0 :=
      positiveImagNegative.ne
    by_cases negativeRealNonpositive : value negativeReal ≤ 0
    · by_cases negativeRealZero : value negativeReal = 0
      · exact Or.inr (Or.inl (by
          dsimp only [matrix, positiveReal, negativeReal, positiveImag,
            negativeImag] at *
          simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
            satisfyingAtoms, formulaEvalWith, SignTest.Holds,
            positiveRealNegative, positiveRealNotNonnegative,
            positiveRealNonzero, positiveImagNonzero, negativeRealZero,
            negativeRealOwner, orientedWeakForm]))
      · exact Or.inl (by
          dsimp only [matrix, positiveReal, negativeReal, positiveImag,
            negativeImag] at *
          simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
            satisfyingAtoms, formulaEvalWith, SignTest.Holds,
            positiveRealNegative, positiveRealNotNonnegative,
            positiveRealNonzero, positiveImagNonzero,
            negativeRealNonpositive, negativeRealZero])
    · have negativeImagNonpositive : value negativeImag ≤ 0 := by
        rcases evaluated.2 with positiveRealNonnegative | tail
        · linarith
        · rcases tail with negativeRealLe | tail
          · exact (negativeRealNonpositive negativeRealLe).elim
          · rcases tail with positiveImagNonnegative | negativeImagLe
            · linarith
            · exact negativeImagLe
      by_cases negativeImagZero : value negativeImag = 0
      · exact Or.inr (Or.inr (Or.inl (by
          dsimp only [matrix, positiveReal, negativeReal, positiveImag,
            negativeImag] at *
          simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
            satisfyingAtoms, formulaEvalWith, SignTest.Holds,
            positiveRealNegative, positiveRealNotNonnegative,
            positiveImagNotNonnegative,
            positiveRealNonzero, positiveImagNonzero,
            negativeRealNonpositive,
            negativeImagZero, negativeImagOwner, orientedWeakForm])))
      · exact Or.inl (by
          dsimp only [matrix, positiveReal, negativeReal, positiveImag,
            negativeImag] at *
          simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
            satisfyingAtoms, formulaEvalWith, SignTest.Holds,
            positiveRealNegative, positiveRealNotNonnegative,
            positiveImagNotNonnegative,
            positiveRealNonzero, positiveImagNonzero,
            negativeRealNonpositive,
            negativeImagZero])
  · have positiveRealNonnegative : 0 ≤ value positiveReal :=
      le_of_not_gt positiveRealNegative
    have negativeImagNonpositive : value negativeImag ≤ 0 := by
      rcases evaluated.1.1 with negative | nonpositive
      · exact (positiveRealNegative negative).elim
      · exact nonpositive
    by_cases positiveRealZero : value positiveReal = 0
    · by_cases negativeImagZero : value negativeImag = 0
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by
          dsimp only [matrix, positiveReal, negativeReal, positiveImag,
            negativeImag] at *
          simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
            satisfyingAtoms, formulaEvalWith, SignTest.Holds,
            positiveRealZero, negativeImagZero,
            positiveRealOwner, negativeImagOwner, orientedWeakForm]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by
          dsimp only [matrix, positiveReal, negativeReal, positiveImag,
            negativeImag] at *
          simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
            satisfyingAtoms, formulaEvalWith, SignTest.Holds,
            positiveRealZero, negativeImagZero,
            positiveRealOwner, orientedWeakForm]))))
    · by_cases negativeImagZero : value negativeImag = 0
      · exact Or.inr (Or.inr (Or.inl (by
          dsimp only [matrix, positiveReal, negativeReal, positiveImag,
            negativeImag] at *
          simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
            satisfyingAtoms, formulaEvalWith, SignTest.Holds,
            positiveRealNegative, positiveRealNonnegative,
            positiveRealZero, negativeImagZero,
            negativeImagOwner, orientedWeakForm])))
      · exact Or.inl (by
          dsimp only [matrix, positiveReal, negativeReal, positiveImag,
            negativeImag] at *
          simp [sectorBitsFormula, activeOwnerForms, activeSatisfyingAtoms,
            satisfyingAtoms, formulaEvalWith, SignTest.Holds,
            positiveRealNegative, positiveRealNonnegative,
            positiveRealZero, negativeImagZero])

/-- A positive angle gap is preserved by every nondegenerate homographic
pullback. -/
theorem pullback_angleGap_pos
    (pullbackMatrix : Mat2 QI)
    (pullbackDeterminantNonzero : determinant pullbackMatrix ≠ 0)
    (left right : HermitianForm)
    (localPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    0 < boundaryDiscriminant (pullbackForm pullbackMatrix left) *
          boundaryDiscriminant (pullbackForm pullbackMatrix right) -
        2 * gradientPairingConstant (pullbackForm pullbackMatrix left)
          (pullbackForm pullbackMatrix right) ^ 2 := by
  rw [gradientPairingConstant_pullbackForm,
    boundaryDiscriminant_pullbackForm,
    boundaryDiscriminant_pullbackForm]
  let factor := normSq (determinant pullbackMatrix)
  have factorPositive : 0 < factor :=
    normSq_pos pullbackDeterminantNonzero
  calc
    0 < factor ^ 2 *
        (boundaryDiscriminant left * boundaryDiscriminant right -
          2 * gradientPairingConstant left right ^ 2) :=
      mul_pos (sq_pos_of_pos factorPositive) localPositive
    _ = factor * boundaryDiscriminant left *
          (factor * boundaryDiscriminant right) -
        2 * (factor * gradientPairingConstant left right) ^ 2 := by
      ring

theorem gradientPairingConstant_negativeImag_positiveReal
    (matrix : Mat2 QI) :
    gradientPairingConstant (negativeImagOwner matrix)
        (positiveRealOwner matrix) = 0 := by
  calc
    gradientPairingConstant (negativeImagOwner matrix)
        (positiveRealOwner matrix) =
        -gradientPairingConstant
          (realComparisonForm matrix (1 / 2))
          (imagComparisonForm matrix (-1 / 2)) := by
      simp only [negativeImagOwner, positiveRealOwner,
        gradientPairingConstant, HermitianForm.neg]
      ring
    _ = 0 := by
      rw [gradientPairingConstant_real_imag]
      norm_num

theorem gradientPairingConstant_pullback_negativeImag_positiveReal
    (pullbackMatrix matrix : Mat2 QI) :
    gradientPairingConstant
        (pullbackForm pullbackMatrix (negativeImagOwner matrix))
        (pullbackForm pullbackMatrix (positiveRealOwner matrix)) = 0 := by
  rw [gradientPairingConstant_pullbackForm,
    gradientPairingConstant_negativeImag_positiveReal]
  exact mul_zero _

/-- Repeating one active owner face does not change a direction that is
strictly inward for it. -/
theorem classifiedTangentDirection?_isSome_of_duplicate
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (stateDeterminant : determinant state.matrix ≠ 0)
    {form : HermitianForm}
    (forms : eventPayloadIncrementalActiveOwnerForms selected = [form, form]) :
    (classifiedTangentDirection? selected).isSome := by
  have formMember : form ∈
      eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  rcases exists_classified_axis_direction_single_of_stateDeterminant selected
      stateDeterminant formMember with
    ⟨direction, directionMember, slopePositive⟩
  apply classifiedTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using slopePositive

/-- A common-positive direction for two faces also handles a repeated copy
of the second face. -/
theorem classifiedTangentDirection?_isSome_of_pair_repeat_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (forms : eventPayloadIncrementalActiveOwnerForms selected =
      [left, right, right])
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    (classifiedTangentDirection? selected).isSome := by
  have leftMember : left ∈
      eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  have rightMember : right ∈
      eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  rcases exists_classified_direction_pair_of_angleGap selected leftMember
      rightMember angleGapPositive with
    ⟨direction, directionMember, leftPositive, rightPositive⟩
  apply classifiedTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using And.intro leftPositive rightPositive

/-- The orthogonal-coordinate pair search likewise tolerates a repeated
second face. -/
theorem classifiedTangentDirection?_isSome_of_pair_repeat_pairingConstant_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (stateDeterminant : determinant state.matrix ≠ 0)
    {left right : HermitianForm}
    (forms : eventPayloadIncrementalActiveOwnerForms selected =
      [left, right, right])
    (constantZero : gradientPairingConstant left right = 0) :
    (classifiedTangentDirection? selected).isSome := by
  have leftMember : left ∈
      eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  have rightMember : right ∈
      eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  have dotDivides :=
    selectedGradientDotPolynomial_dvd_of_pairingConstant_zero selected
      leftMember rightMember constantZero
  rcases exists_classified_direction_pair_of_gradientDot_dvd selected
      leftMember rightMember
      (selectedIncrementalActiveOwner_boundaryDiscriminant_ne selected
        stateDeterminant leftMember)
      (selectedIncrementalActiveOwner_boundaryDiscriminant_ne selected
        stateDeterminant rightMember)
      dotDivides with
    ⟨direction, directionMember, leftPositive, rightPositive⟩
  apply classifiedTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using And.intro leftPositive rightPositive

/-- The only four-entry true-one-bit shape is algebraically impossible: its
three distinct faces are the normalized radial circle and the south-east
coordinate corner. -/
theorem selectedSectorOneTrueActiveOwnerForms_ne_four
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (stateDeterminantNonzero : determinant state.matrix ≠ 0)
    (forms : eventPayloadIncrementalActiveOwnerForms selected =
      [radialOwnerForm kind exponent (adjugate state.matrix),
        negativeImagOwner
          (normalizedMatrix kind exponent (adjugate state.matrix)),
        positiveRealOwner
          (normalizedMatrix kind exponent (adjugate state.matrix)),
        positiveRealOwner
          (normalizedMatrix kind exponent (adjugate state.matrix))]) :
    False := by
  let normalized := normalizedMatrix kind exponent (adjugate state.matrix)
  let decoderLower := selectedSlopeDecoderDenominatorPositiveLowerBound
    selected stateDeterminantNonzero
  have normalizedLower : FTA.PositiveLowerBound.Certificate
      (clearedForm (affineNormForm normalized.c normalized.d)
        (selectedPath selected))
      (selectedSlopeSigns selected).refined.interval := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent
      (adjugate state.matrix)
    dsimp only [normalized]
    rw [lowerRow.1, lowerRow.2]
    exact decoderLower
  have radialMember :
      HermitianForm.scale (normalizedRadialOwnerScale kind exponent)
          (normComparisonForm normalized (normalizedRadialRadius kind)) ∈
        eventPayloadIncrementalActiveOwnerForms selected := by
    rw [← radialOwnerForm_eq_scale_normalized]
    simp [forms]
  apply selectedSlope_scaled_norm_real_imag_not_all_active selected
    normalized (normalizedRadialRadius kind) (1 / 2) (-1 / 2)
    (normalizedRadialOwnerScale kind exponent) 1 (-1)
  · exact normalizedRadialOwnerScale_ne kind exponent
  · norm_num
  · norm_num
  · have gap := normalizedCorner_radius_gap_ne kind
    norm_num at gap ⊢
    exact gap
  · exact normalizedLower
  · exact radialMember
  · simp [normalized, forms, positiveRealOwner]
  · simp [normalized, forms, negativeImagOwner]

/-- The remaining true first-sector-bit transition has a total executable
tangent search, despite its syntactically repeated positive-real face. -/
theorem classifiedTangentDirection?_isSome_sector_zero_true
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output) (selectedTrue : selected.bit = true)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.sector kind exponent .zero, matrix, history⟩) selected).isSome := by
  let formula := Formula.pullback (adjugate matrix)
    (activeFormula (.sector kind exponent (.one true)))
  have formulaIdentity : inputIncrementalAdvanceFormula
      ⟨.sector kind exponent .zero, matrix, history⟩ selected.bit =
        formula := by
    simp [formula, selectedTrue, inputIncrementalAdvanceFormula,
      incrementalAdvanceFormula, RawParser.step]
  have evaluation : formulaEvalWith formula
      (eventPayloadCanonicalValue (state :=
        ⟨.sector kind exponent .zero, matrix, history⟩) selected) = true := by
    rw [← formulaIdentity]
    exact selected.canonical_holds
  let localValue : HermitianForm → ℚ := fun form =>
    eventPayloadCanonicalValue (state :=
      ⟨.sector kind exponent .zero, matrix, history⟩) selected
        (pullbackForm (adjugate matrix) form)
  have localEvaluation : formulaEvalWith
      (activeFormula (.sector kind exponent (.one true))) localValue = true := by
    rw [← formulaEvalWith_pullback]
    simpa only [formula] using evaluation
  have evaluated :
      formulaEvalWith
          (radialFormula kind exponent RawParser.identityMatrix) localValue =
          true ∧
        formulaEvalWith
          (sectorBitsFormula kind exponent (.one true)) localValue = true := by
    simpa [activeFormula, formulaEvalWith] using localEvaluation
  have formsIdentity :
      eventPayloadIncrementalActiveOwnerForms (state :=
        ⟨.sector kind exponent .zero, matrix, history⟩) selected =
      (activeOwnerForms
          (radialFormula kind exponent RawParser.identityMatrix) localValue ++
        activeOwnerForms
          (sectorBitsFormula kind exponent (.one true)) localValue).map
            (pullbackForm (adjugate matrix)) := by
    rw [eventPayloadIncrementalActiveOwnerForms, formulaIdentity]
    simp only [formula, activeOwnerForms_pullback, activeFormula,
      activeOwnerForms_and]
    dsimp only [localValue]
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      RawParser.identityMatrix localValue evaluated.1 with
    radialNil | radialSingleton
  · rcases sectorBitsFormula_one_true_activeOwnerForms_shapes kind exponent
        localValue evaluated.2 with
      sectorNil | sectorNegativeReal | sectorNegativeImag |
        sectorPositiveRealDuplicate | sectorSouthEastDuplicate
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected = [] := by
        simpa [radialNil, sectorNil] using formsIdentity
      exact classifiedTangentDirection?_isSome_of_nil selected forms
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected =
          [negativeRealOwner
            (normalizedMatrix kind exponent (adjugate matrix))] := by
        simpa [radialNil, sectorNegativeReal] using formsIdentity
      exact classifiedTangentDirection?_isSome_of_singleton selected
        stateDeterminant forms
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected =
          [negativeImagOwner
            (normalizedMatrix kind exponent (adjugate matrix))] := by
        simpa [radialNil, sectorNegativeImag] using formsIdentity
      exact classifiedTangentDirection?_isSome_of_singleton selected
        stateDeterminant forms
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected =
          [positiveRealOwner
              (normalizedMatrix kind exponent (adjugate matrix)),
            positiveRealOwner
              (normalizedMatrix kind exponent (adjugate matrix))] := by
        simpa [radialNil, sectorPositiveRealDuplicate] using formsIdentity
      exact classifiedTangentDirection?_isSome_of_duplicate selected
        stateDeterminant forms
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected =
          [negativeImagOwner
              (normalizedMatrix kind exponent (adjugate matrix)),
            positiveRealOwner
              (normalizedMatrix kind exponent (adjugate matrix)),
            positiveRealOwner
              (normalizedMatrix kind exponent (adjugate matrix))] := by
        simpa [radialNil, sectorSouthEastDuplicate] using formsIdentity
      apply classifiedTangentDirection?_isSome_of_pair_repeat_pairingConstant_zero
        selected stateDeterminant forms
      simpa only [pullbackForm_negativeImagOwner,
        pullbackForm_positiveRealOwner, normalizedMatrix_identity_mul] using
        gradientPairingConstant_pullback_negativeImag_positiveReal
          (adjugate matrix)
          (normalizedMatrix kind exponent RawParser.identityMatrix)
  · rcases sectorBitsFormula_one_true_activeOwnerForms_shapes kind exponent
        localValue evaluated.2 with
      sectorNil | sectorNegativeReal | sectorNegativeImag |
        sectorPositiveRealDuplicate | sectorSouthEastDuplicate
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected =
          [radialOwnerForm kind exponent (adjugate matrix)] := by
        rw [radialSingleton, sectorNil] at formsIdentity
        simpa only [List.append_nil, List.map_cons, List.map_nil,
          pullbackForm_radialOwnerForm, identityMatrix_mul] using formsIdentity
      exact classifiedTangentDirection?_isSome_of_singleton selected
        stateDeterminant forms
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected =
          [radialOwnerForm kind exponent (adjugate matrix),
            negativeRealOwner
              (normalizedMatrix kind exponent (adjugate matrix))] := by
        rw [radialSingleton, sectorNegativeReal] at formsIdentity
        simpa only [List.singleton_append, List.map_cons, List.map_nil,
          pullbackForm_radialOwnerForm, identityMatrix_mul,
          pullbackForm_negativeRealOwner, normalizedMatrix_identity_mul] using
            formsIdentity
      apply classifiedTangentDirection?_isSome_of_pair_angleGap selected forms
      have pulledGap := pullback_angleGap_pos (adjugate matrix) (by
          rw [determinant_adjugate]
          exact stateDeterminant)
        (radialOwnerForm kind exponent RawParser.identityMatrix)
        (negativeRealOwner
          (normalizedMatrix kind exponent RawParser.identityMatrix))
        (radialOwner_sectorOwner_angleGap_pos kind exponent .west
          RawParser.identityMatrix (by
            norm_num [determinant, RawParser.identityMatrix]) (by
              simp [sectorOwnerForms]))
      simpa only [pullbackForm_radialOwnerForm, identityMatrix_mul,
        pullbackForm_negativeRealOwner, normalizedMatrix_identity_mul] using
          pulledGap
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected =
          [radialOwnerForm kind exponent (adjugate matrix),
            negativeImagOwner
              (normalizedMatrix kind exponent (adjugate matrix))] := by
        rw [radialSingleton, sectorNegativeImag] at formsIdentity
        simpa only [List.singleton_append, List.map_cons, List.map_nil,
          pullbackForm_radialOwnerForm, identityMatrix_mul,
          pullbackForm_negativeImagOwner, normalizedMatrix_identity_mul] using
            formsIdentity
      apply classifiedTangentDirection?_isSome_of_pair_angleGap selected forms
      have pulledGap := pullback_angleGap_pos (adjugate matrix) (by
          rw [determinant_adjugate]
          exact stateDeterminant)
        (radialOwnerForm kind exponent RawParser.identityMatrix)
        (negativeImagOwner
          (normalizedMatrix kind exponent RawParser.identityMatrix))
        (radialOwner_sectorOwner_angleGap_pos kind exponent .south
          RawParser.identityMatrix (by
            norm_num [determinant, RawParser.identityMatrix]) (by
              simp [sectorOwnerForms]))
      simpa only [pullbackForm_radialOwnerForm, identityMatrix_mul,
        pullbackForm_negativeImagOwner, normalizedMatrix_identity_mul] using
          pulledGap
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected =
          [radialOwnerForm kind exponent (adjugate matrix),
            positiveRealOwner
              (normalizedMatrix kind exponent (adjugate matrix)),
            positiveRealOwner
              (normalizedMatrix kind exponent (adjugate matrix))] := by
        rw [radialSingleton, sectorPositiveRealDuplicate] at formsIdentity
        simpa only [List.singleton_append, List.map_cons, List.map_nil,
          pullbackForm_radialOwnerForm, identityMatrix_mul,
          pullbackForm_positiveRealOwner, normalizedMatrix_identity_mul] using
            formsIdentity
      apply classifiedTangentDirection?_isSome_of_pair_repeat_angleGap selected
        forms
      have pulledGap := pullback_angleGap_pos (adjugate matrix) (by
          rw [determinant_adjugate]
          exact stateDeterminant)
        (radialOwnerForm kind exponent RawParser.identityMatrix)
        (positiveRealOwner
          (normalizedMatrix kind exponent RawParser.identityMatrix))
        (radialOwner_sectorOwner_angleGap_pos kind exponent .east
          RawParser.identityMatrix (by
            norm_num [determinant, RawParser.identityMatrix]) (by
              simp [sectorOwnerForms]))
      simpa only [pullbackForm_radialOwnerForm, identityMatrix_mul,
        pullbackForm_positiveRealOwner, normalizedMatrix_identity_mul] using
          pulledGap
    · have forms : eventPayloadIncrementalActiveOwnerForms (state :=
          ⟨.sector kind exponent .zero, matrix, history⟩) selected =
          [radialOwnerForm kind exponent (adjugate matrix),
            negativeImagOwner
              (normalizedMatrix kind exponent (adjugate matrix)),
            positiveRealOwner
              (normalizedMatrix kind exponent (adjugate matrix)),
            positiveRealOwner
              (normalizedMatrix kind exponent (adjugate matrix))] := by
        rw [radialSingleton, sectorSouthEastDuplicate] at formsIdentity
        simpa only [List.singleton_append, List.map_cons, List.map_nil,
          pullbackForm_radialOwnerForm, identityMatrix_mul,
          pullbackForm_negativeImagOwner, pullbackForm_positiveRealOwner,
          normalizedMatrix_identity_mul] using formsIdentity
      exact (selectedSectorOneTrueActiveOwnerForms_ne_four selected kind exponent
        stateDeterminant forms).elim

/-- Once the parser already has two sector bits, the incremental and complete
classifiers receive the same active-face list and therefore run the same
finite sign refinement. -/
theorem selectedSlopeConditions_eq_complete_of_completedPhase
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second)) :
    selectedSlopeConditions selected.toIncrementalPayload =
      selectedCompleteSlopeConditions selected :=
  by
    simp only [selectedSlopeConditions, selectedCompleteSlopeConditions,
      eventPayloadIncrementalActiveOwnerForms_eq_active_of_completedSector
        selected phase, selectedPath_toIncrementalPayload,
      selectedCompletePath]

theorem classifiedTangentDirection?_eq_complete_of_completedPhase
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second)) :
    classifiedTangentDirection? selected.toIncrementalPayload =
      classifiedCompleteTangentDirection? selected := by
  unfold classifiedTangentDirection? classifiedCompleteTangentDirection?
  unfold classifiedSlopesPositive? classifiedCompleteSlopesPositive?
  rw [eventPayloadIncrementalActiveOwnerForms_eq_active_of_completedSector
    selected phase]
  unfold selectedSlopeValue selectedCompleteSlopeValue
  unfold selectedSlopeSigns selectedCompleteSlopeSigns
  unfold selectedSlopeClassification selectedCompleteSlopeClassification
  rw [selectedSlopeConditions_eq_complete_of_completedPhase selected phase]
  simp only [toIncrementalPayload_candidate,
    selectedPath_toIncrementalPayload, selectedCompletePath]
  rfl

/-- Every finite raw-parser phase has a total incremental tangent search once
its decoder and stored history matrices are certified invertible. -/
theorem classifiedTangentDirection?_isSome_of_state
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible state) :
    (classifiedTangentDirection? selected.toIncrementalPayload).isSome := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      exact classifiedTangentDirection?_isSome_initial
        selected.toIncrementalPayload
        stateDeterminant
  | highUnary count =>
      cases selectedBit : selected.bit
      · exact classifiedTangentDirection?_isSome_highUnary_false
          selected.toIncrementalPayload
          selectedBit stateDeterminant
      · exact classifiedTangentDirection?_isSome_highUnary_true
          selected.toIncrementalPayload
          selectedBit stateDeterminant
  | lowUnary count =>
      cases selectedBit : selected.bit
      · exact classifiedTangentDirection?_isSome_lowUnary_false
          selected.toIncrementalPayload
          selectedBit stateDeterminant
      · exact classifiedTangentDirection?_isSome_lowUnary_true
          selected.toIncrementalPayload
          selectedBit stateDeterminant
  | loopUnary count =>
      cases selectedBit : selected.bit
      · exact classifiedTangentDirection?_isSome_loopUnary_false
          selected.toIncrementalPayload
          selectedBit stateDeterminant
      · exact classifiedTangentDirection?_isSome_loopUnary_true
          selected.toIncrementalPayload
          selectedBit stateDeterminant
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          cases selectedBit : selected.bit
          · exact classifiedTangentDirection?_isSome_sector_zero_false
              selected.toIncrementalPayload
              selectedBit stateDeterminant
          · exact classifiedTangentDirection?_isSome_sector_zero_true
              selected.toIncrementalPayload
              selectedBit stateDeterminant
      | one first =>
          exact classifiedTangentDirection?_isSome_sector_one
            selected.toIncrementalPayload
            stateDeterminant
      | two first second =>
          rw [classifiedTangentDirection?_eq_complete_of_completedPhase
            selected rfl]
          exact classifiedCompleteTangentDirection?_isSome_of_completedPhase
            selected rfl stateDeterminant historyValid

/-- Every non-completed finite parser phase has a total history-free tangent
search.  No current-formula or historical owner premise is used. -/
theorem classifiedTangentDirection?_isSome_of_state_notCompleted
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (notCompleted : ¬∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)) :
    (classifiedTangentDirection? selected).isSome := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      exact classifiedTangentDirection?_isSome_initial selected
        stateDeterminant
  | highUnary count =>
      cases selectedBit : selected.bit
      · exact classifiedTangentDirection?_isSome_highUnary_false selected
          selectedBit stateDeterminant
      · exact classifiedTangentDirection?_isSome_highUnary_true selected
          selectedBit stateDeterminant
  | lowUnary count =>
      cases selectedBit : selected.bit
      · exact classifiedTangentDirection?_isSome_lowUnary_false selected
          selectedBit stateDeterminant
      · exact classifiedTangentDirection?_isSome_lowUnary_true selected
          selectedBit stateDeterminant
  | loopUnary count =>
      cases selectedBit : selected.bit
      · exact classifiedTangentDirection?_isSome_loopUnary_false selected
          selectedBit stateDeterminant
      · exact classifiedTangentDirection?_isSome_loopUnary_true selected
          selectedBit stateDeterminant
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          cases selectedBit : selected.bit
          · exact classifiedTangentDirection?_isSome_sector_zero_false selected
              selectedBit stateDeterminant
          · exact classifiedTangentDirection?_isSome_sector_zero_true selected
              selectedBit stateDeterminant
      | one first =>
          exact classifiedTangentDirection?_isSome_sector_one selected
            stateDeterminant
      | two first second =>
          exact (notCompleted ⟨kind, exponent, first, second, rfl⟩).elim

/-- Executable direction for a parsed history-free owner outside a completed
sector. -/
def parsedIncrementalClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    (selected : IncrementalEventPayload output)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second)) : QI :=
  (classifiedTangentDirection? selected).get
    (classifiedTangentDirection?_isSome_of_state_notCompleted selected
      (RawParser.parse_det_ne word) notCompleted)

theorem parsedIncrementalClassifiedTangentDirection_spec
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    (selected : IncrementalEventPayload output)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second)) :
    classifiedTangentDirection? selected =
      some (parsedIncrementalClassifiedTangentDirection selected
        notCompleted) :=
  Option.eq_some_of_isSome
    (classifiedTangentDirection?_isSome_of_state_notCompleted selected
      (RawParser.parse_det_ne word) notCompleted)

/-- Parser-produced states discharge both invariants required by the phase
totality theorem. -/
theorem classifiedTangentDirection?_isSome_of_parsed
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    (selected : SelectedEventPayload output) :
    (classifiedTangentDirection? selected.toIncrementalPayload).isSome := by
  apply classifiedTangentDirection?_isSome_of_state selected
  · exact RawParser.parse_det_ne word
  · exact parse_historyMatricesInvertible word

/-- Executable compass direction selected for an arbitrary parsed phase. -/
def parsedClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    (selected : SelectedEventPayload output) : QI :=
  (classifiedTangentDirection? selected.toIncrementalPayload).get
    (classifiedTangentDirection?_isSome_of_parsed selected)

theorem parsedClassifiedTangentDirection_spec
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    (selected : SelectedEventPayload output) :
    classifiedTangentDirection? selected.toIncrementalPayload =
      some (parsedClassifiedTangentDirection selected) :=
  Option.eq_some_of_isSome
    (classifiedTangentDirection?_isSome_of_parsed selected)

end CCLIncrementalPhaseCompatibility
end FTA
