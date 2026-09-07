import FTA.CCLCompleteOwnerShapes
import FTA.CCLSectorTangent

/-!
# Compatibility of complete parser owner faces

Finite parser formula shapes restrict which weak boundaries can be active at
the same event.  This module records those restrictions in the algebraic form
consumed by the complete eight-direction tangent search.
-/

namespace FTA
namespace CCLCompleteOwnerCompatibility

open CCL CCL.GaussianRat
open FTA.CCLBranchPlan
open FTA.CCLBranchEventOwner
open FTA.CCLNextBitFormula
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventSemantics
open FTA.CCLSectorTangent

abbrev QI := CCL.GaussianRat

/-- Homographic pullback scales the gradient-pairing obstruction by the
squared norm of the matrix determinant. -/
theorem gradientPairingConstant_pullbackForm
    (pullbackMatrix : Mat2 QI) (left right : HermitianForm) :
    gradientPairingConstant (pullbackForm pullbackMatrix left)
        (pullbackForm pullbackMatrix right) =
      normSq (determinant pullbackMatrix) *
        gradientPairingConstant left right := by
  simp only [gradientPairingConstant, pullbackForm, HermitianForm.add,
    HermitianForm.scale, affineNormForm, realCrossForm, imagCrossForm,
    determinant, normSq, mul_re, mul_im, sub_re, sub_im]
  ring

/-- A radial circle and a real-coordinate boundary through the same
homography have pairing determined only by the coordinate threshold. -/
theorem gradientPairingConstant_norm_real
    (matrix : Mat2 QI) (radiusSq realThreshold : ℚ) :
    gradientPairingConstant (normComparisonForm matrix radiusSq)
        (realComparisonForm matrix realThreshold) =
      2 * realThreshold * normSq (determinant matrix) := by
  simp only [gradientPairingConstant, normComparisonForm,
    realComparisonForm, HermitianForm.sub, HermitianForm.add,
    HermitianForm.neg, HermitianForm.scale, affineNormForm, realCrossForm,
    determinant, normSq, mul_re, mul_im, sub_re, sub_im]
  ring

/-- Imaginary-coordinate version of the radial/coordinate pairing law. -/
theorem gradientPairingConstant_norm_imag
    (matrix : Mat2 QI) (radiusSq imagThreshold : ℚ) :
    gradientPairingConstant (normComparisonForm matrix radiusSq)
        (imagComparisonForm matrix imagThreshold) =
      2 * imagThreshold * normSq (determinant matrix) := by
  simp only [gradientPairingConstant, normComparisonForm,
    imagComparisonForm, HermitianForm.sub, HermitianForm.add,
    HermitianForm.neg, HermitianForm.scale, affineNormForm, imagCrossForm,
    determinant, normSq, mul_re, mul_im, sub_re, sub_im]
  ring

/-- Parser normalization rotates and rescales the sector coordinates but does
not change the radial/real pairing constant before the shared decoder
pullback. -/
@[simp] theorem gradientPairingConstant_norm_normalizedReal
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (radiusSq realThreshold : ℚ) :
    gradientPairingConstant (normComparisonForm matrix radiusSq)
        (realComparisonForm (normalizedMatrix kind exponent matrix)
          realThreshold) =
      2 * realThreshold * normSq (determinant matrix) := by
  cases kind <;>
    simp only [gradientPairingConstant, normComparisonForm,
      realComparisonForm, normalizedMatrix, normalizationMatrix, Mat2.mul,
      Mat2.scale, HermitianForm.sub, HermitianForm.add, HermitianForm.neg,
      HermitianForm.scale, affineNormForm, realCrossForm, determinant, normSq,
      mul_re, mul_im, add_re, add_im, sub_re, sub_im, zero_mul, one_mul,
      zero_add, zero_re, zero_im] <;>
    ring

/-- Imaginary-coordinate version of normalized radial/sector pairing. -/
@[simp] theorem gradientPairingConstant_norm_normalizedImag
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (radiusSq imagThreshold : ℚ) :
    gradientPairingConstant (normComparisonForm matrix radiusSq)
        (imagComparisonForm (normalizedMatrix kind exponent matrix)
          imagThreshold) =
      2 * imagThreshold * normSq (determinant matrix) := by
  cases kind <;>
    simp only [gradientPairingConstant, normComparisonForm,
      imagComparisonForm, normalizedMatrix, normalizationMatrix, Mat2.mul,
      Mat2.scale, HermitianForm.sub, HermitianForm.add, HermitianForm.neg,
      HermitianForm.scale, affineNormForm, imagCrossForm, determinant, normSq,
      mul_re, mul_im, add_re, add_im, sub_re, sub_im, zero_mul, one_mul,
      zero_add, zero_re, zero_im] <;>
    ring

/-- The unique possible weak radial owner of a completed block, oriented
toward the accepted annulus. -/
def radialOwnerForm
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    HermitianForm :=
  match kind with
  | .initialHigh => normComparisonForm matrix ((2 : ℚ) ^ exponent)
  | .initialLow => normComparisonForm matrix (1 / (2 : ℚ) ^ exponent)
  | .loop => (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))).neg

/-- Squared radial boundary after the parser's normalizing rotation/scale. -/
def normalizedRadialRadius : RawParser.BlockKind → ℚ
  | .initialHigh | .initialLow => 1
  | .loop => 2

/-- Nonzero scalar relating the original oriented radial owner to its
normalized-radius presentation. -/
def normalizedRadialOwnerScale
    (kind : RawParser.BlockKind) (exponent : ℕ) : ℚ :=
  match kind with
  | .initialHigh => (2 : ℚ) ^ exponent
  | .initialLow => ((2 : ℚ) ^ exponent)⁻¹
  | .loop => -((2 : ℚ) ^ exponent)

theorem normalizedRadialOwnerScale_ne
    (kind : RawParser.BlockKind) (exponent : ℕ) :
    normalizedRadialOwnerScale kind exponent ≠ 0 := by
  cases kind <;> simp [normalizedRadialOwnerScale]

/-- Norm forms commute with a common Gaussian scaling of their affine
numerator pair. -/
theorem affineNormForm_mul_left
    (scaleValue u v : QI) :
    affineNormForm (scaleValue * u) (scaleValue * v) =
      HermitianForm.scale (normSq scaleValue) (affineNormForm u v) := by
  apply HermitianForm.ext <;>
    simp only [affineNormForm, HermitianForm.scale, normSq, mul_re, mul_im] <;>
    ring

/-- Expanded norm comparison for a matrix whose numerator row is scaled. -/
theorem normComparisonForm_scaleMatrix
    (scaleValue : QI) (matrix : Mat2 QI) (radius : ℚ) :
    normComparisonForm (Mat2.mul (Mat2.scale scaleValue) matrix) radius =
      HermitianForm.sub
        (HermitianForm.scale (normSq scaleValue)
          (affineNormForm matrix.a matrix.b))
        (HermitianForm.scale radius
          (affineNormForm matrix.c matrix.d)) := by
  simp only [normComparisonForm, Mat2.mul, Mat2.scale, zero_mul, one_mul,
    zero_add, add_zero, affineNormForm_mul_left]

/-- The oriented radial owner is a nonzero rational multiple of the norm
comparison through the normalized sector matrix. -/
theorem radialOwnerForm_eq_scale_normalized
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    radialOwnerForm kind exponent matrix =
      HermitianForm.scale (normalizedRadialOwnerScale kind exponent)
        (normComparisonForm (normalizedMatrix kind exponent matrix)
          (normalizedRadialRadius kind)) := by
  cases kind with
  | initialHigh =>
      rw [normalizedMatrix, normalizationMatrix,
        normComparisonForm_scaleMatrix]
      apply HermitianForm.ext <;>
        simp only [radialOwnerForm, normalizedRadialOwnerScale,
          normalizedRadialRadius, normComparisonForm, HermitianForm.sub,
          HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
          normSq_inv _ (RawParser.natPow_gamma_ne exponent),
          normSq_natPow, normSq_gamma] <;>
        field_simp
  | initialLow =>
      rw [normalizedMatrix, normalizationMatrix,
        normComparisonForm_scaleMatrix]
      apply HermitianForm.ext <;>
        simp only [radialOwnerForm, normalizedRadialOwnerScale,
          normalizedRadialRadius, normComparisonForm, HermitianForm.sub,
          HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
          normSq_natPow, normSq_gamma] <;>
        field_simp
  | loop =>
      rw [normalizedMatrix, normalizationMatrix,
        normComparisonForm_scaleMatrix]
      apply HermitianForm.ext <;>
        simp only [radialOwnerForm, normalizedRadialOwnerScale,
          normalizedRadialRadius, normComparisonForm, HermitianForm.sub,
          HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
          normSq_inv _ (RawParser.natPow_gamma_ne exponent),
          normSq_natPow, normSq_gamma, pow_succ] <;>
        field_simp

theorem normalizedCorner_radius_gap_ne
    (kind : RawParser.BlockKind) :
    (1 / 2 : ℚ) ^ 2 + (1 / 2 : ℚ) ^ 2 -
        normalizedRadialRadius kind ≠ 0 := by
  cases kind <;> norm_num [normalizedRadialRadius]

@[simp] theorem HermitianForm.scale_one (form : HermitianForm) :
    HermitianForm.scale 1 form = form := by
  ext <;> simp [HermitianForm.scale]

@[simp] theorem HermitianForm.scale_neg_one (form : HermitianForm) :
    HermitianForm.scale (-1) form = form.neg := by
  ext <;> simp [HermitianForm.scale, HermitianForm.neg]

@[simp] theorem pullbackForm_radialOwnerForm
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (matrix pullbackMatrix : Mat2 QI) :
    pullbackForm pullbackMatrix (radialOwnerForm kind exponent matrix) =
      radialOwnerForm kind exponent (Mat2.mul matrix pullbackMatrix) := by
  cases kind <;>
    simp [radialOwnerForm, pullbackForm_normComparison, pullbackForm_neg]

@[simp] theorem pullbackForm_positiveRealOwner
    (matrix pullbackMatrix : Mat2 QI) :
    pullbackForm pullbackMatrix (positiveRealOwner matrix) =
      positiveRealOwner (Mat2.mul matrix pullbackMatrix) := by
  simp [positiveRealOwner, pullbackForm_realComparison]

@[simp] theorem pullbackForm_negativeRealOwner
    (matrix pullbackMatrix : Mat2 QI) :
    pullbackForm pullbackMatrix (negativeRealOwner matrix) =
      negativeRealOwner (Mat2.mul matrix pullbackMatrix) := by
  simp [negativeRealOwner, pullbackForm_realComparison, pullbackForm_neg]

@[simp] theorem pullbackForm_positiveImagOwner
    (matrix pullbackMatrix : Mat2 QI) :
    pullbackForm pullbackMatrix (positiveImagOwner matrix) =
      positiveImagOwner (Mat2.mul matrix pullbackMatrix) := by
  simp [positiveImagOwner, pullbackForm_imagComparison]

@[simp] theorem pullbackForm_negativeImagOwner
    (matrix pullbackMatrix : Mat2 QI) :
    pullbackForm pullbackMatrix (negativeImagOwner matrix) =
      negativeImagOwner (Mat2.mul matrix pullbackMatrix) := by
  simp [negativeImagOwner, pullbackForm_imagComparison, pullbackForm_neg]

@[simp] theorem normalizedMatrix_identity_mul
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    Mat2.mul (normalizedMatrix kind exponent RawParser.identityMatrix) matrix =
      normalizedMatrix kind exponent matrix := by
  cases kind <;>
    ext <;>
    simp [normalizedMatrix, normalizationMatrix, RawParser.identityMatrix,
      Mat2.mul, Mat2.scale]

@[simp] theorem identityMatrix_mul (matrix : Mat2 QI) :
    Mat2.mul RawParser.identityMatrix matrix = matrix := by
  ext <;> simp [RawParser.identityMatrix, Mat2.mul]

theorem abs_gradientPairingConstant_radialOwner_positiveReal
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    |gradientPairingConstant (radialOwnerForm kind exponent matrix)
        (positiveRealOwner (normalizedMatrix kind exponent matrix))| =
      normSq (determinant matrix) := by
  cases kind <;>
    simp [radialOwnerForm, positiveRealOwner,
      abs_of_nonneg (normSq_nonneg (determinant matrix))]

theorem abs_gradientPairingConstant_radialOwner_negativeReal
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    |gradientPairingConstant (radialOwnerForm kind exponent matrix)
        (negativeRealOwner (normalizedMatrix kind exponent matrix))| =
      normSq (determinant matrix) := by
  cases kind <;>
    simp [radialOwnerForm, negativeRealOwner,
      abs_of_nonneg (normSq_nonneg (determinant matrix))] <;>
    norm_num

theorem abs_gradientPairingConstant_radialOwner_positiveImag
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    |gradientPairingConstant (radialOwnerForm kind exponent matrix)
        (positiveImagOwner (normalizedMatrix kind exponent matrix))| =
      normSq (determinant matrix) := by
  cases kind <;>
    simp [radialOwnerForm, positiveImagOwner,
      abs_of_nonneg (normSq_nonneg (determinant matrix))]

theorem abs_gradientPairingConstant_radialOwner_negativeImag
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    |gradientPairingConstant (radialOwnerForm kind exponent matrix)
        (negativeImagOwner (normalizedMatrix kind exponent matrix))| =
      normSq (determinant matrix) := by
  cases kind <;>
    simp [radialOwnerForm, negativeImagOwner,
      abs_of_nonneg (normSq_nonneg (determinant matrix))] <;>
    norm_num

/-- Every oriented sector side has radial pairing of exactly one decoder
determinant norm in absolute value.  Parser normalization and the loop
orientation can change the sign but not this magnitude. -/
theorem abs_gradientPairingConstant_radialOwner_sectorOwner
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) {sectorForm : HermitianForm}
    (member : sectorForm ∈ sectorOwnerForms sector
      (normalizedMatrix kind exponent matrix)) :
    |gradientPairingConstant (radialOwnerForm kind exponent matrix)
        sectorForm| = normSq (determinant matrix) := by
  cases sector with
  | east =>
      simp [sectorOwnerForms] at member
      subst sectorForm
      exact abs_gradientPairingConstant_radialOwner_positiveReal kind exponent
        matrix
  | northEast =>
      simp [sectorOwnerForms] at member
      rcases member with rfl | rfl
      · exact abs_gradientPairingConstant_radialOwner_positiveReal kind exponent
          matrix
      · exact abs_gradientPairingConstant_radialOwner_positiveImag kind exponent
          matrix
  | north =>
      simp [sectorOwnerForms] at member
      subst sectorForm
      exact abs_gradientPairingConstant_radialOwner_positiveImag kind exponent
        matrix
  | northWest =>
      simp [sectorOwnerForms] at member
      rcases member with rfl | rfl
      · exact abs_gradientPairingConstant_radialOwner_negativeReal kind exponent
          matrix
      · exact abs_gradientPairingConstant_radialOwner_positiveImag kind exponent
          matrix
  | west =>
      simp [sectorOwnerForms] at member
      subst sectorForm
      exact abs_gradientPairingConstant_radialOwner_negativeReal kind exponent
        matrix
  | southWest =>
      simp [sectorOwnerForms] at member
      rcases member with rfl | rfl
      · exact abs_gradientPairingConstant_radialOwner_negativeReal kind exponent
          matrix
      · exact abs_gradientPairingConstant_radialOwner_negativeImag kind exponent
          matrix
  | south =>
      simp [sectorOwnerForms] at member
      subst sectorForm
      exact abs_gradientPairingConstant_radialOwner_negativeImag kind exponent
        matrix
  | southEast =>
      simp [sectorOwnerForms] at member
      rcases member with rfl | rfl
      · exact abs_gradientPairingConstant_radialOwner_positiveReal kind exponent
          matrix
      · exact abs_gradientPairingConstant_radialOwner_negativeImag kind exponent
          matrix

/-- Exact determinant norm of the normalized sector homography. -/
theorem normSq_determinant_normalizedMatrix
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    normSq (determinant (normalizedMatrix kind exponent matrix)) =
      match kind with
      | .initialHigh | .loop =>
          ((2 : ℚ) ^ exponent)⁻¹ * normSq (determinant matrix)
      | .initialLow =>
          (2 : ℚ) ^ exponent * normSq (determinant matrix) := by
  cases kind with
  | initialHigh =>
      rw [normalizedMatrix, determinant_mul, normSq_mul]
      simp [normalizationMatrix, determinant, Mat2.scale,
        normSq_inv _ (RawParser.natPow_gamma_ne exponent),
        normSq_natPow, normSq_gamma]
  | initialLow =>
      rw [normalizedMatrix, determinant_mul, normSq_mul]
      simp [normalizationMatrix, determinant, Mat2.scale,
        normSq_natPow, normSq_gamma]
  | loop =>
      rw [normalizedMatrix, determinant_mul, normSq_mul]
      simp [normalizationMatrix, determinant, Mat2.scale,
        normSq_inv _ (RawParser.natPow_gamma_ne exponent),
        normSq_natPow, normSq_gamma]

/-- Every oriented sector owner has the normalized decoder's line
discriminant. -/
theorem boundaryDiscriminant_sectorOwner
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) {sectorForm : HermitianForm}
    (member : sectorForm ∈ sectorOwnerForms sector
      (normalizedMatrix kind exponent matrix)) :
    boundaryDiscriminant sectorForm =
      -normSq (determinant (normalizedMatrix kind exponent matrix)) := by
  cases sector <;> simp [sectorOwnerForms] at member
  all_goals rcases member with rfl | rfl <;>
    simp [positiveRealOwner, negativeRealOwner, positiveImagOwner,
      negativeImagOwner, boundaryDiscriminant_realComparisonForm,
      boundaryDiscriminant_imagComparisonForm]

/-- A nonorthogonal radial/sector pair is separated from the forbidden
opposite 45-degree cones by a strict rational angle gap. -/
theorem radialOwner_sectorOwner_angleGap_pos
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (determinantNonzero : determinant matrix ≠ 0)
    {sectorForm : HermitianForm}
    (member : sectorForm ∈ sectorOwnerForms sector
      (normalizedMatrix kind exponent matrix)) :
    0 < boundaryDiscriminant (radialOwnerForm kind exponent matrix) *
        boundaryDiscriminant sectorForm -
      2 * gradientPairingConstant (radialOwnerForm kind exponent matrix)
        sectorForm ^ 2 := by
  have sectorDiscriminant := boundaryDiscriminant_sectorOwner kind exponent
    sector matrix member
  have pairingMagnitude :=
    abs_gradientPairingConstant_radialOwner_sectorOwner kind exponent sector
      matrix member
  have determinantPositive : 0 < normSq (determinant matrix) :=
    normSq_pos determinantNonzero
  have pairingSquare :
      gradientPairingConstant (radialOwnerForm kind exponent matrix)
          sectorForm ^ 2 = normSq (determinant matrix) ^ 2 := by
    calc
      gradientPairingConstant (radialOwnerForm kind exponent matrix)
            sectorForm ^ 2 =
          |gradientPairingConstant (radialOwnerForm kind exponent matrix)
            sectorForm| ^ 2 := by rw [sq_abs]
      _ = normSq (determinant matrix) ^ 2 := by rw [pairingMagnitude]
  rw [sectorDiscriminant, pairingSquare,
    normSq_determinant_normalizedMatrix]
  cases kind with
  | initialHigh =>
      simp only [radialOwnerForm]
      rw [boundaryDiscriminant_normComparisonForm]
      have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
      field_simp
      nlinarith
  | initialLow =>
      simp only [radialOwnerForm]
      rw [boundaryDiscriminant_normComparisonForm]
      have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
      field_simp
      nlinarith
  | loop =>
      simp only [radialOwnerForm, boundaryDiscriminant_neg]
      rw [boundaryDiscriminant_normComparisonForm]
      have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
      rw [pow_succ]
      field_simp
      nlinarith

/-- Under a true radial bracket, the only possible active face is its one
weak annulus boundary, already oriented toward the accepted block. -/
theorem radialFormula_activeOwnerForms_eq_nil_or_singleton
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (value : HermitianForm → ℚ)
    (evaluation :
      formulaEvalWith (radialFormula kind exponent matrix) value = true) :
    activeOwnerForms (radialFormula kind exponent matrix) value = [] ∨
      activeOwnerForms (radialFormula kind exponent matrix) value =
        [radialOwnerForm kind exponent matrix] := by
  cases kind with
  | initialHigh =>
      have evaluated :
          0 ≤ value (normComparisonForm matrix ((2 : ℚ) ^ exponent)) ∧
            value (normComparisonForm matrix
              ((2 : ℚ) ^ (exponent + 1))) < 0 := by
        simpa [radialFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictNonzero :
          value (normComparisonForm matrix
            ((2 : ℚ) ^ (exponent + 1))) ≠ 0 := evaluated.2.ne
      by_cases weakZero :
          value (normComparisonForm matrix ((2 : ℚ) ^ exponent)) = 0
      · right
        simp [radialFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, radialOwnerForm, orientedWeakForm, weakZero,
          strictNonzero]
      · left
        simp [radialFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, weakZero, strictNonzero]
  | initialLow =>
      have evaluated :
          0 ≤ value (normComparisonForm matrix
              (((2 : ℚ) ^ exponent)⁻¹)) ∧
            value (normComparisonForm matrix
              (2 / (2 : ℚ) ^ exponent)) < 0 := by
        simpa [radialFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictNonzero :
          value (normComparisonForm matrix
            (2 / (2 : ℚ) ^ exponent)) ≠ 0 := evaluated.2.ne
      by_cases weakZero :
          value (normComparisonForm matrix
            (((2 : ℚ) ^ exponent)⁻¹)) = 0
      · right
        simp [radialFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, radialOwnerForm, orientedWeakForm, weakZero,
          strictNonzero]
      · left
        simp [radialFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, weakZero, strictNonzero]
  | loop =>
      have evaluated :
          0 < value (normComparisonForm matrix ((2 : ℚ) ^ exponent)) ∧
            value (normComparisonForm matrix
              ((2 : ℚ) ^ (exponent + 1))) ≤ 0 := by
        simpa [radialFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictNonzero :
          value (normComparisonForm matrix ((2 : ℚ) ^ exponent)) ≠ 0 :=
        evaluated.1.ne'
      by_cases weakZero :
          value (normComparisonForm matrix
            ((2 : ℚ) ^ (exponent + 1))) = 0
      · right
        simp [radialFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, radialOwnerForm, orientedWeakForm, weakZero,
          strictNonzero]
      · left
        simp [radialFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, weakZero, strictNonzero]

/-- Every active face selected from a true sector formula is one of that
row's explicitly oriented weak owner forms. -/
theorem sectorFormula_activeOwnerForms_mem_sectorOwnerForms
    (sector : Sector) (matrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (sectorFormula sector matrix) value = true)
    {form : HermitianForm}
    (member : form ∈ activeOwnerForms (sectorFormula sector matrix) value) :
    form ∈ sectorOwnerForms sector matrix := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  have source : atom ∈ formulaAtoms (sectorFormula sector matrix) :=
    satisfyingAtoms_mem_formulaAtoms _ _
      (activeSatisfyingAtoms_source atomMember)
  have weak := activeSatisfyingAtom_sign_weak evaluation
    (satisfyingAtoms_noZeroTest _ _
      (sectorFormula_noZeroTests sector matrix)) atomMember
  rcases atom with ⟨form, sign⟩
  cases sign <;> simp at weak
  · cases sector <;>
      simp [sectorFormula, formulaAtoms, sectorOwnerForms,
        positiveRealOwner, negativeRealOwner, positiveImagOwner,
        negativeImagOwner, orientedWeakForm] at source ⊢ <;>
      aesop
  · cases sector <;>
      simp [sectorFormula, formulaAtoms, sectorOwnerForms,
        positiveRealOwner, negativeRealOwner, positiveImagOwner,
        negativeImagOwner, orientedWeakForm] at source ⊢ <;>
      aesop

theorem activeOwnerForms_and
    (left right : Formula) (value : HermitianForm → ℚ) :
    activeOwnerForms (.and left right) value =
      activeOwnerForms left value ++ activeOwnerForms right value := by
  simp [activeOwnerForms, activeSatisfyingAtoms, satisfyingAtoms,
    List.filter_append, List.map_append]

/-- Every deterministic sector row has at most two active weak faces; the
axis rows have only one weak atom and the diagonal rows have exactly two
atoms total. -/
theorem sectorFormula_activeOwnerForms_length_le_two
    (sector : Sector) (matrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (sectorFormula sector matrix) value = true) :
    (activeOwnerForms (sectorFormula sector matrix) value).length ≤ 2 := by
  cases sector with
  | east =>
      have evaluated :
          0 ≤ value (realComparisonForm matrix ((2 : ℚ)⁻¹)) ∧
            0 < value (imagComparisonForm matrix (-1 / 2)) ∧
              value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower := evaluated.2.1.ne'
      have strictUpper := evaluated.2.2.ne
      by_cases weakZero :
          value (realComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, weakZero, strictLower, strictUpper]
  | northEast =>
      exact (activeOwnerForms_length_le_formulaAtoms
        (sectorFormula .northEast matrix) value).trans (by
          simp [sectorFormula, formulaAtoms])
  | north =>
      have evaluated :
          0 < value (realComparisonForm matrix (-1 / 2)) ∧
            value (realComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 ∧
              0 ≤ value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower := evaluated.1.ne'
      have strictUpper := evaluated.2.1.ne
      by_cases weakZero :
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, weakZero, strictLower, strictUpper]
  | northWest =>
      exact (activeOwnerForms_length_le_formulaAtoms
        (sectorFormula .northWest matrix) value).trans (by
          simp [sectorFormula, formulaAtoms])
  | west =>
      have evaluated :
          value (realComparisonForm matrix (-1 / 2)) ≤ 0 ∧
            0 < value (imagComparisonForm matrix (-1 / 2)) ∧
              value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower := evaluated.2.1.ne'
      have strictUpper := evaluated.2.2.ne
      by_cases weakZero :
          value (realComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, weakZero, strictLower, strictUpper]
  | southWest =>
      exact (activeOwnerForms_length_le_formulaAtoms
        (sectorFormula .southWest matrix) value).trans (by
          simp [sectorFormula, formulaAtoms])
  | south =>
      have evaluated :
          0 < value (realComparisonForm matrix (-1 / 2)) ∧
            value (realComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 ∧
              value (imagComparisonForm matrix (-1 / 2)) ≤ 0 := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower := evaluated.1.ne'
      have strictUpper := evaluated.2.1.ne
      by_cases weakZero :
          value (imagComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, weakZero, strictLower, strictUpper]
  | southEast =>
      exact (activeOwnerForms_length_le_formulaAtoms
        (sectorFormula .southEast matrix) value).trans (by
          simp [sectorFormula, formulaAtoms])

/-- A sector row with exactly two active faces is one of its real/imaginary
corners.  Their oriented gradient pairing is identically zero. -/
theorem sectorFormula_activeOwnerForms_pairingConstant_zero
    (sector : Sector) (matrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (sectorFormula sector matrix) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms (sectorFormula sector matrix) value =
      [left, right]) :
    gradientPairingConstant left right = 0 := by
  cases sector with
  | east =>
      have evaluated :
          0 ≤ value (realComparisonForm matrix ((2 : ℚ)⁻¹)) ∧
            0 < value (imagComparisonForm matrix (-1 / 2)) ∧
              value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower :
          value (imagComparisonForm matrix (-1 / 2)) ≠ 0 := by
        exact evaluated.2.1.ne'
      have strictUpper :
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) ≠ 0 := by
        exact evaluated.2.2.ne
      by_cases realZero :
          value (realComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, strictLower, strictUpper,
          realZero, orientedWeakForm] at forms
  | northEast =>
      by_cases realZero :
          value (realComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        by_cases imagZero :
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, realZero, imagZero,
          orientedWeakForm] at forms
      rw [← forms.1, ← forms.2]
      exact gradientPairingConstant_real_imag matrix ((2 : ℚ)⁻¹) ((2 : ℚ)⁻¹)
  | north =>
      have evaluated :
          0 < value (realComparisonForm matrix (-1 / 2)) ∧
            value (realComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 ∧
              0 ≤ value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower :
          value (realComparisonForm matrix (-1 / 2)) ≠ 0 := by
        exact evaluated.1.ne'
      have strictUpper :
          value (realComparisonForm matrix ((2 : ℚ)⁻¹)) ≠ 0 := by
        exact evaluated.2.1.ne
      by_cases imagZero :
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, strictLower, strictUpper,
          imagZero, orientedWeakForm] at forms
  | northWest =>
      by_cases realZero : value (realComparisonForm matrix (-1 / 2)) = 0 <;>
        by_cases imagZero :
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, realZero, imagZero,
          orientedWeakForm] at forms
      rw [← forms.1, ← forms.2]
      simpa using gradientPairingConstant_real_imag matrix (-1 / 2)
        ((2 : ℚ)⁻¹)
  | west =>
      have evaluated :
          value (realComparisonForm matrix (-1 / 2)) ≤ 0 ∧
            0 < value (imagComparisonForm matrix (-1 / 2)) ∧
              value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower :
          value (imagComparisonForm matrix (-1 / 2)) ≠ 0 := by
        exact evaluated.2.1.ne'
      have strictUpper :
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) ≠ 0 := by
        exact evaluated.2.2.ne
      by_cases realZero : value (realComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, strictLower, strictUpper,
          realZero, orientedWeakForm] at forms
  | southWest =>
      by_cases realZero : value (realComparisonForm matrix (-1 / 2)) = 0 <;>
        by_cases imagZero : value (imagComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, realZero, imagZero,
          orientedWeakForm] at forms
      rw [← forms.1, ← forms.2]
      simpa using gradientPairingConstant_real_imag matrix (-1 / 2) (-1 / 2)
  | south =>
      have evaluated :
          0 < value (realComparisonForm matrix (-1 / 2)) ∧
            value (realComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 ∧
              value (imagComparisonForm matrix (-1 / 2)) ≤ 0 := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower :
          value (realComparisonForm matrix (-1 / 2)) ≠ 0 := by
        exact evaluated.1.ne'
      have strictUpper :
          value (realComparisonForm matrix ((2 : ℚ)⁻¹)) ≠ 0 := by
        exact evaluated.2.1.ne
      by_cases imagZero : value (imagComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, strictLower, strictUpper,
          imagZero, orientedWeakForm] at forms
  | southEast =>
      by_cases realZero :
          value (realComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        by_cases imagZero : value (imagComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, realZero, imagZero,
          orientedWeakForm] at forms
      rw [← forms.1, ← forms.2]
      simpa using gradientPairingConstant_real_imag matrix ((2 : ℚ)⁻¹)
        (-1 / 2)

/-- Exact shape of a two-face sector row: only a diagonal sector can expose
two weak faces, and they are its displayed oriented real/imaginary corner. -/
theorem sectorFormula_activeOwnerForms_pair_exact
    (sector : Sector) (matrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (sectorFormula sector matrix) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms (sectorFormula sector matrix) value =
      [left, right]) :
    (sector = .northEast ∧ left = positiveRealOwner matrix ∧
        right = positiveImagOwner matrix) ∨
      (sector = .northWest ∧ left = negativeRealOwner matrix ∧
        right = positiveImagOwner matrix) ∨
      (sector = .southWest ∧ left = negativeRealOwner matrix ∧
        right = negativeImagOwner matrix) ∨
      (sector = .southEast ∧ left = positiveRealOwner matrix ∧
        right = negativeImagOwner matrix) := by
  cases sector with
  | east =>
      have evaluated :
          0 ≤ value (realComparisonForm matrix ((2 : ℚ)⁻¹)) ∧
            0 < value (imagComparisonForm matrix (-1 / 2)) ∧
              value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower := evaluated.2.1.ne'
      have strictUpper := evaluated.2.2.ne
      by_cases realZero :
          value (realComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, strictLower, strictUpper, realZero,
          orientedWeakForm] at forms
  | northEast =>
      by_cases realZero :
          value (realComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        by_cases imagZero :
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, realZero, imagZero, orientedWeakForm] at forms
      refine Or.inl ⟨rfl, ?_, ?_⟩
      · simpa [positiveRealOwner] using forms.1.symm
      · simpa [positiveImagOwner] using forms.2.symm
  | north =>
      have evaluated :
          0 < value (realComparisonForm matrix (-1 / 2)) ∧
            value (realComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 ∧
              0 ≤ value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower := evaluated.1.ne'
      have strictUpper := evaluated.2.1.ne
      by_cases imagZero :
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, strictLower, strictUpper, imagZero,
          orientedWeakForm] at forms
  | northWest =>
      by_cases realZero : value (realComparisonForm matrix (-1 / 2)) = 0 <;>
        by_cases imagZero :
          value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, realZero, imagZero, orientedWeakForm] at forms
      refine Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)
      · simpa [negativeRealOwner] using forms.1.symm
      · simpa [positiveImagOwner] using forms.2.symm
  | west =>
      have evaluated :
          value (realComparisonForm matrix (-1 / 2)) ≤ 0 ∧
            0 < value (imagComparisonForm matrix (-1 / 2)) ∧
              value (imagComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower := evaluated.2.1.ne'
      have strictUpper := evaluated.2.2.ne
      by_cases realZero : value (realComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, strictLower, strictUpper, realZero,
          orientedWeakForm] at forms
  | southWest =>
      by_cases realZero : value (realComparisonForm matrix (-1 / 2)) = 0 <;>
        by_cases imagZero : value (imagComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, realZero, imagZero, orientedWeakForm] at forms
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_⟩))
      · simpa [negativeRealOwner] using forms.1.symm
      · simpa [negativeImagOwner] using forms.2.symm
  | south =>
      have evaluated :
          0 < value (realComparisonForm matrix (-1 / 2)) ∧
            value (realComparisonForm matrix ((2 : ℚ)⁻¹)) < 0 ∧
              value (imagComparisonForm matrix (-1 / 2)) ≤ 0 := by
        simpa [sectorFormula, formulaEvalWith, SignTest.Holds] using evaluation
      have strictLower := evaluated.1.ne'
      have strictUpper := evaluated.2.1.ne
      by_cases imagZero : value (imagComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, strictLower, strictUpper, imagZero,
          orientedWeakForm] at forms
  | southEast =>
      by_cases realZero :
          value (realComparisonForm matrix ((2 : ℚ)⁻¹)) = 0 <;>
        by_cases imagZero : value (imagComparisonForm matrix (-1 / 2)) = 0 <;>
        simp [sectorFormula, activeOwnerForms, activeSatisfyingAtoms,
          satisfyingAtoms, realZero, imagZero, orientedWeakForm] at forms
      refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_, ?_⟩))
      · simpa [positiveRealOwner] using forms.1.symm
      · simpa [negativeImagOwner] using forms.2.symm

/-- If a completed radial-and-sector predicate has exactly two active faces,
they are either the orthogonal sector corner or its radial face followed by
one oriented sector side. -/
theorem radialSectorFormula_activeOwnerForms_pair_shape
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (sectorFormula sector (normalizedMatrix kind exponent matrix)))
      value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (sectorFormula sector (normalizedMatrix kind exponent matrix)))
      value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      |gradientPairingConstant left right| = normSq (determinant matrix) := by
  have evaluated := evaluation
  simp only [formulaEvalWith, Bool.and_eq_true] at evaluated
  have radialEvaluation :
      formulaEvalWith (radialFormula kind exponent matrix) value = true :=
    evaluated.1
  have sectorEvaluation :
      formulaEvalWith
        (sectorFormula sector (normalizedMatrix kind exponent matrix)) value =
          true := evaluated.2
  rw [activeOwnerForms_and] at forms
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      matrix value radialEvaluation with radialNil | radialSingleton
  · left
    rw [radialNil, List.nil_append] at forms
    exact sectorFormula_activeOwnerForms_pairingConstant_zero sector
      (normalizedMatrix kind exponent matrix) value sectorEvaluation forms
  · right
    rw [radialSingleton] at forms
    cases sectorForms : activeOwnerForms
        (sectorFormula sector (normalizedMatrix kind exponent matrix)) value with
    | nil => simp [sectorForms] at forms
    | cons sectorForm tail =>
        cases tail with
        | nil =>
            rw [sectorForms] at forms
            change [radialOwnerForm kind exponent matrix, sectorForm] =
              [left, right] at forms
            simp only [List.cons.injEq] at forms
            rw [← forms.1, ← forms.2.1]
            apply abs_gradientPairingConstant_radialOwner_sectorOwner kind
              exponent sector matrix
            apply sectorFormula_activeOwnerForms_mem_sectorOwnerForms sector
              (normalizedMatrix kind exponent matrix) value sectorEvaluation
            simp [sectorForms]
        | cons next rest =>
            have lengths := congrArg List.length forms
            simp [sectorForms] at lengths

/-- The stronger two-face classification needed by the finite compass table:
the sector corner is orthogonal, while a radial/sector corner has a strict
45-degree angle gap. -/
theorem radialSectorFormula_activeOwnerForms_pair_angleGap
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (determinantNonzero : determinant matrix ≠ 0)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (sectorFormula sector (normalizedMatrix kind exponent matrix)))
      value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (sectorFormula sector (normalizedMatrix kind exponent matrix)))
      value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2 := by
  have evaluated := evaluation
  simp only [formulaEvalWith, Bool.and_eq_true] at evaluated
  rw [activeOwnerForms_and] at forms
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      matrix value evaluated.1 with radialNil | radialSingleton
  · left
    rw [radialNil, List.nil_append] at forms
    exact sectorFormula_activeOwnerForms_pairingConstant_zero sector
      (normalizedMatrix kind exponent matrix) value evaluated.2 forms
  · right
    rw [radialSingleton] at forms
    cases sectorForms : activeOwnerForms
        (sectorFormula sector (normalizedMatrix kind exponent matrix)) value with
    | nil => simp [sectorForms] at forms
    | cons sectorForm tail =>
        cases tail with
        | nil =>
            rw [sectorForms] at forms
            change [radialOwnerForm kind exponent matrix, sectorForm] =
              [left, right] at forms
            simp only [List.cons.injEq] at forms
            rw [← forms.1, ← forms.2.1]
            apply radialOwner_sectorOwner_angleGap_pos kind exponent sector
              matrix determinantNonzero
            apply sectorFormula_activeOwnerForms_mem_sectorOwnerForms sector
              (normalizedMatrix kind exponent matrix) value evaluated.2
            simp [sectorForms]
        | cons next rest =>
            have lengths := congrArg List.length forms
            simp [sectorForms] at lengths

/-- A true completed radial-and-sector core has at most one radial face and
at most two sector faces. -/
theorem radialSectorFormula_activeOwnerForms_length_le_three
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (sectorFormula sector (normalizedMatrix kind exponent matrix)))
      value = true) :
    (activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (sectorFormula sector (normalizedMatrix kind exponent matrix)))
      value).length ≤ 3 := by
  have evaluated := evaluation
  simp only [formulaEvalWith, Bool.and_eq_true] at evaluated
  have sectorLength := sectorFormula_activeOwnerForms_length_le_two sector
    (normalizedMatrix kind exponent matrix) value evaluated.2
  rw [activeOwnerForms_and]
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      matrix value evaluated.1 with radialNil | radialSingleton
  · rw [radialNil, List.nil_append]
    exact sectorLength.trans (by norm_num)
  · rw [radialSingleton, List.length_append, List.length_singleton]
    omega

/-- A true strict-positive atom cannot be an active equality owner. -/
theorem positiveAtom_activeOwnerForms_eq_nil
    (form : HermitianForm) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith (.atom ⟨form, .positive⟩) value = true) :
    activeOwnerForms (.atom ⟨form, .positive⟩) value = [] := by
  have positive : 0 < value form := by
    simpa [formulaEvalWith, SignTest.Holds] using evaluation
  simp [activeOwnerForms, activeSatisfyingAtoms, satisfyingAtoms, positive.ne']

/-- The strict residual test in a completed block contributes no active
owner, so every two-face cone has the radial/sector shape already classified
above. -/
theorem completedSectorFormula_activeOwnerForms_pair_shape
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (residual : HermitianForm)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      |gradientPairingConstant left right| = normSq (determinant matrix) := by
  have evaluated := evaluation
  simp only [formulaEvalWith, Bool.and_eq_true] at evaluated
  have residualNil := positiveAtom_activeOwnerForms_eq_nil residual value
    evaluated.2.2
  have coreEvaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (sectorFormula sector (normalizedMatrix kind exponent matrix))) value =
        true := by
    simp only [formulaEvalWith, Bool.and_eq_true]
    exact ⟨evaluated.1, evaluated.2.1⟩
  rw [activeOwnerForms_and, activeOwnerForms_and, residualNil,
    List.append_nil] at forms
  apply radialSectorFormula_activeOwnerForms_pair_shape kind exponent sector
    matrix value coreEvaluation
  rw [activeOwnerForms_and]
  exact forms

/-- Angle-gap version of the completed-block reduction. -/
theorem completedSectorFormula_activeOwnerForms_pair_angleGap
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (determinantNonzero : determinant matrix ≠ 0)
    (residual : HermitianForm) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2 := by
  have evaluated := evaluation
  simp only [formulaEvalWith, Bool.and_eq_true] at evaluated
  have residualNil := positiveAtom_activeOwnerForms_eq_nil residual value
    evaluated.2.2
  have coreEvaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (sectorFormula sector (normalizedMatrix kind exponent matrix))) value =
        true := by
    simp only [formulaEvalWith, Bool.and_eq_true]
    exact ⟨evaluated.1, evaluated.2.1⟩
  rw [activeOwnerForms_and, activeOwnerForms_and, residualNil,
    List.append_nil] at forms
  apply radialSectorFormula_activeOwnerForms_pair_angleGap kind exponent sector
    matrix determinantNonzero value coreEvaluation
  rw [activeOwnerForms_and]
  exact forms

/-- The strict residual contributes no equality face, so the full completed
block also has at most three active owners. -/
theorem completedSectorFormula_activeOwnerForms_length_le_three
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (residual : HermitianForm)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) value = true) :
    (activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) value).length ≤ 3 := by
  have evaluated := evaluation
  simp only [formulaEvalWith, Bool.and_eq_true] at evaluated
  have residualNil := positiveAtom_activeOwnerForms_eq_nil residual value
    evaluated.2.2
  have coreEvaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (sectorFormula sector (normalizedMatrix kind exponent matrix))) value =
        true := by
    simp only [formulaEvalWith, Bool.and_eq_true]
    exact ⟨evaluated.1, evaluated.2.1⟩
  rw [activeOwnerForms_and, activeOwnerForms_and, residualNil,
    List.append_nil]
  simpa only [activeOwnerForms_and] using
    radialSectorFormula_activeOwnerForms_length_le_three kind exponent sector
      matrix value coreEvaluation

/-- If the three-face bound is attained, the list is exactly the radial owner
followed by the two oriented coordinate faces of one diagonal sector. -/
theorem completedSectorFormula_activeOwnerForms_triple_exact
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (residual : HermitianForm)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) value = true)
    {first second third : HermitianForm}
    (forms : activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) value =
      [first, second, third]) :
    first = radialOwnerForm kind exponent matrix ∧
      ((sector = .northEast ∧
          second = positiveRealOwner
            (normalizedMatrix kind exponent matrix) ∧
          third = positiveImagOwner
            (normalizedMatrix kind exponent matrix)) ∨
        (sector = .northWest ∧
          second = negativeRealOwner
            (normalizedMatrix kind exponent matrix) ∧
          third = positiveImagOwner
            (normalizedMatrix kind exponent matrix)) ∨
        (sector = .southWest ∧
          second = negativeRealOwner
            (normalizedMatrix kind exponent matrix) ∧
          third = negativeImagOwner
            (normalizedMatrix kind exponent matrix)) ∨
        (sector = .southEast ∧
          second = positiveRealOwner
            (normalizedMatrix kind exponent matrix) ∧
          third = negativeImagOwner
            (normalizedMatrix kind exponent matrix))) := by
  have evaluated := evaluation
  simp only [formulaEvalWith, Bool.and_eq_true] at evaluated
  have residualNil := positiveAtom_activeOwnerForms_eq_nil residual value
    evaluated.2.2
  rw [activeOwnerForms_and, activeOwnerForms_and, residualNil,
    List.append_nil] at forms
  rcases radialFormula_activeOwnerForms_eq_nil_or_singleton kind exponent
      matrix value evaluated.1 with radialNil | radialSingleton
  · rw [radialNil, List.nil_append] at forms
    have sectorLength := sectorFormula_activeOwnerForms_length_le_two sector
      (normalizedMatrix kind exponent matrix) value evaluated.2.1
    rw [forms] at sectorLength
    norm_num at sectorLength
  · rw [radialSingleton, List.singleton_append, List.cons.injEq] at forms
    refine ⟨forms.1.symm, ?_⟩
    exact sectorFormula_activeOwnerForms_pair_exact sector
      (normalizedMatrix kind exponent matrix) value evaluated.2.1 forms.2

/-- Specialization to the exact local formula produced by a completed parser
block. -/
theorem completedSectorAdvance_activeOwnerForms_pair_shape
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (advanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit)
      value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (advanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit)
      value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      |gradientPairingConstant left right| = 1 := by
  simpa [advanceFormula, RawParser.identityMatrix, determinant] using
    completedSectorFormula_activeOwnerForms_pair_shape kind exponent
      (RawParser.sectorOfBits first second bit) RawParser.identityMatrix
      (residualForm kind exponent (RawParser.sectorOfBits first second bit))
      value evaluation forms

/-- Homographic pullback preserves the completed-block dichotomy, with the
nonzero pairing magnitude scaled by the determinant norm of the pullback. -/
theorem pullbackCompletedSectorFormula_activeOwnerForms_pair_shape
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix pullbackMatrix : Mat2 QI) (residual : HermitianForm)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (.and (radialFormula kind exponent matrix)
          (.and
            (sectorFormula sector (normalizedMatrix kind exponent matrix))
            (.atom ⟨residual, .positive⟩)))) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (Formula.pullback pullbackMatrix
        (.and (radialFormula kind exponent matrix)
          (.and
            (sectorFormula sector (normalizedMatrix kind exponent matrix))
            (.atom ⟨residual, .positive⟩)))) value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      |gradientPairingConstant left right| =
        normSq (determinant pullbackMatrix) * normSq (determinant matrix) := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue = true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback] at forms
  change (activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue).map
      (pullbackForm pullbackMatrix) = [left, right] at forms
  cases localForms : activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue with
  | nil => simp [localForms] at forms
  | cons localLeft tail =>
      cases tail with
      | nil => simp [localForms] at forms
      | cons localRight rest =>
          cases rest with
          | nil =>
              simp only [localForms, List.map_cons, List.map_nil,
                List.cons.injEq] at forms
              have localShape :=
                completedSectorFormula_activeOwnerForms_pair_shape kind
                  exponent sector matrix residual localValue localEvaluation
                  localForms
              rw [← forms.1, ← forms.2.1,
                gradientPairingConstant_pullbackForm]
              rcases localShape with localZero | localMagnitude
              · left
                rw [localZero]
                exact mul_zero _
              · right
                rw [abs_mul,
                  abs_of_nonneg (normSq_nonneg (determinant pullbackMatrix)),
                  localMagnitude]
          | cons third rest => simp [localForms] at forms

/-- Pullback preserves the strict angle gap because both discriminants and
the gradient pairing acquire the same positive determinant-norm factor. -/
theorem pullbackCompletedSectorFormula_activeOwnerForms_pair_angleGap
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix pullbackMatrix : Mat2 QI)
    (matrixDeterminantNonzero : determinant matrix ≠ 0)
    (pullbackDeterminantNonzero : determinant pullbackMatrix ≠ 0)
    (residual : HermitianForm) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (.and (radialFormula kind exponent matrix)
          (.and
            (sectorFormula sector (normalizedMatrix kind exponent matrix))
            (.atom ⟨residual, .positive⟩)))) value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (Formula.pullback pullbackMatrix
        (.and (radialFormula kind exponent matrix)
          (.and
            (sectorFormula sector (normalizedMatrix kind exponent matrix))
            (.atom ⟨residual, .positive⟩)))) value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2 := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue = true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback] at forms
  change (activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue).map
      (pullbackForm pullbackMatrix) = [left, right] at forms
  cases localForms : activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue with
  | nil => simp [localForms] at forms
  | cons localLeft tail =>
      cases tail with
      | nil => simp [localForms] at forms
      | cons localRight rest =>
          cases rest with
          | nil =>
              simp only [localForms, List.map_cons, List.map_nil,
                List.cons.injEq] at forms
              have localShape :=
                completedSectorFormula_activeOwnerForms_pair_angleGap kind
                  exponent sector matrix matrixDeterminantNonzero residual
                  localValue localEvaluation localForms
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
                  _ =
                      (factor * boundaryDiscriminant localLeft) *
                          (factor * boundaryDiscriminant localRight) -
                        2 * (factor *
                          gradientPairingConstant localLeft localRight) ^ 2 := by
                    ring
          | cons third rest => simp [localForms] at forms

/-- Pullback preserves the three-face structural bound exactly because it
maps the finite active-owner list without changing its length. -/
theorem pullbackCompletedSectorFormula_activeOwnerForms_length_le_three
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix pullbackMatrix : Mat2 QI) (residual : HermitianForm)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (.and (radialFormula kind exponent matrix)
          (.and
            (sectorFormula sector (normalizedMatrix kind exponent matrix))
            (.atom ⟨residual, .positive⟩)))) value = true) :
    (activeOwnerForms
      (Formula.pullback pullbackMatrix
        (.and (radialFormula kind exponent matrix)
          (.and
            (sectorFormula sector (normalizedMatrix kind exponent matrix))
            (.atom ⟨residual, .positive⟩)))) value).length ≤ 3 := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue = true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback, List.length_map]
  exact completedSectorFormula_activeOwnerForms_length_le_three kind exponent
    sector matrix residual localValue localEvaluation

/-- Exact three-face shape after an arbitrary homographic pullback. -/
theorem pullbackCompletedSectorFormula_activeOwnerForms_triple_exact
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix pullbackMatrix : Mat2 QI) (residual : HermitianForm)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix
        (.and (radialFormula kind exponent matrix)
          (.and
            (sectorFormula sector (normalizedMatrix kind exponent matrix))
            (.atom ⟨residual, .positive⟩)))) value = true)
    {first second third : HermitianForm}
    (forms : activeOwnerForms
      (Formula.pullback pullbackMatrix
        (.and (radialFormula kind exponent matrix)
          (.and
            (sectorFormula sector (normalizedMatrix kind exponent matrix))
            (.atom ⟨residual, .positive⟩)))) value =
      [first, second, third]) :
    first = pullbackForm pullbackMatrix
        (radialOwnerForm kind exponent matrix) ∧
      ((sector = .northEast ∧
          second = pullbackForm pullbackMatrix
            (positiveRealOwner (normalizedMatrix kind exponent matrix)) ∧
          third = pullbackForm pullbackMatrix
            (positiveImagOwner (normalizedMatrix kind exponent matrix))) ∨
        (sector = .northWest ∧
          second = pullbackForm pullbackMatrix
            (negativeRealOwner (normalizedMatrix kind exponent matrix)) ∧
          third = pullbackForm pullbackMatrix
            (positiveImagOwner (normalizedMatrix kind exponent matrix))) ∨
        (sector = .southWest ∧
          second = pullbackForm pullbackMatrix
            (negativeRealOwner (normalizedMatrix kind exponent matrix)) ∧
          third = pullbackForm pullbackMatrix
            (negativeImagOwner (normalizedMatrix kind exponent matrix))) ∨
        (sector = .southEast ∧
          second = pullbackForm pullbackMatrix
            (positiveRealOwner (normalizedMatrix kind exponent matrix)) ∧
          third = pullbackForm pullbackMatrix
            (negativeImagOwner (normalizedMatrix kind exponent matrix)))) := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation : formulaEvalWith
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue = true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback] at forms
  change (activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue).map
      (pullbackForm pullbackMatrix) = [first, second, third] at forms
  cases localForms : activeOwnerForms
      (.and (radialFormula kind exponent matrix)
        (.and (sectorFormula sector (normalizedMatrix kind exponent matrix))
          (.atom ⟨residual, .positive⟩))) localValue with
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
                  have localShape :=
                    completedSectorFormula_activeOwnerForms_triple_exact kind
                      exponent sector matrix residual localValue localEvaluation
                      localForms
                  rcases localShape with ⟨rfl, corner⟩
                  refine ⟨forms.1.symm, ?_⟩
                  rcases corner with northEast | northWest | southWest | southEast
                  · rcases northEast with ⟨rfl, rfl, rfl⟩
                    exact Or.inl
                      ⟨rfl, forms.2.1.symm, forms.2.2.1.symm⟩
                  · rcases northWest with ⟨rfl, rfl, rfl⟩
                    exact Or.inr (Or.inl
                      ⟨rfl, forms.2.1.symm, forms.2.2.1.symm⟩)
                  · rcases southWest with ⟨rfl, rfl, rfl⟩
                    exact Or.inr (Or.inr (Or.inl
                      ⟨rfl, forms.2.1.symm, forms.2.2.1.symm⟩))
                  · rcases southEast with ⟨rfl, rfl, rfl⟩
                    exact Or.inr (Or.inr (Or.inr
                      ⟨rfl, forms.2.1.symm, forms.2.2.1.symm⟩))
              | cons fourth remaining => simp [localForms] at forms

/-- Completed-block specialization in the original input coordinate. -/
theorem completedSectorInputAdvance_activeOwnerForms_pair_shape
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (inputAdvanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit)
      value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (inputAdvanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit)
      value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      |gradientPairingConstant left right| = normSq (determinant matrix) := by
  have pulled :=
    pullbackCompletedSectorFormula_activeOwnerForms_pair_shape kind exponent
      (RawParser.sectorOfBits first second bit) RawParser.identityMatrix
      (adjugate matrix)
      (residualForm kind exponent (RawParser.sectorOfBits first second bit))
      value (by
        simpa [inputAdvanceFormula, advanceFormula] using evaluation) (by
        simpa [inputAdvanceFormula, advanceFormula] using forms)
  rw [determinant_adjugate] at pulled
  simpa [RawParser.identityMatrix, determinant] using pulled

/-- Angle-gap specialization for a completed parser block in the original
input coordinate. -/
theorem completedSectorInputAdvance_activeOwnerForms_pair_angleGap
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (matrix : Mat2 QI) (matrixDeterminantNonzero : determinant matrix ≠ 0)
    (history : List RawParser.Constraint) (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (inputAdvanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit)
      value = true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (inputAdvanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit)
      value = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2 := by
  apply pullbackCompletedSectorFormula_activeOwnerForms_pair_angleGap kind
    exponent (RawParser.sectorOfBits first second bit)
    RawParser.identityMatrix (adjugate matrix)
  · norm_num [RawParser.identityMatrix, determinant]
  · rw [determinant_adjugate]
    exact matrixDeterminantNonzero
  · simpa [inputAdvanceFormula, advanceFormula] using evaluation
  · simpa [inputAdvanceFormula, advanceFormula] using forms

/-- Completed-block three-face bound in the original input coordinate. -/
theorem completedSectorInputAdvance_activeOwnerForms_length_le_three
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (inputAdvanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit)
      value = true) :
    (activeOwnerForms
      (inputAdvanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit)
      value).length ≤ 3 := by
  apply pullbackCompletedSectorFormula_activeOwnerForms_length_le_three kind
    exponent (RawParser.sectorOfBits first second bit)
    RawParser.identityMatrix (adjugate matrix)
    (residualForm kind exponent (RawParser.sectorOfBits first second bit))
  simpa [inputAdvanceFormula, advanceFormula] using evaluation

/-- Exact completed-block three-face shape in the original input coordinate. -/
theorem completedSectorInputAdvance_activeOwnerForms_triple_exact
    (kind : RawParser.BlockKind) (exponent : ℕ) (firstBit secondBit bit : Bool)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (inputAdvanceFormula
        ⟨.sector kind exponent (.two firstBit secondBit), matrix, history⟩ bit)
      value = true)
    {first second third : HermitianForm}
    (forms : activeOwnerForms
      (inputAdvanceFormula
        ⟨.sector kind exponent (.two firstBit secondBit), matrix, history⟩ bit)
      value = [first, second, third]) :
    first = radialOwnerForm kind exponent (adjugate matrix) ∧
      ((RawParser.sectorOfBits firstBit secondBit bit = .northEast ∧
          second = positiveRealOwner
            (normalizedMatrix kind exponent (adjugate matrix)) ∧
          third = positiveImagOwner
            (normalizedMatrix kind exponent (adjugate matrix))) ∨
        (RawParser.sectorOfBits firstBit secondBit bit = .northWest ∧
          second = negativeRealOwner
            (normalizedMatrix kind exponent (adjugate matrix)) ∧
          third = positiveImagOwner
            (normalizedMatrix kind exponent (adjugate matrix))) ∨
        (RawParser.sectorOfBits firstBit secondBit bit = .southWest ∧
          second = negativeRealOwner
            (normalizedMatrix kind exponent (adjugate matrix)) ∧
          third = negativeImagOwner
            (normalizedMatrix kind exponent (adjugate matrix))) ∨
        (RawParser.sectorOfBits firstBit secondBit bit = .southEast ∧
          second = positiveRealOwner
            (normalizedMatrix kind exponent (adjugate matrix)) ∧
          third = negativeImagOwner
            (normalizedMatrix kind exponent (adjugate matrix)))) := by
  have pulled :=
    pullbackCompletedSectorFormula_activeOwnerForms_triple_exact kind exponent
      (RawParser.sectorOfBits firstBit secondBit bit)
      RawParser.identityMatrix (adjugate matrix)
      (residualForm kind exponent
        (RawParser.sectorOfBits firstBit secondBit bit))
      value (by
        simpa [inputAdvanceFormula, advanceFormula] using evaluation) (by
        simpa [inputAdvanceFormula, advanceFormula] using forms)
  simpa only [pullbackForm_radialOwnerForm, pullbackForm_positiveRealOwner,
    pullbackForm_negativeRealOwner, pullbackForm_positiveImagOwner,
    pullbackForm_negativeImagOwner, identityMatrix_mul,
    normalizedMatrix_identity_mul] using pulled

/-- The same two-face sector compatibility holds after any homographic
formula pullback into the original root coordinate. -/
theorem pullbackSectorFormula_activeOwnerForms_pairingConstant_zero
    (sector : Sector) (matrix pullbackMatrix : Mat2 QI)
    (value : HermitianForm → ℚ)
    (evaluation : formulaEvalWith
      (Formula.pullback pullbackMatrix (sectorFormula sector matrix)) value =
        true)
    {left right : HermitianForm}
    (forms : activeOwnerForms
      (Formula.pullback pullbackMatrix (sectorFormula sector matrix)) value =
        [left, right]) :
    gradientPairingConstant left right = 0 := by
  let localValue : HermitianForm → ℚ := fun form =>
    value (pullbackForm pullbackMatrix form)
  have localEvaluation :
      formulaEvalWith (sectorFormula sector matrix) localValue = true := by
    rw [← formulaEvalWith_pullback]
    exact evaluation
  rw [activeOwnerForms_pullback] at forms
  change (activeOwnerForms (sectorFormula sector matrix) localValue).map
      (pullbackForm pullbackMatrix) = [left, right] at forms
  cases localForms : activeOwnerForms (sectorFormula sector matrix) localValue with
  | nil => simp [localForms] at forms
  | cons localLeft tail =>
      cases tail with
      | nil => simp [localForms] at forms
      | cons localRight rest =>
          cases rest with
          | nil =>
              simp only [localForms, List.map_cons, List.map_nil,
                List.cons.injEq] at forms
              rw [← forms.1, ← forms.2.1,
                gradientPairingConstant_pullbackForm]
              rw [sectorFormula_activeOwnerForms_pairingConstant_zero sector
                matrix localValue localEvaluation localForms]
              exact mul_zero _
          | cons third rest => simp [localForms] at forms

end CCLCompleteOwnerCompatibility
end FTA
