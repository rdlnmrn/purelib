import FTA.CCLBoundaryPath
import FTA.CCLFormulaPullback

/-!
# Concrete curve plans for CCL branch comparisons

The finite curve controller must retain more than an erased Hermitian form:
it needs the standard circle or line from which that form arose.  This module
records that provenance and turns it into the exact polynomial projective path
consumed by the Sturm machinery.  In particular, `BoundarySource.onBoundary`
constructs the boundary proof from a decoder determinant and the path's
denominator certificate; callers no longer have to postulate that connection.
-/

namespace FTA
namespace CCLBranchPlan

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLBoundaryPath
open FTA.CCLFormulaPullback
open FTA.ProjectivePath
open FTA.PathPolynomial

abbrev QI := CCL.GaussianRat

/-- Provenance for the three kinds of nondegenerate branch boundary used by
the raw CCL parser.  A norm boundary stores an exact Gaussian-rational scale,
so its squared radius is rational without a square-root choice. -/
inductive BoundarySource where
  | norm (matrix : Mat2 QI) (scaleValue : QI)
  | real (matrix : Mat2 QI) (threshold : ℚ)
  | imag (matrix : Mat2 QI) (threshold : ℚ)
deriving DecidableEq, Repr

namespace BoundarySource

def matrix : BoundarySource → Mat2 QI
  | .norm value _ | .real value _ | .imag value _ => value

/-- The standard parametrization genuinely varies.  Only a norm circle needs
an explicit premise: its Gaussian scale must be nonzero. -/
def ParametrizationNondegenerate : BoundarySource → Prop
  | .norm _ scaleValue => scaleValue ≠ 0
  | .real .. | .imag .. => True

instance (source : BoundarySource) : Decidable source.ParametrizationNondegenerate := by
  cases source <;> simp [ParametrizationNondegenerate] <;> infer_instance

/-- The exact Hermitian comparison represented by the source. -/
def form : BoundarySource → HermitianForm
  | .norm matrix scaleValue =>
      normComparisonForm matrix (normSq scaleValue)
  | .real matrix threshold => realComparisonForm matrix threshold
  | .imag matrix threshold => imagComparisonForm matrix threshold

/-- Standard polynomial path before applying the inverse decoder. -/
def standardPath : BoundarySource → Path
  | .norm _ scaleValue => scaledCirclePath scaleValue
  | .real _ threshold => linePath ⟨threshold, 0⟩ ⟨0, 1⟩
  | .imag _ threshold => linePath ⟨0, threshold⟩ ⟨1, 0⟩

/-- Original-coordinate inverse image of the standard circle or line. -/
def path (source : BoundarySource) : Path :=
  actPath (adjugate source.matrix) source.standardPath

@[simp] theorem path_norm (matrix : Mat2 QI) (scaleValue : QI) :
    (BoundarySource.norm matrix scaleValue).path =
      inverseScaledCirclePath matrix scaleValue := rfl

@[simp] theorem path_real (matrix : Mat2 QI) (threshold : ℚ) :
    (BoundarySource.real matrix threshold).path =
      inverseRealBoundaryPath matrix threshold := rfl

@[simp] theorem path_imag (matrix : Mat2 QI) (threshold : ℚ) :
    (BoundarySource.imag matrix threshold).path =
      inverseImagBoundaryPath matrix threshold := rfl

theorem standardPath_denominator_ne (source : BoundarySource) (t : ℚ) :
    source.standardPath.denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
  cases source with
  | norm matrix scaleValue => exact unitCirclePath_denominator_ne t
  | real matrix threshold => exact linePath_denominator_ne _ _ t
  | imag matrix threshold => exact linePath_denominator_ne _ _ t

/-- The polynomial inverse path is the affine adjugate homography wherever
its standard projective denominator is nonzero (which is automatic here). -/
theorem path_value (source : BoundarySource) (t : ℚ) :
    source.path.value t =
      RatBox.homographic (adjugate source.matrix)
        (source.standardPath.value t) := by
  exact CCLBoundaryPath.actPath_value
    (adjugate source.matrix) source.standardPath t
    (source.standardPath_denominator_ne t)

/-- A nonzero polynomial denominator on the inverse path supplies the affine
adjugate denominator needed by the inverse-homography theorem. -/
theorem inverseDenominator_ne
    (source : BoundarySource) (t : ℚ)
    (pathDenominator :
      source.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (adjugate source.matrix).c * source.standardPath.value t +
        (adjugate source.matrix).d ≠ 0 := by
  exact CCLBoundaryPath.homographic_denominator_ne_of_actPath
    (adjugate source.matrix) source.standardPath t
    (source.standardPath_denominator_ne t) pathDenominator

/-- Decoding an inverse-path point recovers its standard circle/line point. -/
theorem decoded_path_value
    (source : BoundarySource) (t : ℚ)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (pathDenominator :
      source.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    RatBox.homographic source.matrix (source.path.value t) =
      source.standardPath.value t := by
  rw [source.path_value]
  exact homographic_adjugate_inverse source.matrix
    (source.standardPath.value t) determinantNonzero
    (source.inverseDenominator_ne t pathDenominator)

theorem forwardDenominator_ne
    (source : BoundarySource) (t : ℚ)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (pathDenominator :
      source.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    source.matrix.c * source.path.value t + source.matrix.d ≠ 0 := by
  rw [source.path_value]
  exact denominator_inverse_tail_ne source.matrix
    (source.standardPath.value t) determinantNonzero
    (source.inverseDenominator_ne t pathDenominator)

/-- Every generated inverse path lies on its displayed comparison boundary.
The only cell-specific premise is the nonzero path denominator already carried
by the intersection sampler's denominator certificate. -/
theorem onBoundary
    (source : BoundarySource) (t : ℚ)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (pathDenominator :
      source.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    source.form.eval (source.path.value t) = 0 := by
  have decoded := source.decoded_path_value t determinantNonzero pathDenominator
  have forwardDenominator :=
    source.forwardDenominator_ne t determinantNonzero pathDenominator
  cases source with
  | norm matrix scaleValue =>
      have decoded' :
          RatBox.homographic matrix
              ((BoundarySource.norm matrix scaleValue).path.value t) =
            (scaledCirclePath scaleValue).value t := by
        simpa [BoundarySource.matrix, standardPath] using decoded
      apply (norm_homographic_eq_iff matrix _ (normSq scaleValue)
        forwardDenominator).1
      rw [decoded', scaledCirclePath_value, normSq_mul,
        normSq_unitCircleParam, _root_.mul_one]
  | real matrix threshold =>
      have decoded' :
          RatBox.homographic matrix
              ((BoundarySource.real matrix threshold).path.value t) =
            (linePath ⟨threshold, 0⟩ ⟨0, 1⟩).value t := by
        simpa [BoundarySource.matrix, standardPath] using decoded
      apply (real_homographic_eq_iff matrix _ threshold
        forwardDenominator).1
      rw [decoded', linePath_value]
      simp [CCLGeometry.ofRat]
  | imag matrix threshold =>
      have decoded' :
          RatBox.homographic matrix
              ((BoundarySource.imag matrix threshold).path.value t) =
            (linePath ⟨0, threshold⟩ ⟨1, 0⟩).value t := by
        simpa [BoundarySource.matrix, standardPath] using decoded
      apply (imag_homographic_eq_iff matrix _ threshold
        forwardDenominator).1
      rw [decoded', linePath_value]
      simp [CCLGeometry.ofRat]

/-! ## Finite affine charts -/

/-- Circle sources use the primary and reciprocal charts; line sources use
the primary affine chart (their projective point at infinity is the excluded
decoder pole). -/
def paths : BoundarySource → List Path
  | .norm matrix scaleValue =>
      [inverseScaledCirclePath matrix scaleValue,
        inverseReciprocalScaledCirclePath matrix scaleValue]
  | .real matrix threshold => [inverseRealBoundaryPath matrix threshold]
  | .imag matrix threshold => [inverseImagBoundaryPath matrix threshold]

theorem paths_ne_nil (source : BoundarySource) : source.paths ≠ [] := by
  cases source <;> simp [paths]

theorem paths_length_le_two (source : BoundarySource) :
    source.paths.length ≤ 2 := by
  cases source <;> simp [paths]

private theorem reciprocalNorm_onBoundary
    (matrix : Mat2 QI) (scaleValue : QI) (t : ℚ)
    (determinantNonzero : determinant matrix ≠ 0)
    (pathDenominator :
      (inverseReciprocalScaledCirclePath matrix scaleValue).denominator.eval
        (PathPolynomial.ofRat t) ≠ 0) :
    (normComparisonForm matrix (normSq scaleValue)).eval
        ((inverseReciprocalScaledCirclePath matrix scaleValue).value t) = 0 := by
  let standard := reciprocalScaledCirclePath scaleValue
  have standardDenominator :
      standard.denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
    exact reciprocalUnitCirclePath_denominator_ne t
  have inverseDenominator :
      (adjugate matrix).c * standard.value t +
        (adjugate matrix).d ≠ 0 := by
    exact CCLBoundaryPath.homographic_denominator_ne_of_actPath
      (adjugate matrix) standard t standardDenominator pathDenominator
  have pathValue :
      (inverseReciprocalScaledCirclePath matrix scaleValue).value t =
        RatBox.homographic (adjugate matrix) (standard.value t) := by
    exact CCLBoundaryPath.actPath_value
      (adjugate matrix) standard t standardDenominator
  have decoded :
      RatBox.homographic matrix
          ((inverseReciprocalScaledCirclePath matrix scaleValue).value t) =
        standard.value t := by
    rw [pathValue]
    exact homographic_adjugate_inverse matrix (standard.value t)
      determinantNonzero inverseDenominator
  have forwardDenominator :
      matrix.c *
          (inverseReciprocalScaledCirclePath matrix scaleValue).value t +
        matrix.d ≠ 0 := by
    rw [pathValue]
    exact denominator_inverse_tail_ne matrix (standard.value t)
      determinantNonzero inverseDenominator
  apply (norm_homographic_eq_iff matrix _ (normSq scaleValue)
    forwardDenominator).1
  rw [decoded, reciprocalScaledCirclePath_value, normSq_mul,
    normSq_reciprocalUnitCircleParam, _root_.mul_one]

/-- Every path in the finite chart list lies on the same displayed boundary. -/
theorem path_mem_onBoundary
    (source : BoundarySource) {path : Path} (member : path ∈ source.paths)
    (t : ℚ) (determinantNonzero : determinant source.matrix ≠ 0)
    (pathDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    source.form.eval (path.value t) = 0 := by
  cases source with
  | norm matrix scaleValue =>
      simp [paths] at member
      rcases member with rfl | rfl
      · exact (BoundarySource.norm matrix scaleValue).onBoundary t
          determinantNonzero pathDenominator
      · exact reciprocalNorm_onBoundary matrix scaleValue t
          determinantNonzero pathDenominator
  | real matrix threshold =>
      simp [paths] at member
      subst path
      exact (BoundarySource.real matrix threshold).onBoundary t
        determinantNonzero pathDenominator
  | imag matrix threshold =>
      simp [paths] at member
      subst path
      exact (BoundarySource.imag matrix threshold).onBoundary t
        determinantNonzero pathDenominator

/-! ## Provenance-preserving homographic pullback -/

/-- Pull a concrete standard boundary through one more homography while
retaining its circle/line constructor. -/
def pullback (source : BoundarySource) (inner : Mat2 QI) : BoundarySource :=
  match source with
  | .norm outer scaleValue => .norm (Mat2.mul outer inner) scaleValue
  | .real outer threshold => .real (Mat2.mul outer inner) threshold
  | .imag outer threshold => .imag (Mat2.mul outer inner) threshold

theorem pullback_parametrizationNondegenerate
    (source : BoundarySource) (inner : Mat2 QI)
    (nondegenerate : source.ParametrizationNondegenerate) :
    (source.pullback inner).ParametrizationNondegenerate := by
  cases source <;> exact nondegenerate

@[simp] theorem pullback_matrix (source : BoundarySource) (inner : Mat2 QI) :
    (source.pullback inner).matrix = Mat2.mul source.matrix inner := by
  cases source <;> rfl

/-- Formula pullback and geometric-source pullback agree exactly, not merely
up to a nonzero scalar. -/
theorem form_pullback (source : BoundarySource) (inner : Mat2 QI) :
    (source.pullback inner).form = pullbackForm inner source.form := by
  cases source with
  | norm outer scaleValue =>
      exact (pullbackForm_normComparison outer inner
        (normSq scaleValue)).symm
  | real outer threshold =>
      exact (pullbackForm_realComparison outer inner threshold).symm
  | imag outer threshold =>
      exact (pullbackForm_imagComparison outer inner threshold).symm

/-- The path generated after pullback is the inverse image under the composed
matrix recorded by the pulled-back Hermitian atom. -/
theorem pullback_path (source : BoundarySource) (inner : Mat2 QI) :
    (source.pullback inner).path =
      actPath (adjugate (Mat2.mul source.matrix inner)) source.standardPath := by
  cases source <;> rfl

end BoundarySource

/-! ## Finite parser-phase boundary plans -/

/-- Exact Gaussian-rational scale for the circle of squared radius `2^n`. -/
def highScale (exponent : ℕ) : QI := natPow gamma exponent

/-- Exact Gaussian-rational scale for the circle of squared radius
`1 / 2^n`. -/
def lowScale (exponent : ℕ) : QI := inv (natPow gamma exponent)

theorem highScale_ne (exponent : ℕ) : highScale exponent ≠ 0 :=
  RawParser.natPow_gamma_ne exponent

theorem lowScale_ne (exponent : ℕ) : lowScale exponent ≠ 0 :=
  inv_ne_zero (RawParser.natPow_gamma_ne exponent)

private theorem gamma_ne : gamma ≠ 0 := by
  intro zero
  have normZero := congrArg normSq zero
  rw [normSq_zero, normSq_gamma] at normZero
  norm_num at normZero

@[simp] theorem normSq_highScale (exponent : ℕ) :
    normSq (highScale exponent) = (2 : ℚ) ^ exponent := by
  rw [highScale, normSq_natPow, normSq_gamma]

@[simp] theorem normSq_lowScale (exponent : ℕ) :
    normSq (lowScale exponent) = 1 / (2 : ℚ) ^ exponent := by
  rw [lowScale, normSq_inv _ (RawParser.natPow_gamma_ne exponent),
    normSq_natPow, normSq_gamma]

theorem normComparisonForm_identity (radiusSq : ℚ) :
    normComparisonForm RawParser.identityMatrix radiusSq =
      CCLParserGeometry.affineNormComparisonForm radiusSq := by
  apply HermitianForm.ext <;>
    simp [normComparisonForm, RawParser.identityMatrix,
      CCLParserGeometry.affineNormComparisonForm,
      CCLParserGeometry.constantForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, normSq]

private def identityNorm (scaleValue : QI) : BoundarySource :=
  .norm RawParser.identityMatrix scaleValue

private def normalizedReal
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (threshold : ℚ) : BoundarySource :=
  .real (CCLParserGeometry.normalizedMatrix kind exponent
    RawParser.identityMatrix) threshold

private def normalizedImag
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (threshold : ℚ) : BoundarySource :=
  .imag (CCLParserGeometry.normalizedMatrix kind exponent
    RawParser.identityMatrix) threshold

/-- The finite list of genuinely new comparison boundaries introduced by the
next bit in each parser phase.  Historical constraints are deliberately not
repeated: they restrict the relevant parameter cells but do not create a new
branch choice.

For sector fragments the plan retains every coordinate wall that can separate
the remaining table rows.  Equality ownership is attached only after the
parameter-cell sign data has restricted a wall to one relevant arc; at sector
corners a full projective line does not have one globally valid owner. -/
def localPlan : RawParser.Phase → List BoundarySource
  | .initial => [identityNorm gamma]
  | .highUnary count => [identityNorm (highScale (count + 1))]
  | .lowUnary 0 => [identityNorm 1]
  | .lowUnary (count + 1) => [identityNorm (lowScale (count + 1))]
  | .loopUnary count => [identityNorm (highScale (count + 1))]
  | .sector kind exponent .zero =>
      [normalizedReal kind exponent (-1 / 2),
        normalizedImag kind exponent (1 / 2),
        normalizedImag kind exponent (-1 / 2)]
  | .sector kind exponent (.one first) =>
      let threshold : ℚ := if first then -1 / 2 else 1 / 2
      let finalRealThreshold : ℚ := if first then 1 / 2 else -1 / 2
      [normalizedReal kind exponent threshold,
        normalizedImag kind exponent threshold,
        normalizedReal kind exponent finalRealThreshold]
  | .sector kind exponent (.two false false) =>
      [normalizedImag kind exponent (1 / 2)]
  | .sector kind exponent (.two false true) =>
      [normalizedReal kind exponent (-1 / 2)]
  | .sector kind exponent (.two true false) =>
      [normalizedImag kind exponent (-1 / 2)]
  | .sector kind exponent (.two true true) =>
      [normalizedReal kind exponent (1 / 2)]

/-- Hermitian forms of the new comparison curves, before the current decoder
is pulled back to the original root coordinate. -/
def localForms (phase : RawParser.Phase) : List HermitianForm :=
  (localPlan phase).map BoundarySource.form

/-- Forms occurring syntactically in a finite parser formula. -/
def formulaForms : CCLParserGeometry.Formula → List HermitianForm
  | .truth | .falsity => []
  | .atom atom => [atom.form]
  | .and left right | .or left right =>
      formulaForms left ++ formulaForms right

theorem form_mem_formulaForms_any
    {form : HermitianForm} {formula : CCLParserGeometry.Formula}
    {formulas : List CCLParserGeometry.Formula}
    (formulaMember : formula ∈ formulas)
    (formMember : form ∈ formulaForms formula) :
    form ∈ formulaForms (CCLParserGeometry.Formula.any formulas) := by
  induction formulas with
  | nil => simp at formulaMember
  | cons head tail inductionHypothesis =>
      simp only [CCLParserGeometry.Formula.any, List.foldr_cons, formulaForms,
        List.mem_append]
      rcases List.mem_cons.mp formulaMember with rfl | tailMember
      · exact Or.inl formMember
      · exact Or.inr (inductionHypothesis tailMember)

theorem form_mem_stateFormula_of_active
    (state : RawParser.State) {form : HermitianForm}
    (member : form ∈ formulaForms
      (CCLParserGeometry.activeFormula state.phase)) :
    form ∈ formulaForms (CCLParserGeometry.stateFormula state) := by
  exact List.mem_append_right _ member

theorem formulaForms_pullback
    (matrix : Mat2 QI) (formula : CCLParserGeometry.Formula) :
    formulaForms (CCLFormulaPullback.Formula.pullback matrix formula) =
      (formulaForms formula).map (pullbackForm matrix) := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | atom atom => rfl
  | and left right leftInduction rightInduction =>
      simp only [CCLFormulaPullback.Formula.pullback, formulaForms,
        leftInduction, rightInduction, List.map_append]
  | or left right leftInduction rightInduction =>
      simp only [CCLFormulaPullback.Formula.pullback, formulaForms,
        leftInduction, rightInduction, List.map_append]

@[simp] theorem localForms_initial :
    localForms .initial =
      [CCLParserGeometry.affineNormComparisonForm 2] := by
  simp [localForms, localPlan, identityNorm, BoundarySource.form,
    normComparisonForm_identity, normSq_gamma]

@[simp] theorem localForms_highUnary (count : ℕ) :
    localForms (.highUnary count) =
      [CCLParserGeometry.affineNormComparisonForm ((2 : ℚ) ^ (count + 1))] := by
  simp [localForms, localPlan, identityNorm, BoundarySource.form,
    normComparisonForm_identity]

@[simp] theorem localForms_lowUnary_zero :
    localForms (.lowUnary 0) =
      [CCLParserGeometry.affineNormComparisonForm 1] := by
  simp [localForms, localPlan, identityNorm, BoundarySource.form,
    normComparisonForm_identity]

@[simp] theorem localForms_lowUnary_succ (count : ℕ) :
    localForms (.lowUnary (count + 1)) =
      [CCLParserGeometry.affineNormComparisonForm
        (1 / (2 : ℚ) ^ (count + 1))] := by
  simp [localForms, localPlan, identityNorm, BoundarySource.form,
    normComparisonForm_identity]

@[simp] theorem localForms_loopUnary (count : ℕ) :
    localForms (.loopUnary count) =
      [CCLParserGeometry.affineNormComparisonForm ((2 : ℚ) ^ (count + 1))] := by
  simp [localForms, localPlan, identityNorm, BoundarySource.form,
    normComparisonForm_identity]

@[simp] theorem localForms_sector_zero
    (kind : RawParser.BlockKind) (exponent : ℕ) :
    localForms (.sector kind exponent .zero) =
      [realComparisonForm
          (CCLParserGeometry.normalizedMatrix kind exponent
            RawParser.identityMatrix) (-1 / 2),
        imagComparisonForm
          (CCLParserGeometry.normalizedMatrix kind exponent
            RawParser.identityMatrix) (1 / 2),
        imagComparisonForm
          (CCLParserGeometry.normalizedMatrix kind exponent
            RawParser.identityMatrix) (-1 / 2)] := by
  rfl

@[simp] theorem localForms_sector_one
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool) :
    localForms (.sector kind exponent (.one first)) =
      let threshold : ℚ := if first then -1 / 2 else 1 / 2
      [realComparisonForm
          (CCLParserGeometry.normalizedMatrix kind exponent
            RawParser.identityMatrix) threshold,
        imagComparisonForm
          (CCLParserGeometry.normalizedMatrix kind exponent
            RawParser.identityMatrix) threshold,
        realComparisonForm
          (CCLParserGeometry.normalizedMatrix kind exponent
            RawParser.identityMatrix)
          (if first then 1 / 2 else -1 / 2)] := by
  cases first <;> rfl

@[simp] theorem localForms_sector_two
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second : Bool) :
    localForms (.sector kind exponent (.two first second)) =
      match first, second with
      | false, false =>
          [imagComparisonForm
            (CCLParserGeometry.normalizedMatrix kind exponent
              RawParser.identityMatrix) (1 / 2)]
      | false, true =>
          [realComparisonForm
            (CCLParserGeometry.normalizedMatrix kind exponent
              RawParser.identityMatrix) (-1 / 2)]
      | true, false =>
          [imagComparisonForm
            (CCLParserGeometry.normalizedMatrix kind exponent
              RawParser.identityMatrix) (-1 / 2)]
      | true, true =>
          [realComparisonForm
            (CCLParserGeometry.normalizedMatrix kind exponent
              RawParser.identityMatrix) (1 / 2)] := by
  cases first <;> cases second <;> rfl

theorem localPlan_ne_nil (phase : RawParser.Phase) :
    localPlan phase ≠ [] := by
  cases phase with
  | initial => simp [localPlan]
  | highUnary count => simp [localPlan]
  | lowUnary count => cases count <;> simp [localPlan]
  | loopUnary count => simp [localPlan]
  | sector kind exponent bits =>
      cases bits with
      | zero => simp [localPlan]
      | one first => cases first <;> simp [localPlan]
      | two first second => cases first <;> cases second <;> simp [localPlan]

theorem localPlan_length_le_three (phase : RawParser.Phase) :
    (localPlan phase).length ≤ 3 := by
  cases phase with
  | initial => simp [localPlan]
  | highUnary count => simp [localPlan]
  | lowUnary count => cases count <;> simp [localPlan]
  | loopUnary count => simp [localPlan]
  | sector kind exponent bits =>
      cases bits with
      | zero => simp [localPlan]
      | one first => cases first <;> simp [localPlan]
      | two first second => cases first <;> cases second <;> simp [localPlan]

theorem localPlan_parametrizationNondegenerate
    (phase : RawParser.Phase) {source : BoundarySource}
    (member : source ∈ localPlan phase) :
    source.ParametrizationNondegenerate := by
  cases phase with
  | initial =>
      simp [localPlan] at member
      subst source
      simpa [identityNorm, BoundarySource.ParametrizationNondegenerate] using gamma_ne
  | highUnary count =>
      simp [localPlan] at member
      subst source
      simpa [identityNorm, BoundarySource.ParametrizationNondegenerate] using
        highScale_ne (count + 1)
  | lowUnary count =>
      cases count with
      | zero =>
          simp [localPlan] at member
          subst source
          simp [identityNorm, BoundarySource.ParametrizationNondegenerate]
      | succ count =>
          simp [localPlan] at member
          subst source
          simpa [identityNorm, BoundarySource.ParametrizationNondegenerate] using
            lowScale_ne (count + 1)
  | loopUnary count =>
      simp [localPlan] at member
      subst source
      simpa [identityNorm, BoundarySource.ParametrizationNondegenerate] using
        highScale_ne (count + 1)
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp [localPlan] at member
          rcases member with rfl | rfl | rfl <;>
            trivial
      | one first =>
          cases first <;>
            simp [localPlan] at member <;>
            rcases member with rfl | rfl | rfl <;>
            trivial
      | two first second =>
          cases first <;> cases second <;>
            simp [localPlan] at member <;>
            subst source <;>
            trivial

/-- Before the current decoder is pulled back, every planned comparison is
affine and therefore has lower row `(0,1)`. -/
theorem localPlan_lowerRow
    (phase : RawParser.Phase) {source : BoundarySource}
    (member : source ∈ localPlan phase) :
    source.matrix.c = 0 ∧ source.matrix.d = 1 := by
  cases phase with
  | initial =>
      simp [localPlan] at member
      subst source
      simp [identityNorm, BoundarySource.matrix, RawParser.identityMatrix]
  | highUnary count =>
      simp [localPlan] at member
      subst source
      simp [identityNorm, BoundarySource.matrix, RawParser.identityMatrix]
  | lowUnary count =>
      cases count with
      | zero =>
          simp [localPlan] at member
          subst source
          simp [identityNorm, BoundarySource.matrix, RawParser.identityMatrix]
      | succ count =>
          simp [localPlan] at member
          subst source
          simp [identityNorm, BoundarySource.matrix, RawParser.identityMatrix]
  | loopUnary count =>
      simp [localPlan] at member
      subst source
      simp [identityNorm, BoundarySource.matrix, RawParser.identityMatrix]
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp [localPlan] at member
          rcases member with rfl | rfl | rfl <;>
            simpa [normalizedReal, normalizedImag, BoundarySource.matrix,
              RawParser.identityMatrix] using
              CCLParserGeometry.normalizedMatrix_lowerRow kind exponent
                RawParser.identityMatrix
      | one first =>
          cases first <;>
            simp [localPlan] at member <;>
            rcases member with rfl | rfl | rfl <;>
            simpa [normalizedReal, normalizedImag, BoundarySource.matrix,
              RawParser.identityMatrix] using
              CCLParserGeometry.normalizedMatrix_lowerRow kind exponent
                RawParser.identityMatrix
      | two first second =>
          cases first <;> cases second <;>
            simp [localPlan] at member <;>
            subst source <;>
            simpa [normalizedReal, normalizedImag, BoundarySource.matrix,
              RawParser.identityMatrix] using
              CCLParserGeometry.normalizedMatrix_lowerRow kind exponent
                RawParser.identityMatrix

/-- Concrete boundary plan in the original polynomial coordinate. -/
def inputPlan (state : RawParser.State) : List BoundarySource :=
  (localPlan state.phase).map fun source =>
    source.pullback (adjugate state.matrix)

/-- When one raw bit enters a completed-sector phase, its remaining third-bit
boundary is already present in the preceding one-bit sector plan.  The extra
lookahead real wall is what makes this true in the two diagonal cases; the
decoder matrix itself is unchanged until the following bit completes the
block. -/
theorem inputPlan_step_subset_of_completed
    (state : RawParser.State) (bit : Bool)
    (completed : ∃ kind exponent first second,
      (RawParser.step state bit).phase =
        .sector kind exponent (.two first second)) :
    ∀ source ∈ inputPlan (RawParser.step state bit),
      source ∈ inputPlan state := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;> simp [RawParser.step] at completed
  | highUnary count =>
      cases bit <;> simp [RawParser.step] at completed
  | lowUnary count =>
      cases bit <;> simp [RawParser.step] at completed
  | loopUnary count =>
      cases bit <;> simp [RawParser.step] at completed
  | sector kind exponent bits =>
      cases bits with
      | zero => simp [RawParser.step] at completed
      | one first =>
          intro source member
          cases first <;> cases bit <;>
            simp [RawParser.step, inputPlan, localPlan] at member ⊢ <;>
            subst source <;> simp
      | two first second =>
          simp [RawParser.step, RawParser.completeSector] at completed

/-- Exact forms of the original-coordinate plan. -/
def inputForms (state : RawParser.State) : List HermitianForm :=
  (inputPlan state).map BoundarySource.form

theorem inputForms_eq_map_pullback (state : RawParser.State) :
    inputForms state =
      (localForms state.phase).map
        (pullbackForm (adjugate state.matrix)) := by
  simp only [inputForms, inputPlan, localForms, List.map_map]
  apply List.map_congr_left
  intro source member
  exact source.form_pullback (adjugate state.matrix)

/-- The comparison forms actually read by the current local discriminator.
The complete branch plan has one deliberate extra lookahead wall in each
one-bit sector phase, so that the following owner grid already contains the
remaining third-bit boundary.  That wall does not decide the present second
bit and is therefore omitted here. -/
def localDecisionForms : RawParser.Phase → List HermitianForm
  | .sector kind exponent (.one false) =>
      [realComparisonForm
        (CCLParserGeometry.normalizedMatrix kind exponent
          RawParser.identityMatrix) (1 / 2)]
  | .sector kind exponent (.one true) =>
      [realComparisonForm
        (CCLParserGeometry.normalizedMatrix kind exponent
          RawParser.identityMatrix) (-1 / 2)]
  | phase => localForms phase

/-- Current-bit decision forms in the original polynomial coordinate. -/
def inputDecisionForms (state : RawParser.State) : List HermitianForm :=
  (localDecisionForms state.phase).map
    (pullbackForm (adjugate state.matrix))

theorem localDecisionForms_subset_localForms
    (phase : RawParser.Phase) :
    localDecisionForms phase ⊆ localForms phase := by
  cases phase with
  | initial => simp [localDecisionForms]
  | highUnary count => simp [localDecisionForms]
  | lowUnary count => cases count <;> simp [localDecisionForms]
  | loopUnary count => simp [localDecisionForms]
  | sector kind exponent bits =>
      cases bits with
      | zero => simp [localDecisionForms]
      | one first => cases first <;> simp [localDecisionForms, localForms,
          localPlan, normalizedReal, normalizedImag, BoundarySource.form]
      | two first second =>
          cases first <;> cases second <;> simp [localDecisionForms]

@[simp] theorem inputPlan_length (state : RawParser.State) :
    (inputPlan state).length = (localPlan state.phase).length := by
  simp [inputPlan]

/-- Although the initial sector decision now needs three line boundaries,
the complete parser plan still expands to at most four bounded charts: norm
sources have two charts and coordinate sources have one. -/
theorem inputPlan_paths_length_sum_le_four (state : RawParser.State) :
    ((inputPlan state).map fun source => source.paths.length).sum ≤ 4 := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simp [inputPlan, localPlan, identityNorm, BoundarySource.pullback,
        BoundarySource.paths]
  | highUnary count =>
      simp [inputPlan, localPlan, identityNorm, BoundarySource.pullback,
        BoundarySource.paths]
  | lowUnary count =>
      cases count <;>
        simp [inputPlan, localPlan, identityNorm, BoundarySource.pullback,
          BoundarySource.paths]
  | loopUnary count =>
      simp [inputPlan, localPlan, identityNorm, BoundarySource.pullback,
        BoundarySource.paths]
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp [inputPlan, localPlan, normalizedReal, normalizedImag,
            BoundarySource.pullback, BoundarySource.paths]
      | one first =>
          cases first <;>
            simp [inputPlan, localPlan, normalizedReal, normalizedImag,
              BoundarySource.pullback, BoundarySource.paths]
      | two first second =>
          cases first <;> cases second <;>
            simp [inputPlan, localPlan, normalizedReal, normalizedImag,
              BoundarySource.pullback, BoundarySource.paths]

theorem inputPlan_ne_nil (state : RawParser.State) :
    inputPlan state ≠ [] := by
  simp [inputPlan, localPlan_ne_nil state.phase]

/-- Every member of the input plan is an exact provenance-preserving
pullback of one local parser boundary. -/
theorem mem_inputPlan_iff
    (state : RawParser.State) (source : BoundarySource) :
    source ∈ inputPlan state ↔
      ∃ candidate ∈ localPlan state.phase,
        source = candidate.pullback (adjugate state.matrix) := by
  rw [inputPlan, List.mem_map]
  constructor
  · rintro ⟨candidate, member, rfl⟩
    exact ⟨candidate, member, rfl⟩
  · rintro ⟨candidate, member, equality⟩
    exact ⟨candidate, member, equality.symm⟩

theorem inputPlan_parametrizationNondegenerate
    (state : RawParser.State) {source : BoundarySource}
    (member : source ∈ inputPlan state) :
    source.ParametrizationNondegenerate := by
  rcases (mem_inputPlan_iff state source).1 member with
    ⟨candidate, candidateMember, rfl⟩
  exact candidate.pullback_parametrizationNondegenerate (adjugate state.matrix)
    (localPlan_parametrizationNondegenerate state.phase candidateMember)

/-- All original-coordinate planned curves use exactly the inverse decoder's
already-separated affine denominator. -/
theorem inputPlan_lowerRow
    (state : RawParser.State) {source : BoundarySource}
    (member : source ∈ inputPlan state) :
    source.matrix.c = (adjugate state.matrix).c ∧
      source.matrix.d = (adjugate state.matrix).d := by
  rcases (mem_inputPlan_iff state source).1 member with
    ⟨candidate, candidateMember, rfl⟩
  have lowerRow := localPlan_lowerRow state.phase candidateMember
  simp only [BoundarySource.pullback_matrix, Mat2.mul]
  rw [lowerRow.1, lowerRow.2]
  simp

/-! ## Invertibility of every planned curve -/

theorem determinant_mul (left right : Mat2 QI) :
    determinant (Mat2.mul left right) =
      determinant left * determinant right := by
  simpa only [determinant, Mat2.det] using RawParser.det_mul left right

@[simp] theorem determinant_adjugate (matrix : Mat2 QI) :
    determinant (adjugate matrix) = determinant matrix := by
  apply GaussianRat.ext <;>
    simp only [determinant, adjugate, mul_re, mul_im, sub_re, sub_im,
      neg_re, neg_im] <;>
    ring

theorem normalizedMatrix_determinant_ne
    (kind : RawParser.BlockKind) (exponent : ℕ) :
    determinant (CCLParserGeometry.normalizedMatrix kind exponent
      RawParser.identityMatrix) ≠ 0 := by
  cases kind with
  | initialHigh =>
      simpa [determinant, CCLParserGeometry.normalizedMatrix,
        CCLParserGeometry.normalizationMatrix, Mat2.mul, Mat2.scale,
        RawParser.identityMatrix] using
          inv_ne_zero (RawParser.natPow_gamma_ne exponent)
  | initialLow =>
      simpa [determinant, CCLParserGeometry.normalizedMatrix,
        CCLParserGeometry.normalizationMatrix, Mat2.mul, Mat2.scale,
        RawParser.identityMatrix] using
          RawParser.natPow_gamma_ne exponent
  | loop =>
      simpa [determinant, CCLParserGeometry.normalizedMatrix,
        CCLParserGeometry.normalizationMatrix, Mat2.mul, Mat2.scale,
        RawParser.identityMatrix] using
          inv_ne_zero (RawParser.natPow_gamma_ne exponent)

theorem localPlan_determinant_ne
    (phase : RawParser.Phase) {source : BoundarySource}
    (member : source ∈ localPlan phase) :
    determinant source.matrix ≠ 0 := by
  cases phase with
  | initial =>
      simp only [localPlan, List.mem_singleton] at member
      subst source
      norm_num [identityNorm, BoundarySource.matrix, determinant,
        RawParser.identityMatrix]
  | highUnary count =>
      simp only [localPlan, List.mem_singleton] at member
      subst source
      norm_num [identityNorm, BoundarySource.matrix, determinant,
        RawParser.identityMatrix]
  | lowUnary count =>
      cases count with
      | zero =>
          simp only [localPlan, List.mem_singleton] at member
          subst source
          norm_num [identityNorm, BoundarySource.matrix, determinant,
            RawParser.identityMatrix]
      | succ count =>
          simp only [localPlan, List.mem_singleton] at member
          subst source
          norm_num [identityNorm, BoundarySource.matrix, determinant,
            RawParser.identityMatrix]
  | loopUnary count =>
      simp only [localPlan, List.mem_singleton] at member
      subst source
      norm_num [identityNorm, BoundarySource.matrix, determinant,
        RawParser.identityMatrix]
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp [localPlan] at member
          rcases member with rfl | rfl | rfl <;>
            exact normalizedMatrix_determinant_ne kind exponent
      | one first =>
          cases first <;>
            simp [localPlan] at member <;>
            rcases member with rfl | rfl | rfl <;>
            exact normalizedMatrix_determinant_ne kind exponent
      | two first second =>
          cases first <;> cases second <;>
            simp only [localPlan, List.mem_singleton] at member <;>
            subst source <;>
            exact normalizedMatrix_determinant_ne kind exponent

theorem inputPlan_determinant_ne
    (state : RawParser.State) {source : BoundarySource}
    (member : source ∈ inputPlan state)
    (stateDeterminant : determinant state.matrix ≠ 0) :
    determinant source.matrix ≠ 0 := by
  rcases (mem_inputPlan_iff state source).1 member with
    ⟨candidate, candidateMember, rfl⟩
  rw [BoundarySource.pullback_matrix, determinant_mul,
    determinant_adjugate]
  exact mul_ne_zero
    (localPlan_determinant_ne state.phase candidateMember)
    stateDeterminant

end CCLBranchPlan
end FTA
