import FTA.CCLNextBitFormula
import FTA.CCLOwnerDirection

/-!
# Pulling finite CCL formulas back to the original root coordinate

Raw-parser semantics is naturally stated at the current affine tail, whereas
the winding-one boxes in Theorem 10.2 live in the original polynomial
coordinate.  This module clears one decoder denominator and precomposes every
Hermitian atom with a homography.  Because the cleared factor is a positive
squared norm, all six strict/weak sign conventions, including equality, are
preserved exactly.
-/

namespace FTA
namespace CCLFormulaPullback

open CCL CCL.GaussianRat
open CCL.RawParserSemantics
open FTA.CCLGeometry
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLNextBitFormula

abbrev QI := CCL.GaussianRat

/-- Clear the denominator after substituting `H_M(z)` into one Hermitian
form. -/
def pullbackForm (M : Mat2 QI) (form : HermitianForm) : HermitianForm :=
  HermitianForm.add
    (HermitianForm.scale form.radial (affineNormForm M.a M.b))
    (HermitianForm.add
      (HermitianForm.scale form.realLinear
        (realCrossForm M.a M.b M.c M.d))
      (HermitianForm.add
        (HermitianForm.scale form.imagLinear
          (imagCrossForm M.a M.b M.c M.d))
        (HermitianForm.scale form.constant
          (affineNormForm M.c M.d))))

/-- A homographic pullback scales the Hermitian boundary discriminant by the
squared norm of the matrix determinant. -/
theorem boundaryDiscriminant_pullbackForm
    (M : Mat2 QI) (form : HermitianForm) :
    boundaryDiscriminant (pullbackForm M form) =
      normSq (determinant M) * boundaryDiscriminant form := by
  simp only [boundaryDiscriminant, pullbackForm, HermitianForm.add,
    HermitianForm.scale, affineNormForm, realCrossForm, imagCrossForm,
    determinant, normSq, mul_re, mul_im, sub_re, sub_im]
  ring

@[simp] theorem pullbackForm_neg (M : Mat2 QI) (form : HermitianForm) :
    pullbackForm M form.neg = (pullbackForm M form).neg := by
  apply HermitianForm.ext <;>
    simp [pullbackForm, HermitianForm.neg, HermitianForm.add,
      HermitianForm.scale] <;> ring

/-- Pulling back a squared affine norm composes its affine numerator with the
homography's homogeneous numerator and denominator. -/
theorem pullbackForm_affineNorm (M : Mat2 QI) (u v : QI) :
    pullbackForm M (affineNormForm u v) =
      affineNormForm (u * M.a + v * M.c) (u * M.b + v * M.d) := by
  apply HermitianForm.ext <;>
    simp [pullbackForm, HermitianForm.add, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, normSq, mul_re, mul_im,
      add_re, add_im] <;>
    ring

/-- If an invertible affine substitution carries a nonconstant affine
numerator to zero at one point, its transformed linear coefficient is still
nonzero.  This is the elementary cancellation needed to convert a small
pulled-back terminal residual into a small distance from its unique affine
zero. -/
theorem pullbackAffineCoefficient_ne_of_root
    (M : Mat2 QI) (u v point : QI)
    (determinantNonzero : determinant M ≠ 0) (uNonzero : u ≠ 0)
    (root : (u * M.a + v * M.c) * point +
      (u * M.b + v * M.d) = 0) :
    u * M.a + v * M.c ≠ 0 := by
  intro coefficientZero
  have constantZero : u * M.b + v * M.d = 0 := by
    rw [coefficientZero, zero_mul, zero_add] at root
    exact root
  have productZero : u * determinant M = 0 := by
    calc
      u * determinant M =
          (u * M.a + v * M.c) * M.d -
            (u * M.b + v * M.d) * M.c := by
        apply GaussianRat.ext <;>
          simp only [determinant, mul_re, mul_im, add_re, add_im, sub_re,
            sub_im] <;>
          ring
      _ = 0 := by rw [coefficientZero, constantZero]; simp
  rcases mul_eq_zero.mp productZero with left | right
  · exact uNonzero left
  · exact determinantNonzero right

/-- An invertible affine substitution cannot annihilate both coefficients of
a nonconstant affine numerator. -/
theorem pullbackAffinePair_ne
    (M : Mat2 QI) (u v : QI)
    (determinantNonzero : determinant M ≠ 0) (uNonzero : u ≠ 0) :
    u * M.a + v * M.c ≠ 0 ∨ u * M.b + v * M.d ≠ 0 := by
  by_contra neither
  simp only [not_or, not_not] at neither
  have productZero : u * determinant M = 0 := by
    calc
      u * determinant M =
          (u * M.a + v * M.c) * M.d -
            (u * M.b + v * M.d) * M.c := by
        apply GaussianRat.ext <;>
          simp only [determinant, mul_re, mul_im, add_re, add_im, sub_re,
            sub_im] <;>
          ring
      _ = 0 := by rw [neither.1, neither.2]; simp
  rcases mul_eq_zero.mp productZero with left | right
  · exact uNonzero left
  · exact determinantNonzero right

/-- A squared affine numerator is its nonzero leading norm times squared
distance from its unique affine zero. -/
theorem eval_affineNorm_eq_normSq_mul_distance_of_root
    (u v root point : QI) (rootZero : u * root + v = 0) :
    (affineNormForm u v).eval point =
      normSq u * normSq (point - root) := by
  rw [eval_affineNormForm]
  have numerator : u * point + v = u * (point - root) := by
    have realZero := congrArg GaussianRat.re rootZero
    have imagZero := congrArg GaussianRat.im rootZero
    apply GaussianRat.ext <;>
      simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, zero_re,
        zero_im] at realZero imagZero ⊢ <;>
      ring_nf at realZero imagZero ⊢ <;>
      linarith
  rw [numerator, normSq_mul]

/-- Exact positive-factor pullback identity. -/
theorem eval_pullbackForm
    (M : Mat2 QI) (form : HermitianForm) (z : QI)
    (denominator : M.c * z + M.d ≠ 0) :
    (pullbackForm M form).eval z =
      normSq (M.c * z + M.d) *
        form.eval (RatBox.homographic M z) := by
  have normIdentity := cleared_norm_identity M 0 z denominator
  have realIdentity := cleared_real_identity M 0 z denominator
  have imagIdentity := cleared_imag_identity M 0 z denominator
  rw [eval_normComparisonForm] at normIdentity
  rw [eval_realComparisonForm] at realIdentity
  rw [eval_imagComparisonForm] at imagIdentity
  norm_num at normIdentity realIdentity imagIdentity
  have normIdentity' : normSq (M.a * z + M.b) =
      normSq (M.c * z + M.d) * normSq (RatBox.homographic M z) := by
    simpa using normIdentity
  have realIdentity' : ((M.a * z + M.b) * conj (M.c * z + M.d)).re =
      normSq (M.c * z + M.d) * (RatBox.homographic M z).re := by
    simpa using realIdentity
  have imagIdentity' : ((M.a * z + M.b) * conj (M.c * z + M.d)).im =
      normSq (M.c * z + M.d) * (RatBox.homographic M z).im := by
    simpa using imagIdentity
  rw [show pullbackForm M form =
      HermitianForm.add
        (HermitianForm.scale form.radial (affineNormForm M.a M.b))
        (HermitianForm.add
          (HermitianForm.scale form.realLinear
            (realCrossForm M.a M.b M.c M.d))
          (HermitianForm.add
            (HermitianForm.scale form.imagLinear
              (imagCrossForm M.a M.b M.c M.d))
            (HermitianForm.scale form.constant
              (affineNormForm M.c M.d)))) by rfl]
  rw [HermitianForm.eval_add, HermitianForm.eval_scale,
    HermitianForm.eval_add, HermitianForm.eval_scale,
    HermitianForm.eval_add, HermitianForm.eval_scale,
    HermitianForm.eval_scale, eval_affineNormForm, eval_realCrossForm,
    eval_imagCrossForm, eval_affineNormForm]
  rw [normIdentity', realIdentity', imagIdentity']
  simp only [HermitianForm.eval]
  ring

/-- Pulling back a norm comparison preserves its concrete circle provenance:
the decoder matrices simply compose. -/
theorem pullbackForm_normComparison
    (outer inner : Mat2 QI) (radiusSq : ℚ) :
    pullbackForm inner (normComparisonForm outer radiusSq) =
      normComparisonForm (Mat2.mul outer inner) radiusSq := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, normComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, Mat2.mul, normSq,
      mul_re, mul_im, add_re, add_im] <;>
    ring

/-- Pulling back a real-coordinate boundary composes its decoder matrix. -/
theorem pullbackForm_realComparison
    (outer inner : Mat2 QI) (threshold : ℚ) :
    pullbackForm inner (realComparisonForm outer threshold) =
      realComparisonForm (Mat2.mul outer inner) threshold := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, realComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, Mat2.mul, normSq,
      mul_re, mul_im, add_re, add_im] <;>
    ring

/-- Pulling back an imaginary-coordinate boundary composes its decoder
matrix. -/
theorem pullbackForm_imagComparison
    (outer inner : Mat2 QI) (threshold : ℚ) :
    pullbackForm inner (imagComparisonForm outer threshold) =
      imagComparisonForm (Mat2.mul outer inner) threshold := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, imagComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, Mat2.mul, normSq,
      mul_re, mul_im, add_re, add_im] <;>
    ring

private theorem SignTest.holds_mul_pos_iff
    (test : SignTest) (factor value : ℚ) (positive : 0 < factor) :
    test.Holds (factor * value) ↔ test.Holds value := by
  cases test <;> simp only [SignTest.Holds]
  · constructor <;> intro h <;> nlinarith
  · constructor <;> intro h <;> nlinarith
  · simp [positive.ne']
  · simp [positive.ne']
  · constructor <;> intro h <;> nlinarith
  · constructor <;> intro h <;> nlinarith

namespace Formula

/-- Precompose every atom of a finite parser formula with a homography. -/
def pullback (M : Mat2 QI) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom atom => .atom ⟨pullbackForm M atom.form, atom.sign⟩
  | .and left right => .and (pullback M left) (pullback M right)
  | .or left right => .or (pullback M left) (pullback M right)

theorem pullback_iff
    (M : Mat2 QI) (formula : Formula) (z : QI)
    (denominator : M.c * z + M.d ≠ 0) :
    (pullback M formula).Holds z ↔
      formula.Holds (RatBox.homographic M z) := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | atom atom =>
      simp only [pullback, CCLParserGeometry.Formula.Holds, Atom.Holds,
        eval_pullbackForm M atom.form z denominator]
      exact SignTest.holds_mul_pos_iff atom.sign _ _
        (normSq_pos denominator)
  | and left right leftIH rightIH =>
      simp only [pullback, CCLParserGeometry.Formula.Holds]
      exact and_congr leftIH rightIH
  | or left right leftIH rightIH =>
      simp only [pullback, CCLParserGeometry.Formula.Holds]
      exact or_congr leftIH rightIH

end Formula

/-- Proposed child formula expressed directly in the original input
coordinate by applying the projective inverse of the current decoder. -/
def inputAdvanceFormula (state : RawParser.State) (bit : Bool) : Formula :=
  Formula.pullback (adjugate state.matrix) (advanceFormula state bit)

/-- The history-free part of a proposed child predicate, expressed in the
original input coordinate.  The represented-prefix invariant supplies the
unchanged historical constraints separately. -/
def inputIncrementalAdvanceFormula
    (state : RawParser.State) (bit : Bool) : Formula :=
  Formula.pullback (adjugate state.matrix)
    (incrementalAdvanceFormula state bit)

/-- On the third sector bit the incremental predicate is already the complete
local child predicate; only older history is supplied separately by the
represented-prefix invariant. -/
theorem inputIncrementalAdvanceFormula_eq_inputAdvanceFormula_of_completedSector
    (state : RawParser.State) (bit : Bool)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second)) :
    inputIncrementalAdvanceFormula state bit = inputAdvanceFormula state bit := by
  rw [inputIncrementalAdvanceFormula, inputAdvanceFormula]
  unfold incrementalAdvanceFormula
  rw [phase]

theorem inputAdvanceFormula_iff
    (state : RawParser.State) (bit : Bool) (input : QI)
    (inverseDenominator :
      (adjugate state.matrix).c * input + (adjugate state.matrix).d ≠ 0) :
    (inputAdvanceFormula state bit).Holds input ↔
      CCL.EncoderParserBridge.CanAdvanceAt state bit
        (RatBox.homographic (adjugate state.matrix) input) := by
  rw [inputAdvanceFormula,
    Formula.pullback_iff (adjugate state.matrix) _ input inverseDenominator,
    advanceFormula_iff]

/-- Pullback form of the constructive terminal converse.  At a point where
the inverse decoder is affine and the current parser predicate holds, failure
of both input-coordinate children can only be a zero-residual completed
sector. -/
theorem terminalSectorAt_of_no_inputAdvanceFormula
    (state : RawParser.State) (input : QI)
    (inverseDenominator :
      (adjugate state.matrix).c * input + (adjugate state.matrix).d ≠ 0)
    (current : state.Holds
      (RatBox.homographic (adjugate state.matrix) input))
    (none : ∀ bit, ¬(inputAdvanceFormula state bit).Holds input) :
    CCL.EncoderParserBridge.TerminalSectorAt state
      (RatBox.homographic (adjugate state.matrix) input) := by
  apply CCL.EncoderParserBridge.terminalSectorAt_of_no_canAdvanceAt
    state (RatBox.homographic (adjugate state.matrix) input) current
  intro bit advance
  exact none bit ((inputAdvanceFormula_iff state bit input
    inverseDenominator).2 advance)

theorem inputIncrementalAdvanceFormula_iff
    (state : RawParser.State) (bit : Bool) (input : QI)
    (inverseDenominator :
      (adjugate state.matrix).c * input + (adjugate state.matrix).d ≠ 0) :
    (inputIncrementalAdvanceFormula state bit).Holds input ↔
      (incrementalAdvanceFormula state bit).Holds
        (RatBox.homographic (adjugate state.matrix) input) := by
  exact Formula.pullback_iff (adjugate state.matrix)
    (incrementalAdvanceFormula state bit) input inverseDenominator

/-- Multiplying a decoder by its adjugate gives scalar multiplication by its
determinant. -/
theorem mul_adjugate (M : Mat2 QI) :
    Mat2.mul M (adjugate M) =
      ⟨determinant M, 0, 0, determinant M⟩ := by
  apply Mat2.ext <;> apply GaussianRat.ext <;>
    simp only [Mat2.mul, adjugate, determinant, mul_re, mul_im, add_re,
      add_im, sub_re, sub_im, neg_re, neg_im, zero_re, zero_im] <;> ring

/-- Multiplying an adjugate on the other side gives the same scalar matrix.
This orientation is needed when a rational boundary point is decoded first
and then returned through the inverse chart. -/
theorem adjugate_mul (M : Mat2 QI) :
    Mat2.mul (adjugate M) M =
      ⟨determinant M, 0, 0, determinant M⟩ := by
  apply Mat2.ext <;> apply GaussianRat.ext <;>
    simp only [Mat2.mul, adjugate, determinant, mul_re, mul_im, add_re,
      add_im, sub_re, sub_im, neg_re, neg_im, zero_re, zero_im] <;> ring

/-- An invertible forward homography has a nonzero adjugate denominator at
every affine image in its domain. -/
theorem adjugate_denominator_homographic_ne
    (M : Mat2 QI) (input : QI)
    (determinantNonzero : determinant M ≠ 0)
    (denominatorNonzero : M.c * input + M.d ≠ 0) :
    (adjugate M).c * RatBox.homographic M input + (adjugate M).d ≠ 0 := by
  have productDenominator : RawParserSemantics.denominator
      (Mat2.mul (adjugate M) M) input ≠ 0 := by
    rw [adjugate_mul]
    simpa [RawParserSemantics.denominator] using determinantNonzero
  exact (RawParserSemantics.denominator_mul_ne_iff
    (adjugate M) M input denominatorNonzero).mp productDenominator

/-- On the affine domain of an invertible decoder, applying the decoder and
then its adjugate recovers the original point exactly. -/
theorem homographic_adjugate_forward_inverse
    (M : Mat2 QI) (input : QI)
    (determinantNonzero : determinant M ≠ 0)
    (denominatorNonzero : M.c * input + M.d ≠ 0) :
    RatBox.homographic (adjugate M) (RatBox.homographic M input) = input := by
  have inverseDenominator := adjugate_denominator_homographic_ne M input
    determinantNonzero denominatorNonzero
  calc
    RatBox.homographic (adjugate M) (RatBox.homographic M input) =
        RatBox.homographic (Mat2.mul (adjugate M) M) input :=
      (RawParserSemantics.homographic_mul (adjugate M) M input
        denominatorNonzero inverseDenominator).symm
    _ = input := by
      rw [adjugate_mul, RatBox.homographic]
      simp only [zero_mul, zero_add, add_zero]
      calc
        determinant M * input * inv (determinant M) =
            input * (determinant M * inv (determinant M)) := by ring
        _ = input := by
          rw [mul_inv _ determinantNonzero, GaussianRat.mul_one]

/-- The inverse homography's nonzero affine denominator and a nonzero decoder
determinant force the forward denominator to remain nonzero at the recovered
tail. -/
theorem denominator_inverse_tail_ne
    (M : Mat2 QI) (input : QI)
    (determinantNonzero : determinant M ≠ 0)
    (inverseDenominator :
      (adjugate M).c * input + (adjugate M).d ≠ 0) :
    RawParserSemantics.denominator M
      (RatBox.homographic (adjugate M) input) ≠ 0 := by
  have productDenominator : RawParserSemantics.denominator
      (Mat2.mul M (adjugate M)) input ≠ 0 := by
    rw [mul_adjugate]
    simpa [RawParserSemantics.denominator] using determinantNonzero
  exact (RawParserSemantics.denominator_mul_ne_iff M (adjugate M) input
    inverseDenominator).mp productDenominator

/-- On the affine chart selected by the inverse denominator, decoding the
adjugate tail returns the original input exactly. -/
theorem homographic_adjugate_inverse
    (M : Mat2 QI) (input : QI)
    (determinantNonzero : determinant M ≠ 0)
    (inverseDenominator :
      (adjugate M).c * input + (adjugate M).d ≠ 0) :
    RatBox.homographic M (RatBox.homographic (adjugate M) input) = input := by
  have forwardDenominator := denominator_inverse_tail_ne M input
    determinantNonzero inverseDenominator
  calc
    RatBox.homographic M (RatBox.homographic (adjugate M) input) =
        RatBox.homographic (Mat2.mul M (adjugate M)) input :=
      (RawParserSemantics.homographic_mul M (adjugate M) input
        inverseDenominator forwardDenominator).symm
    _ = input := by
      rw [mul_adjugate, RatBox.homographic]
      simp only [zero_mul, zero_add, add_zero]
      calc
        determinant M * input * inv (determinant M) =
            input * (determinant M * inv (determinant M)) := by ring
        _ = input := by
          rw [mul_inv _ determinantNonzero, GaussianRat.mul_one]

/-- Construct the parser representation directly from a point satisfying the
state predicate in inverse-decoder coordinates. -/
theorem represents_of_inverse_tail
    (state : RawParser.State) (input : QI)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (holds : state.Holds
      (RatBox.homographic (adjugate state.matrix) input)) :
    RawParserSemantics.Represents state input
      (RatBox.homographic (adjugate state.matrix) input) := by
  refine ⟨denominator_inverse_tail_ne state.matrix input
      determinantNonzero inverseDenominator, ?_, holds⟩
  exact (homographic_adjugate_inverse state.matrix input
    determinantNonzero inverseDenominator).symm

/-- Original-coordinate child formula characterization for a point already
known to satisfy the current parser state in inverse-decoder coordinates. -/
theorem inputAdvanceFormula_canStep_iff
    (state : RawParser.State) (input : QI) (bit : Bool)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (holds : state.Holds
      (RatBox.homographic (adjugate state.matrix) input)) :
    (inputAdvanceFormula state bit).Holds input ↔
      RawParserSemantics.CanStep state input bit := by
  let tail := RatBox.homographic (adjugate state.matrix) input
  have represented := represents_of_inverse_tail state input
    determinantNonzero inverseDenominator holds
  have parserDeterminant : state.matrix.det ≠ 0 := by
    simpa [determinant, Mat2.det] using determinantNonzero
  rw [inputAdvanceFormula_iff state bit input inverseDenominator]
  exact (CCL.EncoderParserBridge.canStep_iff_canAdvanceAt state input tail
    parserDeterminant represented bit).symm

/-- The two input-coordinate child formulas remain mutually exclusive after
the inverse-decoder pullback whenever that affine chart is defined. -/
theorem inputAdvanceFormula_unique_at
    (state : RawParser.State) (input : QI)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    {left right : Bool}
    (leftHolds : (inputAdvanceFormula state left).Holds input)
    (rightHolds : (inputAdvanceFormula state right).Holds input) :
    left = right := by
  apply CCL.EncoderParserBridge.canAdvanceAt_unique
  · exact (inputAdvanceFormula_iff state left input
      inverseDenominator).1 leftHolds
  · exact (inputAdvanceFormula_iff state right input
      inverseDenominator).1 rightHolds

/-- Semantic specialization of pullback disjointness at a represented
input-coordinate point. -/
theorem inputAdvanceFormula_unique
    (state : RawParser.State) (input : QI)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (holds : state.Holds
      (RatBox.homographic (adjugate state.matrix) input))
    {left right : Bool}
    (leftHolds : (inputAdvanceFormula state left).Holds input)
    (rightHolds : (inputAdvanceFormula state right).Holds input) :
    left = right := by
  have parserDeterminant : state.matrix.det ≠ 0 := by
    simpa [determinant, Mat2.det] using determinantNonzero
  apply RawParserSemantics.canStep_unique parserDeterminant
  · exact (inputAdvanceFormula_canStep_iff state input left
      determinantNonzero inverseDenominator holds).1 leftHolds
  · exact (inputAdvanceFormula_canStep_iff state input right
      determinantNonzero inverseDenominator holds).1 rightHolds

/-- Total formula decision in the original winding-box coordinate. -/
inductive InputDecision (state : RawParser.State) (input : QI) where
  | terminal
      (none : ∀ bit, ¬(inputAdvanceFormula state bit).Holds input)
  | next (bit : Bool)
      (holds : (inputAdvanceFormula state bit).Holds input)
      (unique : ∀ other, (inputAdvanceFormula state other).Holds input →
        other = bit)

/-- Direct finite evaluation of the two pulled-back child formulas. -/
def decideInput
    (state : RawParser.State) (input : QI)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (holds : state.Holds
      (RatBox.homographic (adjugate state.matrix) input)) :
    InputDecision state input := by
  by_cases falseCheck :
      (inputAdvanceFormula state false).evalBool input = true
  · have falseHolds :=
      (CCLParserGeometry.Formula.evalBool_eq_true
        (inputAdvanceFormula state false) input).1 falseCheck
    exact .next false falseHolds (by
      intro other otherHolds
      exact inputAdvanceFormula_unique state input determinantNonzero
        inverseDenominator holds otherHolds falseHolds)
  · by_cases trueCheck :
        (inputAdvanceFormula state true).evalBool input = true
    · have trueHolds :=
        (CCLParserGeometry.Formula.evalBool_eq_true
          (inputAdvanceFormula state true) input).1 trueCheck
      exact .next true trueHolds (by
        intro other otherHolds
        exact inputAdvanceFormula_unique state input determinantNonzero
          inverseDenominator holds otherHolds trueHolds)
    · exact .terminal (by
        intro bit
        cases bit
        · intro falseHolds
          exact falseCheck
            ((CCLParserGeometry.Formula.evalBool_eq_true
              (inputAdvanceFormula state false) input).2 falseHolds)
        · intro trueHolds
          exact trueCheck
            ((CCLParserGeometry.Formula.evalBool_eq_true
              (inputAdvanceFormula state true) input).2 trueHolds))

end CCLFormulaPullback
end FTA
