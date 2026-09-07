import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Curves
import CCL.Boundary.NextBit

/-!
# Finite descriptions of CCL atom boundaries

An unresolved Hermitian atom is useful to the equality-owner layer only when
its zero boundary retains constructive provenance.  The boundary is either a
rationally parameterized generalized circle/line, a finite explicit zero set,
or the identically-zero form.  This avoids recovering geometry from bare
coefficients by an unbounded search.
-/

namespace CCL.CCLBoundaryDescription

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev Parametrization := CCL.CCLBoundaryCurves.Parametrization

open RFAP.ConstructiveGaussian.Gaussian
open CCL.CCLGeometry

/-- Exact geometric source of a parameterized zero boundary.  Retaining the
matrix and the circle/line constructor makes bounded chart generation a
finite computation rather than reverse-engineering bare form coefficients. -/
inductive CurveSource (reference : Mat2) (form : HermitianForm) where
  | norm (matrix : Mat2)
      (determinantNonzero :
        CCL.CCLPullback.determinant matrix ≠ 0)
      (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
      (base : Gaussian)
      (baseNonzero : base ≠ 0)
      (form_eq : form = normComparisonForm matrix (normSq base))
  | real (matrix : Mat2)
      (determinantNonzero :
        CCL.CCLPullback.determinant matrix ≠ 0)
      (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
      (threshold : Coordinate)
      (form_eq : form = realComparisonForm matrix threshold)
  | imaginary (matrix : Mat2)
      (determinantNonzero :
        CCL.CCLPullback.determinant matrix ≠ 0)
      (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
      (threshold : Coordinate)
      (form_eq : form = imagComparisonForm matrix threshold)

namespace CurveSource

/-- Primary affine chart of a geometric source. -/
def primary {reference : Mat2} {form : HermitianForm} :
    CurveSource reference form → Parametrization form
  | .norm matrix determinantNonzero _lowerRow base _baseNonzero form_eq =>
      form_eq.symm ▸
        CCL.CCLBoundaryCurves.normComparison matrix
          determinantNonzero base
  | .real matrix determinantNonzero _lowerRow threshold form_eq =>
      form_eq.symm ▸
        CCL.CCLBoundaryCurves.realComparison matrix
          determinantNonzero threshold
  | .imaginary matrix determinantNonzero _lowerRow threshold form_eq =>
      form_eq.symm ▸
        CCL.CCLBoundaryCurves.imaginaryComparison matrix
          determinantNonzero threshold

/-- The circle's reciprocal chart supplies its missing projective parameter;
coordinate lines need no companion. -/
def companions {reference : Mat2} {form : HermitianForm} :
    (source : CurveSource reference form) → List (Parametrization form)
  | .norm matrix determinantNonzero _lowerRow base _baseNonzero form_eq =>
      [form_eq.symm ▸
        CCL.CCLBoundaryCurves.normComparisonReciprocal matrix
          determinantNonzero base]
  | .real _ _ _ _ _ | .imaginary _ _ _ _ _ => []

end CurveSource

/-- Constructive zero-boundary provenance. -/
inductive Description (reference : Mat2) (form : HermitianForm) where
  | curve (source : CurveSource reference form)
  | finite (points : List Gaussian)
      (complete : ∀ value, form.eval value = 0 → value ∈ points)
      (nonnegative : ∀ value, 0 ≤ form.eval value)
  | universal (zero : ∀ value, form.eval value = 0)

namespace Description

/-- Transport a boundary description across a proved form identity. -/
def cast {reference : Mat2} {left right : HermitianForm}
    (equal : left = right)
    (description : Description reference left) : Description reference right := by
  subst right
  exact description

/-- The zero set of a squared affine norm is computed by one equality test.
It is empty, a singleton, or universal; no root search is involved. -/
def affineNorm (reference : Mat2) (u v : Gaussian) :
    Description reference (affineNormForm u v) := by
  if uZero : u = 0 then
    if vZero : v = 0 then
      exact .universal (by
        intro value
        rw [eval_affineNormForm, uZero, vZero, zero_mul, zero_add, normSq_zero])
    else
      exact .finite [] (by
          intro value evaluatesZero
          rw [eval_affineNormForm, uZero, zero_mul, zero_add] at evaluatesZero
          exact (vZero (normSq_eq_zero.mp evaluatesZero)).elim)
        (by
          intro value
          rw [eval_affineNormForm, uZero, zero_mul, zero_add]
          exact normSq_nonneg v)
  else
    let point := (-v) * u⁻¹
    exact .finite [point] (by
        intro value evaluatesZero
        have affineZero : u * value + v = 0 := by
          apply normSq_eq_zero.mp
          simpa only [eval_affineNormForm] using evaluatesZero
        have product : u * value = -v := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext
          · have coordinate := congrArg
                RFAP.ConstructiveGaussian.Gaussian.re affineZero
            simp only [add_re, zero_re] at coordinate
            simp only [neg_re]
            calc
              (u * value).re = (u * value).re + v.re - v.re := by ring1
              _ = 0 - v.re := by rw [coordinate]
              _ = -v.re := by ring1
          · have coordinate := congrArg
                RFAP.ConstructiveGaussian.Gaussian.im affineZero
            simp only [add_im, zero_im] at coordinate
            simp only [neg_im]
            calc
              (u * value).im = (u * value).im + v.im - v.im := by ring1
              _ = 0 - v.im := by rw [coordinate]
              _ = -v.im := by ring1
        have pointProduct : point * u = -v := by
          dsimp only [point]
          calc
            (-v) * u⁻¹ * u = (-v) * (u⁻¹ * u) :=
              RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
            _ = (-v) * 1 := by
              rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
                inv_mul _ uZero]
            _ = -v := RFAP.ConstructiveGaussian.Gaussian.mul_one _
        have equal : value = point := by
          apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne uZero
          calc
            value * u = u * value :=
              RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
            _ = -v := product
            _ = point * u := pointProduct.symm
        rw [List.mem_singleton]
        exact equal)
      (by
        intro value
        rw [eval_affineNormForm]
        exact normSq_nonneg (u * value + v))

/-- Pulling back a squared affine norm still has an explicit finite zero-set
description. -/
def pulledAffineNorm
    (matrix : CCL.GaussianProjective.Mat2) (u v : Gaussian) :
    Description matrix
      (CCL.CCLPullback.pullbackForm matrix
        (affineNormForm u v)) :=
  cast
    (CCL.CCLPullback.pullbackForm_affineNorm matrix u v).symm
    (affineNorm matrix (u * matrix.a + v * matrix.c)
      (u * matrix.b + v * matrix.d))

end Description

private theorem normComparison_zero_eq_affineNorm (matrix : Mat2) :
    normComparisonForm matrix 0 = affineNormForm matrix.a matrix.b := by
  apply HermitianForm.ext <;>
    simp only [normComparisonForm, HermitianForm.sub, HermitianForm.add,
      HermitianForm.neg, HermitianForm.scale, affineNormForm] <;>
    ring1

private theorem determinant_mul_ne
    (outer inner : Mat2)
    (outerNonzero : CCL.Chordal.Mat2.det outer ≠ 0)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0) :
    CCL.Chordal.Mat2.det (CCL.Mat2.mul outer inner) ≠ 0 := by
  rw [CCL.RawParser.det_mul]
  exact mul_ne_zero_direct outerNonzero innerNonzero

private theorem mul_lowerRow
    (outer inner : Mat2)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1) :
    (CCL.Mat2.mul outer inner).c = inner.c ∧
      (CCL.Mat2.mul outer inner).d = inner.d := by
  rcases outerLowerRow with ⟨lowerLeft, lowerRight⟩
  constructor <;>
    simp only [CCL.Mat2.mul, lowerLeft, lowerRight,
      RFAP.ConstructiveGaussian.Gaussian.zero_mul,
      RFAP.ConstructiveGaussian.Gaussian.one_mul,
      RFAP.ConstructiveGaussian.Gaussian.zero_add]

/-- Pullback of a rational circle comparison, retaining the composed
homography rather than attempting to reconstruct a circle from coefficients. -/
def pulledNormComparison
    (outer inner : Mat2)
    (outerNonzero : CCL.Chordal.Mat2.det outer ≠ 0)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1)
    (base : Gaussian) :
    Description inner
      (CCL.CCLPullback.pullbackForm inner
        (normComparisonForm outer (normSq base))) := by
  by_cases baseZero : base = 0
  · have sourceIdentity :
        normComparisonForm outer (normSq base) =
          affineNormForm outer.a outer.b := by
      rw [baseZero, normSq_zero]
      exact normComparison_zero_eq_affineNorm outer
    exact Description.cast
      (congrArg (CCL.CCLPullback.pullbackForm inner)
        sourceIdentity).symm
      (Description.pulledAffineNorm inner outer.a outer.b)
  · exact .curve (.norm (CCL.Mat2.mul outer inner)
      (determinant_mul_ne outer inner outerNonzero innerNonzero)
      (mul_lowerRow outer inner outerLowerRow) base baseZero
      (CCL.CCLPullback.pullbackForm_normComparison
        outer inner (normSq base)))

/-- Pullback of a rational vertical comparison line. -/
def pulledRealComparison
    (outer inner : Mat2)
    (outerNonzero : CCL.Chordal.Mat2.det outer ≠ 0)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1)
    (threshold : Coordinate) :
    Description inner
      (CCL.CCLPullback.pullbackForm inner
        (realComparisonForm outer threshold)) := by
  exact .curve (.real (CCL.Mat2.mul outer inner)
    (determinant_mul_ne outer inner outerNonzero innerNonzero)
    (mul_lowerRow outer inner outerLowerRow) threshold
    (CCL.CCLPullback.pullbackForm_realComparison
      outer inner threshold))

/-- Pullback of a rational horizontal comparison line. -/
def pulledImaginaryComparison
    (outer inner : Mat2)
    (outerNonzero : CCL.Chordal.Mat2.det outer ≠ 0)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1)
    (threshold : Coordinate) :
    Description inner
      (CCL.CCLPullback.pullbackForm inner
        (imagComparisonForm outer threshold)) := by
  exact .curve (.imaginary (CCL.Mat2.mul outer inner)
    (determinant_mul_ne outer inner outerNonzero innerNonzero)
    (mul_lowerRow outer inner outerLowerRow) threshold
    (CCL.CCLPullback.pullbackForm_imagComparison
      outer inner threshold))

private theorem affineNormComparison_eq
    (threshold : Coordinate) :
    CCL.CCLFormula.affineNormComparisonForm threshold =
      normComparisonForm CCL.RawParser.identityMatrix threshold := by
  apply HermitianForm.ext <;>
    simp only [CCL.CCLFormula.affineNormComparisonForm,
      CCL.CCLFormula.constantForm, normComparisonForm,
      HermitianForm.sub, HermitianForm.add, HermitianForm.neg,
      HermitianForm.scale, affineNormForm,
      CCL.RawParser.identityMatrix, normSq,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im,
      RFAP.ConstructiveGaussian.Gaussian.zero_re,
      RFAP.ConstructiveGaussian.Gaussian.zero_im] <;>
    ring1

private theorem scaledNormComparison_eq
    (exponent : Nat) (threshold : Coordinate) :
    CCL.CCLFormula.scaledNormComparisonForm exponent threshold =
      normComparisonForm
        (CCL.CCLFormula.normalizationMatrix
          .initialLow exponent) threshold := by
  apply HermitianForm.ext
  all_goals
    simp only [CCL.CCLFormula.scaledNormComparisonForm,
      CCL.CCLFormula.constantForm,
      CCL.CCLFormula.normalizationMatrix,
      CCL.Mat2.scale, normComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im,
      RFAP.ConstructiveGaussian.Gaussian.zero_re,
      RFAP.ConstructiveGaussian.Gaussian.zero_im, normSq_one, normSq_zero]
  · rw [normSq_natPow, normSq_gamma]
    ring1
  · ring1
  · ring1
  · ring1

private theorem identityMatrix_det_ne :
    CCL.Chordal.Mat2.det
      CCL.RawParser.identityMatrix ≠ 0 := by
  intro determinantZero
  have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re determinantZero
  simp only [CCL.Chordal.Mat2.det,
    CCL.RawParser.identityMatrix,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.one_re,
    RFAP.ConstructiveGaussian.Gaussian.one_im,
    RFAP.ConstructiveGaussian.Gaussian.zero_re,
    RFAP.ConstructiveGaussian.Gaussian.zero_im] at realZero
  exact RFAP.ConstructiveFraction.zero_ne_one realZero.symm

private theorem identityMatrix_lowerRow :
    CCL.RawParser.identityMatrix.c = 0 ∧
      CCL.RawParser.identityMatrix.d = 1 :=
  ⟨rfl, rfl⟩

private theorem normalizationMatrix_lowerRow
    (kind : CCL.RawParser.BlockKind) (exponent : Nat) :
    (CCL.CCLFormula.normalizationMatrix kind exponent).c = 0 ∧
      (CCL.CCLFormula.normalizationMatrix kind exponent).d = 1 := by
  cases kind <;> exact ⟨rfl, rfl⟩

/-- Pulled-back boundary `normSq z = 2^exponent`. -/
def pulledAffineNormDyadic
    (inner : Mat2)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0)
    (exponent : Nat) :
    Description inner
      (CCL.CCLPullback.pullbackForm inner
        (CCL.CCLFormula.affineNormComparisonForm
          ((2 : Coordinate) ^ exponent))) := by
  let base := natPow gamma exponent
  have sourceIdentity :
      CCL.CCLFormula.affineNormComparisonForm
          ((2 : Coordinate) ^ exponent) =
        normComparisonForm CCL.RawParser.identityMatrix
          (normSq base) := by
    rw [affineNormComparison_eq, normSq_natPow, normSq_gamma]
  exact Description.cast
    (congrArg (CCL.CCLPullback.pullbackForm inner)
      sourceIdentity).symm
    (pulledNormComparison CCL.RawParser.identityMatrix inner
      identityMatrix_det_ne innerNonzero identityMatrix_lowerRow base)

/-- Pulled-back boundary `2^exponent * normSq z = 1`. -/
def pulledScaledNormOne
    (inner : Mat2)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0)
    (exponent : Nat) :
    Description inner
      (CCL.CCLPullback.pullbackForm inner
        (CCL.CCLFormula.scaledNormComparisonForm exponent 1)) := by
  let outer := CCL.CCLFormula.normalizationMatrix
    CCL.RawParser.BlockKind.initialLow exponent
  have oneNorm : normSq (1 : Gaussian) = 1 := by decide
  have sourceIdentity :
      CCL.CCLFormula.scaledNormComparisonForm exponent 1 =
        normComparisonForm outer (normSq (1 : Gaussian)) := by
    rw [scaledNormComparison_eq, oneNorm]
  exact Description.cast
    (congrArg (CCL.CCLPullback.pullbackForm inner)
      sourceIdentity).symm
    (pulledNormComparison outer inner
      (CCL.CCLFormula.normalizationMatrix_det_ne
        .initialLow exponent) innerNonzero
      (normalizationMatrix_lowerRow .initialLow exponent) 1)

/-- Pulled-back boundary `2^exponent * normSq z = 2`. -/
def pulledScaledNormTwo
    (inner : Mat2)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0)
    (exponent : Nat) :
    Description inner
      (CCL.CCLPullback.pullbackForm inner
        (CCL.CCLFormula.scaledNormComparisonForm exponent 2)) := by
  let outer := CCL.CCLFormula.normalizationMatrix
    CCL.RawParser.BlockKind.initialLow exponent
  have sourceIdentity :
      CCL.CCLFormula.scaledNormComparisonForm exponent 2 =
        normComparisonForm outer (normSq gamma) := by
    rw [scaledNormComparison_eq, normSq_gamma]
  exact Description.cast
    (congrArg (CCL.CCLPullback.pullbackForm inner)
      sourceIdentity).symm
    (pulledNormComparison outer inner
      (CCL.CCLFormula.normalizationMatrix_det_ne
        .initialLow exponent) innerNonzero
      (normalizationMatrix_lowerRow .initialLow exponent) gamma)

end CCL.CCLBoundaryDescription
