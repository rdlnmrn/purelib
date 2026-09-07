import FTA.ProjectivePath
import FTA.CCLIntersectionSampler

/-!
# Affine clearance from projective polynomial paths

Theorem 5.3 bounds the squared norm of a denominator-cleared polynomial on a
rational parameter cell.  This module computes a finite upper bound for the
accumulated projective denominator and divides by it, yielding the positive
affine clearance used in the zero-count branch of Theorem 10.2.
-/

namespace FTA
namespace ProjectivePathBounds

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.PathClearance
open FTA.ProjectivePath
open FTA.RationalPolynomialBounds
open FTA.CCLIntersectionSampler

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI
abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- Real coordinate of the accumulated projective denominator power. -/
def denominatorReal (p : GaussianPolynomial) (path : Path) : RatPolynomial :=
  realPart (clearedDenominatorPower p path)

/-- Imaginary coordinate of the accumulated projective denominator power. -/
def denominatorImag (p : GaussianPolynomial) (path : Path) : RatPolynomial :=
  imagPart (clearedDenominatorPower p path)

@[simp] theorem eval_denominatorReal
    (p : GaussianPolynomial) (path : Path) (t : ℚ) :
    (denominatorReal p path).eval t =
      ((clearedDenominatorPower p path).eval
        (PathPolynomial.ofRat t)).re := by
  rw [denominatorReal, eval_realPart]

@[simp] theorem eval_denominatorImag
    (p : GaussianPolynomial) (path : Path) (t : ℚ) :
    (denominatorImag p path).eval t =
      ((clearedDenominatorPower p path).eval
        (PathPolynomial.ofRat t)).im := by
  rw [denominatorImag, eval_imagPart]

/-- Executable upper bound for the squared norm of the accumulated projective
denominator throughout a closed rational parameter interval. -/
def denominatorNormMajorant (p : GaussianPolynomial) (path : Path)
    (interval : RationalInterval) : ℚ :=
  let B := intervalMagnitude interval.lower interval.upper
  max 1 (denseEvalAbsBound (denominatorReal p path) B ^ 2 +
    denseEvalAbsBound (denominatorImag p path) B ^ 2)

theorem denominatorNormMajorant_pos (p : GaussianPolynomial) (path : Path)
    (interval : RationalInterval) :
    0 < denominatorNormMajorant p path interval := by
  exact zero_lt_one.trans_le (le_max_left _ _)

theorem normSq_clearedDenominatorPower_le_majorant
    (p : GaussianPolynomial) (path : Path) (interval : RationalInterval)
    {t : ℚ} (hLower : interval.lower ≤ t) (hUpper : t ≤ interval.upper) :
    normSq ((clearedDenominatorPower p path).eval
      (PathPolynomial.ofRat t)) ≤ denominatorNormMajorant p path interval := by
  let B := intervalMagnitude interval.lower interval.upper
  have hB : 0 ≤ B := (intervalMagnitude_pos _ _).le
  have htB : |t| ≤ B := abs_le_intervalMagnitude hLower hUpper
  have hrealAbs := abs_dense_eval_le_denseEvalAbsBound
    (denominatorReal p path) hB htB
  have himagAbs := abs_dense_eval_le_denseEvalAbsBound
    (denominatorImag p path) hB htB
  have hrealSq : (denominatorReal p path).eval t ^ 2 ≤
      denseEvalAbsBound (denominatorReal p path) B ^ 2 := by
    have h := pow_le_pow_left₀
      (abs_nonneg ((denominatorReal p path).eval t)) hrealAbs 2
    simpa [sq_abs] using h
  have himagSq : (denominatorImag p path).eval t ^ 2 ≤
      denseEvalAbsBound (denominatorImag p path) B ^ 2 := by
    have h := pow_le_pow_left₀
      (abs_nonneg ((denominatorImag p path).eval t)) himagAbs 2
    simpa [sq_abs] using h
  rw [normSq, ← eval_denominatorReal, ← eval_denominatorImag]
  exact (add_le_add hrealSq himagSq).trans (le_max_right _ _)

/-- A positive lower bound for the displayed path-denominator norm raises to
the exact finite Horner exponent and bounds the cleared denominator power. -/
theorem denominatorCertificate_pow_le_normSq_clearedDenominatorPower
    {p : GaussianPolynomial} {path : Path} {interval : RationalInterval}
    (certificate : DenominatorCertificate path interval)
    {t : ℚ} (hLower : interval.lower ≤ t) (hUpper : t ≤ interval.upper) :
    certificate.bound ^ p.coeffs.length ≤
      normSq ((clearedDenominatorPower p path).eval
        (PathPolynomial.ofRat t)) := by
  rw [clearedDenominatorPower_eval_eq_pow, normSq_pow,
    ← CCLPathIntersection.eval_denominatorNorm]
  exact pow_le_pow_left₀ certificate.positive.le
    (certificate.lower hLower hUpper) p.coeffs.length

/-- Explicit affine residual obtained from upper bounds for both cleared
coordinates and a positive whole-cell projective denominator margin. -/
def affineResidualBound
    (p : GaussianPolynomial) {path : Path} {interval : RationalInterval}
    (certificate : DenominatorCertificate path interval)
    (realBound imagBound : ℚ) : ℚ :=
  (realBound ^ 2 + imagBound ^ 2) /
    certificate.bound ^ p.coeffs.length

theorem normSq_eval_le_affineResidualBound
    {p : GaussianPolynomial} {path : Path} {interval : RationalInterval}
    (certificate : DenominatorCertificate path interval)
    {t realBound imagBound : ℚ}
    (hLower : interval.lower ≤ t) (hUpper : t ≤ interval.upper)
    (realSmall : |(clearedReal p path).eval t| ≤ realBound)
    (imagSmall : |(clearedImag p path).eval t| ≤ imagBound) :
    normSq (p.eval (path.value t)) ≤
      affineResidualBound p certificate realBound imagBound := by
  have realSquare : (clearedReal p path).eval t ^ 2 ≤ realBound ^ 2 := by
    calc
      (clearedReal p path).eval t ^ 2 =
          |(clearedReal p path).eval t| ^ 2 := (sq_abs _).symm
      _ ≤ realBound ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) realSmall 2
  have imagSquare : (clearedImag p path).eval t ^ 2 ≤ imagBound ^ 2 := by
    calc
      (clearedImag p path).eval t ^ 2 =
          |(clearedImag p path).eval t| ^ 2 := (sq_abs _).symm
      _ ≤ imagBound ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) imagSmall 2
  have denominatorPower :=
    denominatorCertificate_pow_le_normSq_clearedDenominatorPower certificate
      (p := p) hLower hUpper
  have denominatorPositive :
      0 < certificate.bound ^ p.coeffs.length :=
    pow_pos certificate.positive p.coeffs.length
  have valueNonnegative : 0 ≤ normSq (p.eval (path.value t)) :=
    normSq_nonneg _
  have denominatorNonzero := certificate.denominator_ne hLower hUpper
  have scaled :
      certificate.bound ^ p.coeffs.length *
          normSq (p.eval (path.value t)) ≤
        realBound ^ 2 + imagBound ^ 2 := by
    calc
      certificate.bound ^ p.coeffs.length *
          normSq (p.eval (path.value t)) ≤
        normSq ((clearedDenominatorPower p path).eval
            (PathPolynomial.ofRat t)) *
          normSq (p.eval (path.value t)) :=
        mul_le_mul_of_nonneg_right denominatorPower valueNonnegative
      _ = (clearedReal p path).eval t ^ 2 +
          (clearedImag p path).eval t ^ 2 :=
        (eval_cleared_normSq p path t denominatorNonzero).symm
      _ ≤ realBound ^ 2 + imagBound ^ 2 :=
        add_le_add realSquare imagSquare
  apply (le_div_iff₀ denominatorPositive).2
  calc
    normSq (p.eval (path.value t)) *
        certificate.bound ^ p.coeffs.length =
      certificate.bound ^ p.coeffs.length *
        normSq (p.eval (path.value t)) := mul_comm _ _
    _ ≤ realBound ^ 2 + imagBound ^ 2 := scaled

/-- Positive affine clearance for a Gaussian polynomial evaluated on a
projective path.  The denominator-nonzero argument remains explicit because
the finite parameter-cell decomposition is responsible for excluding poles. -/
structure AffineCertificate (p : GaussianPolynomial) (path : Path)
    (interval : RationalInterval) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ t : ℚ, interval.lower ≤ t → t ≤ interval.upper →
    path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 →
      bound ≤ normSq (p.eval (path.value t))

/-- Divide any positive lower bound for the squared cleared coordinates by
the coefficient-computed upper bound for the accumulated projective
denominator.  This reusable form also accepts certificates obtained from a
common guarded partition rather than a fresh zero-count computation. -/
def affineCertificateOfCleared
    (p : GaussianPolynomial) (path : Path) (interval : RationalInterval)
    (cleared : PathClearance.Certificate
      (clearedReal p path) (clearedImag p path) interval) :
    AffineCertificate p path interval := by
  let M := denominatorNormMajorant p path interval
  exact
    { bound := cleared.bound / M
      positive := div_pos cleared.positive
        (denominatorNormMajorant_pos p path interval)
      lower := by
        intro t hLower hUpper hden
        have hcleared := cleared.lower t hLower hUpper
        rw [ProjectivePath.eval_cleared_normSq p path t hden] at hcleared
        have hpower := normSq_clearedDenominatorPower_le_majorant
          p path interval hLower hUpper
        have hvalue : 0 ≤ normSq (p.eval (path.value t)) := normSq_nonneg _
        have hscaled : cleared.bound ≤
            M * normSq (p.eval (path.value t)) := by
          have h := hcleared.trans
            (mul_le_mul_of_nonneg_right hpower hvalue)
          simpa only [M] using h
        apply (div_le_iff₀ (denominatorNormMajorant_pos p path interval)).2
        calc
          cleared.bound ≤
              denominatorNormMajorant p path interval *
                normSq (p.eval (path.value t)) := by
            simpa only [M] using hscaled
          _ = normSq (p.eval (path.value t)) *
              denominatorNormMajorant p path interval := by ring }

/-- The zero common-factor count of Theorem 5.3, followed by the finite
denominator upper bound, computes an affine curve-clearance certificate. -/
def computeAffineClearance
    (p : GaussianPolynomial) (path : Path)
    (hnonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval interval.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval interval.upper ≠ 0)
    (countZero : ProjectivePath.commonFactorRootCount2 p path hnonzero
      interval.lower interval.upper = 0) :
    AffineCertificate p path interval :=
  affineCertificateOfCleared p path interval
    (ProjectivePath.computeClearance p path hnonzero interval proper
      lowerClear upperClear countZero)

end ProjectivePathBounds
end FTA
