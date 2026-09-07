import FTA.PathPolynomial
import FTA.PositiveLowerBound

/-!
# Finite clearance certificates for rational polynomial paths

This module implements the quantitative zero-count branch of Theorem 5.3.
For rational coordinate polynomials `P,Q`, executable symmetric gcd reduction
gives `P = g P₁`, `Q = g Q₁` and a dense Bézout certificate for the coprime
pair `P₁,Q₁`.  A positive lower bound for `g²` and a finite Horner upper bound
for the two Bézout coefficients combine through the exact sum-of-squares
identity to produce a positive lower bound for `P²+Q²`.
-/

namespace FTA.PathClearance

open CCL
open CCL.GaussianRat
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.DenseGCD
open FTA.DenseSquarefree
open FTA.PathPolynomial
open FTA.PositiveLowerBound
open FTA.RationalPolynomialBounds
open FTA.SquarefreeFactorization
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ

def commonFactor (P Q : RatPolynomial) : RatPolynomial :=
  symmetricGCD P Q

def reducedReal (P Q : RatPolynomial) : RatPolynomial :=
  symmetricLeftFactor P Q

def reducedImag (P Q : RatPolynomial) : RatPolynomial :=
  symmetricRightFactor P Q

theorem commonFactor_mul_reducedReal_eval (P Q : RatPolynomial) (t : ℚ) :
    P.eval t = (commonFactor P Q).eval t * (reducedReal P Q).eval t :=
  symmetricLeftFactor_eval_identity P Q t

theorem commonFactor_mul_reducedImag_eval (P Q : RatPolynomial) (t : ℚ) :
    Q.eval t = (commonFactor P Q).eval t * (reducedImag P Q).eval t :=
  symmetricRightFactor_eval_identity P Q t

theorem commonFactor_isZero_false {P Q : RatPolynomial}
    (hnonzero : P.isZero = false ∨ Q.isZero = false) :
    (commonFactor P Q).isZero = false :=
  symmetricGCD_isZero_false hnonzero

theorem reducedPair_nonzero {P Q : RatPolynomial}
    (hnonzero : P.isZero = false ∨ Q.isZero = false) :
    (reducedReal P Q).isZero = false ∨ (reducedImag P Q).isZero = false := by
  rcases hnonzero with hP | hQ
  · exact Or.inl (symmetricLeftFactor_isZero_false hP)
  · exact Or.inr (symmetricRightFactor_isZero_false hQ)

/-- The actual dense Bézout certificate for the two gcd quotients. -/
def reducedPairCertificate (P Q : RatPolynomial)
    (hnonzero : P.isZero = false ∨ Q.isZero = false) :
    CoprimeCertificate (reducedReal P Q) (reducedImag P Q) :=
  certificateOfIsCoprimeNonzero (reducedReal P Q) (reducedImag P Q)
    (reducedPair_nonzero hnonzero) (symmetricFactors_isCoprime P Q hnonzero)

/-- If a nonzero polynomial pair vanishes simultaneously at a rational
parameter, its computed common factor vanishes there.  Otherwise the Bézout
identity for the reduced pair would evaluate to `0 = 1`. -/
theorem commonFactor_eval_eq_zero_of_eval_eq_zero
    {P Q : RatPolynomial}
    (hnonzero : P.isZero = false ∨ Q.isZero = false) {t : ℚ}
    (realZero : P.eval t = 0) (imagZero : Q.eval t = 0) :
    (commonFactor P Q).eval t = 0 := by
  by_contra commonNonzero
  have reducedRealZero : (reducedReal P Q).eval t = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left commonNonzero
    rw [← commonFactor_mul_reducedReal_eval P Q t, realZero]
  have reducedImagZero : (reducedImag P Q).eval t = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left commonNonzero
    rw [← commonFactor_mul_reducedImag_eval P Q t, imagZero]
  have identity := (reducedPairCertificate P Q hnonzero).identity t
  simp [reducedRealZero, reducedImagZero] at identity

/-- The finite factor-descent Sturm count of the common coordinate factor. -/
def commonFactorRootCount2 (P Q : RatPolynomial)
    (hnonzero : P.isZero = false ∨ Q.isZero = false) (a b : ℚ) : ℤ :=
  factorRootCount2 (commonFactor P Q) (commonFactor_isZero_false hnonzero) a b

/-- Positive quantitative proof that a coordinate pair stays away from the
origin throughout a rational parameter interval. -/
structure Certificate (P Q : RatPolynomial) (interval : RationalInterval) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ t : ℚ, interval.lower ≤ t → t ≤ interval.upper →
    bound ≤ P.eval t ^ 2 + Q.eval t ^ 2

/-- Executable upper bound for the squared Euclidean norm of the two dense
Bézout coefficients on the whole interval. -/
def bezoutNormMajorant {P Q : RatPolynomial}
    (certificate : CoprimeCertificate P Q) (interval : RationalInterval) : ℚ :=
  let B := intervalMagnitude interval.lower interval.upper
  max 1 (denseEvalAbsBound certificate.left B ^ 2 +
    denseEvalAbsBound certificate.right B ^ 2)

theorem bezoutNormMajorant_pos {P Q : RatPolynomial}
    (certificate : CoprimeCertificate P Q) (interval : RationalInterval) :
    0 < bezoutNormMajorant certificate interval := by
  exact zero_lt_one.trans_le (le_max_left _ _)

theorem bezout_eval_sq_add_le_majorant {P Q : RatPolynomial}
    (certificate : CoprimeCertificate P Q) (interval : RationalInterval)
    {t : ℚ} (hLower : interval.lower ≤ t) (hUpper : t ≤ interval.upper) :
    certificate.left.eval t ^ 2 + certificate.right.eval t ^ 2 ≤
      bezoutNormMajorant certificate interval := by
  let B := intervalMagnitude interval.lower interval.upper
  have hB : 0 ≤ B := (intervalMagnitude_pos _ _).le
  have htB : |t| ≤ B := abs_le_intervalMagnitude hLower hUpper
  have hleftAbs := abs_dense_eval_le_denseEvalAbsBound certificate.left hB htB
  have hrightAbs := abs_dense_eval_le_denseEvalAbsBound certificate.right hB htB
  have hleftSq : certificate.left.eval t ^ 2 ≤
      denseEvalAbsBound certificate.left B ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (certificate.left.eval t)) hleftAbs 2
    simpa [sq_abs] using this
  have hrightSq : certificate.right.eval t ^ 2 ≤
      denseEvalAbsBound certificate.right B ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (certificate.right.eval t)) hrightAbs 2
    simpa [sq_abs] using this
  exact (add_le_add hleftSq hrightSq).trans (le_max_right _ _)

/-- A displayed dense Bézout identity directly supplies a quantitative
sum-of-squares clearance certificate on any closed rational interval.  This is
the safe-line branch after a nonzero elimination value has certified the two
coordinate polynomials coprime. -/
def certificateOfCoprime {P Q : RatPolynomial}
    (coprime : CoprimeCertificate P Q) (interval : RationalInterval) :
    Certificate P Q interval := by
  let M := bezoutNormMajorant coprime interval
  exact
    { bound := 1 / M
      positive := div_pos zero_lt_one (bezoutNormMajorant_pos coprime interval)
      lower := by
        intro t hLower hUpper
        let S := P.eval t ^ 2 + Q.eval t ^ 2
        have hS : 0 ≤ S := add_nonneg (sq_nonneg _) (sq_nonneg _)
        have hcoefficients :
            coprime.left.eval t ^ 2 + coprime.right.eval t ^ 2 ≤ M :=
          bezout_eval_sq_add_le_majorant coprime interval hLower hUpper
        have hbezout :
            coprime.left.eval t * P.eval t +
              coprime.right.eval t * Q.eval t = 1 := coprime.identity t
        have hsos : 1 ≤
            (coprime.left.eval t ^ 2 + coprime.right.eval t ^ 2) * S := by
          calc
            1 = (coprime.left.eval t * P.eval t +
                coprime.right.eval t * Q.eval t) ^ 2 := by
              rw [hbezout]
              norm_num
            _ ≤ (coprime.left.eval t ^ 2 +
                coprime.right.eval t ^ 2) * S := by
              dsimp only [S]
              nlinarith [sq_nonneg
                (coprime.left.eval t * Q.eval t -
                  coprime.right.eval t * P.eval t)]
        have hone : 1 ≤ M * S :=
          hsos.trans (mul_le_mul_of_nonneg_right hcoefficients hS)
        apply (div_le_iff₀ (bezoutNormMajorant_pos coprime interval)).2
        dsimp only [S] at hone ⊢
        nlinarith }

/-- Combine any positive squared lower bound for the computed common factor
with the executable Bézout certificate for the reduced coordinate pair.  This
is the reusable quantitative bridge from an independently certified
common-factor-free interval to clearance of both original coordinates. -/
def certificateOfCommonFactor {P Q : RatPolynomial}
    (hnonzero : P.isZero = false ∨ Q.isZero = false)
    (interval : RationalInterval)
    (commonCertificate : PositiveLowerBound.Certificate
      (commonFactor P Q) interval) :
    Certificate P Q interval := by
  let P₁ := reducedReal P Q
  let Q₁ := reducedImag P Q
  let coprime := reducedPairCertificate P Q hnonzero
  let reducedCertificate := certificateOfCoprime coprime interval
  exact
    { bound := commonCertificate.bound * reducedCertificate.bound
      positive := mul_pos commonCertificate.positive
        reducedCertificate.positive
      lower := by
        intro t lower upper
        have commonLower := commonCertificate.lower t lower upper
        have reducedLower := reducedCertificate.lower t lower upper
        have realIdentity : P.eval t =
            (commonFactor P Q).eval t * P₁.eval t := by
          simpa [P₁] using commonFactor_mul_reducedReal_eval P Q t
        have imagIdentity : Q.eval t =
            (commonFactor P Q).eval t * Q₁.eval t := by
          simpa [Q₁] using commonFactor_mul_reducedImag_eval P Q t
        calc
          commonCertificate.bound * reducedCertificate.bound ≤
              (commonFactor P Q).eval t ^ 2 *
                (P₁.eval t ^ 2 + Q₁.eval t ^ 2) :=
            mul_le_mul commonLower reducedLower reducedCertificate.positive.le
              (sq_nonneg _)
          _ = P.eval t ^ 2 + Q.eval t ^ 2 := by
            rw [realIdentity, imagIdentity]
            ring }

/-- Quantitative zero-count branch of Theorem 5.3 for a pair of rational
coordinate polynomials. -/
def compute {P Q : RatPolynomial}
    (hnonzero : P.isZero = false ∨ Q.isZero = false)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear : (commonFactor P Q).eval interval.lower ≠ 0)
    (upperClear : (commonFactor P Q).eval interval.upper ≠ 0)
    (countZero : commonFactorRootCount2 P Q hnonzero
      interval.lower interval.upper = 0) : Certificate P Q interval := by
  let g := commonFactor P Q
  let P₁ := reducedReal P Q
  let Q₁ := reducedImag P Q
  let coprime := reducedPairCertificate P Q hnonzero
  let commonLower := PositiveLowerBound.computeFromFactorCount
    (commonFactor_isZero_false hnonzero) interval proper lowerClear upperClear
    (by simpa [commonFactorRootCount2, g] using countZero)
  let M := bezoutNormMajorant coprime interval
  exact
    { bound := commonLower.bound / M
      positive := div_pos commonLower.positive
        (bezoutNormMajorant_pos coprime interval)
      lower := by
        intro t hLower hUpper
        let S := P₁.eval t ^ 2 + Q₁.eval t ^ 2
        have hS : 0 ≤ S := add_nonneg (sq_nonneg _) (sq_nonneg _)
        have hcoefficients :
            coprime.left.eval t ^ 2 + coprime.right.eval t ^ 2 ≤ M := by
          exact bezout_eval_sq_add_le_majorant coprime interval hLower hUpper
        have hbezout :
            coprime.left.eval t * P₁.eval t +
              coprime.right.eval t * Q₁.eval t = 1 :=
          coprime.identity t
        have hunit : 1 ≤ M * S := by
          have hsos : 1 ≤
              (coprime.left.eval t ^ 2 + coprime.right.eval t ^ 2) * S := by
            calc
              1 = (coprime.left.eval t * P₁.eval t +
                  coprime.right.eval t * Q₁.eval t) ^ 2 := by
                rw [hbezout]
                norm_num
              _ ≤ (coprime.left.eval t ^ 2 + coprime.right.eval t ^ 2) * S := by
                nlinarith [sq_nonneg
                  (coprime.left.eval t * Q₁.eval t -
                    coprime.right.eval t * P₁.eval t)]
          exact hsos.trans (mul_le_mul_of_nonneg_right hcoefficients hS)
        have hcommon := commonLower.lower t hLower hUpper
        have hPidentity : P.eval t = g.eval t * P₁.eval t := by
          simpa [g, P₁] using commonFactor_mul_reducedReal_eval P Q t
        have hQidentity : Q.eval t = g.eval t * Q₁.eval t := by
          simpa [g, Q₁] using commonFactor_mul_reducedImag_eval P Q t
        have hscaled : g.eval t ^ 2 ≤ M * (g.eval t ^ 2 * S) := by
          have h := mul_le_mul_of_nonneg_left hunit (sq_nonneg (g.eval t))
          nlinarith
        apply (div_le_iff₀ (bezoutNormMajorant_pos coprime interval)).2
        calc
          commonLower.bound ≤ g.eval t ^ 2 := hcommon
          _ ≤ M * (g.eval t ^ 2 * S) := hscaled
          _ = (P.eval t ^ 2 + Q.eval t ^ 2) * M := by
            rw [hPidentity, hQidentity]
            dsimp only [S]
            ring }

/-! ## Affine Gaussian-rational path specialization -/

def lineCommonFactor (p : GaussianPolynomial) (u d : QI) : RatPolynomial :=
  commonFactor (pathReal p u d) (pathImag p u d)

def lineCommonFactorRootCount2 (p : GaussianPolynomial) (u d : QI)
    (hnonzero : (pathReal p u d).isZero = false ∨
      (pathImag p u d).isZero = false) (a b : ℚ) : ℤ :=
  commonFactorRootCount2 (pathReal p u d) (pathImag p u d) hnonzero a b

def computeLine (p : GaussianPolynomial) (u d : QI)
    (hnonzero : (pathReal p u d).isZero = false ∨
      (pathImag p u d).isZero = false)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear : (lineCommonFactor p u d).eval interval.lower ≠ 0)
    (upperClear : (lineCommonFactor p u d).eval interval.upper ≠ 0)
    (countZero : lineCommonFactorRootCount2 p u d hnonzero
      interval.lower interval.upper = 0) :
    Certificate (pathReal p u d) (pathImag p u d) interval :=
  compute hnonzero interval proper lowerClear upperClear countZero

theorem computeLine_lower_normSq (p : GaussianPolynomial) (u d : QI)
    (hnonzero : (pathReal p u d).isZero = false ∨
      (pathImag p u d).isZero = false)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear : (lineCommonFactor p u d).eval interval.lower ≠ 0)
    (upperClear : (lineCommonFactor p u d).eval interval.upper ≠ 0)
    (countZero : lineCommonFactorRootCount2 p u d hnonzero
      interval.lower interval.upper = 0)
    {t : ℚ} (hLower : interval.lower ≤ t) (hUpper : t ≤ interval.upper) :
    (computeLine p u d hnonzero interval proper lowerClear upperClear
      countZero).bound ≤ normSq (p.eval (line u d t)) := by
  have h := (computeLine p u d hnonzero interval proper lowerClear upperClear
    countZero).lower t hLower hUpper
  simpa only [normSq, eval_pathReal, eval_pathImag] using h

private def clearReal : RatPolynomial := constant 1
private def clearImag : RatPolynomial := ⟨[1, 0]⟩

/-- A coordinate path `1 + it` is uniformly clear on `[-1,1]`. -/
theorem compute_clear_coordinate_example :
    let certificate := compute (P := clearReal) (Q := clearImag)
      (by native_decide) ⟨-1, 1⟩ (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)
    0 < certificate.bound ∧
      certificate.bound ≤ clearReal.eval 0 ^ 2 + clearImag.eval 0 ^ 2 := by
  dsimp only
  constructor
  · exact (compute (P := clearReal) (Q := clearImag)
      (by native_decide) ⟨-1, 1⟩ (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)).positive
  · exact (compute (P := clearReal) (Q := clearImag)
      (by native_decide) ⟨-1, 1⟩ (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)).lower 0
        (by norm_num) (by norm_num)

private def obstructedReal : RatPolynomial := ⟨[1, 0]⟩
private def obstructedImag : RatPolynomial := 0

/-- A path through the origin has a positive common-factor count and is
therefore rejected by the zero-count clearance branch. -/
theorem obstructed_coordinate_count_example :
    commonFactorRootCount2 obstructedReal obstructedImag (by native_decide)
      (-1) 1 = 2 := by
  native_decide

private def identityGaussianPolynomial : GaussianPolynomial :=
  ⟨[1, 0]⟩

private def oneBase : QI := GaussianRat.mk 1 0
private def imaginaryDirection : QI := GaussianRat.mk 0 1

/-- Full affine-path regression: the identity polynomial on `1 + it` remains
quantitatively clear for `-1 ≤ t ≤ 1`. -/
theorem computeLine_clear_example :
    let hnonzero :
        (pathReal identityGaussianPolynomial oneBase imaginaryDirection).isZero = false ∨
        (pathImag identityGaussianPolynomial oneBase imaginaryDirection).isZero = false :=
      by native_decide
    let certificate := computeLine identityGaussianPolynomial oneBase imaginaryDirection
      hnonzero ⟨-1, 1⟩ (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)
    0 < certificate.bound ∧
      certificate.bound ≤ normSq
        (identityGaussianPolynomial.eval (line oneBase imaginaryDirection 0)) := by
  dsimp only
  let hnonzero :
      (pathReal identityGaussianPolynomial oneBase imaginaryDirection).isZero = false ∨
      (pathImag identityGaussianPolynomial oneBase imaginaryDirection).isZero = false :=
    by native_decide
  constructor
  · exact (computeLine identityGaussianPolynomial oneBase imaginaryDirection
      hnonzero ⟨-1, 1⟩ (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)).positive
  · exact computeLine_lower_normSq identityGaussianPolynomial oneBase
      imaginaryDirection hnonzero ⟨-1, 1⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)
      (t := 0) (by norm_num) (by norm_num)

/-- The identity polynomial on the real line through zero is detected as an
obstructed affine path. -/
theorem obstructedLine_count_example :
    let hnonzero :
        (pathReal identityGaussianPolynomial 0 1).isZero = false ∨
        (pathImag identityGaussianPolynomial 0 1).isZero = false :=
      by native_decide
    lineCommonFactorRootCount2 identityGaussianPolynomial 0 1 hnonzero
      (-1) 1 = 2 := by
  native_decide

end FTA.PathClearance
