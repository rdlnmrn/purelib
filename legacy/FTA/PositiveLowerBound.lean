import FTA.SturmIsolation
import FTA.SquarefreeFactorization

/-!
# Finite positive polynomial lower bounds

This module packages the proof-bearing rational lower bounds used in Lemma
3.5.  A whole-cell sign certificate immediately supplies a positive squared
lower bound.  The complementary local case uses a whole-cell derivative sign
and the executable Taylor remainder to prove strict monotonicity, after which
the smaller endpoint magnitude is a lower bound.  Adjacent certificates
combine by taking a finite rational minimum.
-/

namespace FTA.PositiveLowerBound

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.DenseDerivative
open FTA.RationalPolynomialBounds
open FTA.Sturm
open FTA.SturmIsolation
open FTA.SturmTransducer
open FTA.SquarefreeFactorization

abbrev RatPolynomial := DensePolynomial ℚ

/-- A positive rational lower bound for the squared value of one polynomial
throughout a closed rational interval. -/
structure Certificate (p : RatPolynomial) (interval : RationalInterval) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ t : ℚ, interval.lower ≤ t → t ≤ interval.upper →
    bound ≤ p.eval t ^ 2

theorem Certificate.eval_ne_zero {p : RatPolynomial}
    {interval : RationalInterval} (certificate : Certificate p interval)
    {t : ℚ} (lower : interval.lower ≤ t) (upper : t ≤ interval.upper) :
    p.eval t ≠ 0 := by
  intro zero
  have bound := certificate.lower t lower upper
  rw [zero] at bound
  norm_num at bound
  linarith [certificate.positive]

/-- Restrict a positive lower bound to any displayed nested interval. -/
def Certificate.restrict {p : RatPolynomial} {root : RationalInterval}
    (certificate : Certificate p root) (interval : RationalInterval)
    (refines : interval.Refines root) : Certificate p interval where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro t lower upper
    exact certificate.lower t (refines.1.trans lower) (upper.trans refines.2)

/-- A positive rational cell width below which the ordinary midpoint
Lipschitz classifier must recover the fixed sign already implied by a
squared-value lower bound.  The `min 1` avoids a square-root operation. -/
def Certificate.signResolution {p : RatPolynomial}
    {root : RationalInterval} (certificate : Certificate p root) : ℚ :=
  min 1 certificate.bound /
    max 1 (denseEvalLipschitzBound p
      (intervalMagnitude root.lower root.upper))

theorem Certificate.signResolution_pos {p : RatPolynomial}
    {root : RationalInterval} (certificate : Certificate p root) :
    0 < certificate.signResolution := by
  apply div_pos
  · exact lt_min zero_lt_one certificate.positive
  · exact zero_lt_one.trans_le (le_max_left _ _)

/-- Every proper nested cell narrower than `signResolution` has a successful
midpoint sign certificate. -/
theorem Certificate.midpointResolved_of_width
    {p : RatPolynomial} {root interval : RationalInterval}
    (certificate : Certificate p root) (refines : interval.Refines root)
    (proper : interval.Proper)
    (width : interval.width < certificate.signResolution) :
    MidpointResolved interval p := by
  let rootMagnitude := intervalMagnitude root.lower root.upper
  let cellMagnitude := intervalMagnitude interval.lower interval.upper
  let slope := denseEvalLipschitzBound p cellMagnitude
  let slopeMajorant := max 1 (denseEvalLipschitzBound p rootMagnitude)
  let margin := min 1 certificate.bound
  let sample := midpoint interval.lower interval.upper
  have cellMagnitudeNonnegative : 0 ≤ cellMagnitude :=
    (intervalMagnitude_pos interval.lower interval.upper).le
  have magnitudeBound : cellMagnitude ≤ rootMagnitude :=
    interval.intervalMagnitude_le_of_refines refines proper
  have slopeBound : slope ≤ slopeMajorant := by
    exact ((denseHornerBounds_mono p cellMagnitudeNonnegative magnitudeBound).2).trans
      (le_max_right _ _)
  have slopeMajorantPositive : 0 < slopeMajorant :=
    zero_lt_one.trans_le (le_max_left _ _)
  have marginPositive : 0 < margin :=
    lt_min zero_lt_one certificate.positive
  have widthScaled : slopeMajorant * interval.width < margin := by
    have := (lt_div_iff₀ slopeMajorantPositive).mp
      (show interval.width < margin / slopeMajorant by
        simpa [Certificate.signResolution, margin, slopeMajorant,
          rootMagnitude] using width)
    simpa [mul_comm] using this
  have radiusNonnegative :
      0 ≤ intervalRadius interval.lower interval.upper sample := by
    dsimp [intervalRadius]
    positivity
  have radiusEquation :
      intervalRadius interval.lower interval.upper sample = interval.width / 2 := by
    simpa only [sample] using interval.midpointRadius_eq_half_width proper
  have slopeNonnegative : 0 ≤ slope :=
    (denseHornerBounds_nonneg p cellMagnitudeNonnegative).2
  have lossSmall :
      slope * intervalRadius interval.lower interval.upper sample < margin / 2 := by
    rw [radiusEquation]
    have intervalWidthNonnegative := (RationalInterval.width_pos proper).le
    have slopeScaled :=
      mul_le_mul_of_nonneg_right slopeBound intervalWidthNonnegative
    nlinarith
  have sampleLower : root.lower ≤ sample :=
    refines.1.trans (lower_lt_midpoint proper).le
  have sampleUpper : sample ≤ root.upper :=
    (midpoint_lt_upper proper).le.trans refines.2
  have sampleSquare := certificate.lower sample sampleLower sampleUpper
  have sampleAbsPositive : 0 < |p.eval sample| := by
    rw [abs_pos]
    intro sampleZero
    rw [sampleZero] at sampleSquare
    norm_num at sampleSquare
    linarith [certificate.positive]
  have halfMarginLtAbs : margin / 2 < |p.eval sample| := by
    by_cases oneLe : 1 ≤ |p.eval sample|
    · have marginLeOne : margin ≤ 1 := min_le_left _ _
      nlinarith
    · have sampleAbsLtOne : |p.eval sample| < 1 := lt_of_not_ge oneLe
      have marginLeBound : margin ≤ certificate.bound := min_le_right _ _
      have squareEquation : |p.eval sample| ^ 2 = p.eval sample ^ 2 := by
        rw [sq_abs]
      rw [← squareEquation] at sampleSquare
      have squareLtAbs : |p.eval sample| ^ 2 < |p.eval sample| := by
        nlinarith
      linarith
  change slope * intervalRadius interval.lower interval.upper sample <
    |p.eval sample|
  exact lossSmall.trans halfMarginLtAbs

/-- Proof-relevant form of the preceding termination bound. -/
def Certificate.midpointSignCertificateOfWidth
    {p : RatPolynomial} {root interval : RationalInterval}
    (certificate : Certificate p root) (refines : interval.Refines root)
    (proper : interval.Proper)
    (width : interval.width < certificate.signResolution) :
    IntervalSignCertificate p interval.lower interval.upper :=
  midpointResolvedCertificate interval proper p
    (certificate.midpointResolved_of_width refines proper width)

/-- Multiply two lower-bound certificates on the same interval. -/
def Certificate.mul {p q : RatPolynomial} {interval : RationalInterval}
    (left : Certificate p interval) (right : Certificate q interval) :
    Certificate (p * q) interval where
  bound := left.bound * right.bound
  positive := mul_pos left.positive right.positive
  lower := by
    intro t hLower hUpper
    have hleft := left.lower t hLower hUpper
    have hright := right.lower t hLower hUpper
    calc
      left.bound * right.bound ≤ p.eval t ^ 2 * q.eval t ^ 2 :=
        mul_le_mul hleft hright right.positive.le (sq_nonneg _)
      _ = (p * q).eval t ^ 2 := by rw [eval_mul]; ring

/-- Transport a product certificate through an exact nonzero scalar
evaluation identity. -/
def Certificate.ofScalarProduct {p q : RatPolynomial}
    {interval : RationalInterval} (scalar : ℚ) (scalarNe : scalar ≠ 0)
    (certificate : Certificate q interval)
    (identity : ∀ x, p.eval x = scalar * q.eval x) : Certificate p interval where
  bound := scalar ^ 2 * certificate.bound
  positive := mul_pos (sq_pos_of_ne_zero scalarNe) certificate.positive
  lower := by
    intro t hLower hUpper
    calc
      scalar ^ 2 * certificate.bound ≤ scalar ^ 2 * q.eval t ^ 2 :=
        mul_le_mul_of_nonneg_left (certificate.lower t hLower hUpper)
          (sq_nonneg scalar)
      _ = p.eval t ^ 2 := by rw [identity]; ring

/-- Exact certificate for a represented nonzero constant polynomial. -/
def Certificate.ofConstant {p : RatPolynomial} (hp : p.isZero = false)
    (hdegree : p.natDegree = 0) (interval : RationalInterval) :
    Certificate p interval where
  bound := p.leadingCoeff ^ 2
  positive := sq_pos_of_ne_zero (leadingCoeff_ne_zero hp)
  lower := by
    intro t _ _
    rw [FTA.DenseSquarefree.eval_eq_leadingCoeff_of_natDegree_eq_zero
      hp hdegree t]

/-- A whole-cell sign certificate gives the square of its explicit absolute
margin as a positive lower bound. -/
def Certificate.ofIntervalSign {p : RatPolynomial} {interval : RationalInterval}
    (sign : IntervalSignCertificate p interval.lower interval.upper) :
    Certificate p interval where
  bound := sign.absMargin ^ 2
  positive := sq_pos_of_pos sign.absMargin_pos
  lower := by
    intro t hLower hUpper
    exact sign.absMargin_sq_le_eval_sq hLower hUpper

/-- Combine adjacent lower-bound certificates by taking their finite minimum. -/
def Certificate.combine {p : RatPolynomial} {a cut b : ℚ}
    (left : Certificate p ⟨a, cut⟩) (right : Certificate p ⟨cut, b⟩) :
    Certificate p ⟨a, b⟩ where
  bound := min left.bound right.bound
  positive := lt_min left.positive right.positive
  lower := by
    intro t hat htb
    by_cases hcut : t ≤ cut
    · exact (min_le_left _ _).trans (left.lower t hat hcut)
    · have hct : cut ≤ t := (lt_of_not_ge hcut).le
      exact (min_le_right _ _).trans (right.lower t hct htb)

/-- Local data proving that `p` is strictly monotone on the cell without
invoking a completed real derivative theorem.  The Taylor remainder per unit
width is smaller than the derivative's certified absolute margin. -/
structure DerivativeMonotoneCertificate (p : RatPolynomial)
    (interval : RationalInterval) where
  proper : interval.Proper
  derivativeSign : IntervalSignCertificate (derivative p)
    interval.lower interval.upper
  taylorSmall : denseTaylorHornerRemainderBound p
      (intervalMagnitude interval.lower interval.upper) * interval.width <
    derivativeSign.absMargin

namespace DerivativeMonotoneCertificate

/-- Exact rational Taylor arithmetic gives the difference `p(v)-p(u)` the
same strict sign as the fixed derivative sample whenever `u<v` in the cell. -/
theorem eval_sub_mul_sampleDerivative_pos {p : RatPolynomial}
    {interval : RationalInterval}
    (certificate : DerivativeMonotoneCertificate p interval)
    {u v : ℚ} (hLower : interval.lower ≤ u) (huv : u < v)
    (hUpper : v ≤ interval.upper) :
    0 < (p.eval v - p.eval u) *
      (derivative p).eval certificate.derivativeSign.sample := by
  let B := intervalMagnitude interval.lower interval.upper
  let remainder := denseTaylorHornerRemainderBound p B
  let distance := v - u
  let slopeU := (derivative p).eval u
  let difference := p.eval v - p.eval u
  have hB : 0 ≤ B := (intervalMagnitude_pos _ _).le
  have huB : |u| ≤ B :=
    abs_le_intervalMagnitude hLower (huv.le.trans hUpper)
  have hvB : |v| ≤ B :=
    abs_le_intervalMagnitude (hLower.trans huv.le) hUpper
  have hdistance : 0 < distance := sub_pos.mpr huv
  have hdistanceWidth : distance ≤ interval.width := by
    dsimp only [distance, RationalInterval.width]
    linarith
  have hremainder : 0 ≤ remainder :=
    (denseTaylorHornerBounds_nonneg p hB).2.2
  have hslopeLower : certificate.derivativeSign.absMargin ≤ |slopeU| := by
    exact certificate.derivativeSign.absMargin_le_abs_eval hLower
      (huv.le.trans hUpper)
  have hremainderDistance : remainder * distance < |slopeU| := by
    exact (mul_le_mul_of_nonneg_left hdistanceWidth hremainder).trans_lt
      (certificate.taylorSmall.trans_le hslopeLower)
  have herror := abs_dense_taylor_sub_le_horner p hB hvB huB
  have herrorStrict :
      |difference - slopeU * distance| < |slopeU * distance| := by
    calc
      |difference - slopeU * distance| ≤ remainder * |v - u| ^ 2 := by
        simpa only [difference, slopeU, distance] using herror
      _ = (remainder * distance) * distance := by
        rw [abs_of_pos hdistance]
        ring
      _ < |slopeU| * distance :=
        mul_lt_mul_of_pos_right hremainderDistance hdistance
      _ = |slopeU * distance| := by
        rw [abs_mul, abs_of_pos hdistance]
  have hlinearDifference : 0 < (slopeU * distance) * difference := by
    apply mul_pos_of_abs_sub_lt_abs_left
    simpa [abs_sub_comm] using herrorStrict
  have hslopeDifference : 0 < slopeU * difference := by
    have : 0 < distance * (slopeU * difference) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hlinearDifference
    exact (mul_pos_iff_of_pos_left hdistance).mp this
  have hslopeSample : 0 < slopeU *
      (derivative p).eval certificate.derivativeSign.sample := by
    simpa [slopeU, mul_comm] using
      certificate.derivativeSign.eval_mul_pos hLower (huv.le.trans hUpper)
  have htransfer := mul_pos_of_mul_pos_left hslopeDifference hslopeSample
  simpa [difference, mul_comm] using htransfer

/-- The polynomial value at any cell point lies between its two endpoint
values, with the order determined by the certified derivative sign. -/
theorem eval_between_endpoints {p : RatPolynomial}
    {interval : RationalInterval}
    (certificate : DerivativeMonotoneCertificate p interval)
    {t : ℚ} (hLower : interval.lower ≤ t) (hUpper : t ≤ interval.upper) :
    (p.eval interval.lower ≤ p.eval t ∧
        p.eval t ≤ p.eval interval.upper) ∨
      (p.eval t ≤ p.eval interval.lower ∧
        p.eval interval.upper ≤ p.eval t) := by
  let sampleSlope :=
    (derivative p).eval certificate.derivativeSign.sample
  have hsampleNe : sampleSlope ≠ 0 := by
    exact certificate.derivativeSign.eval_ne_zero
      certificate.derivativeSign.lowerLe certificate.derivativeSign.leUpper
  have hleft : t = interval.lower ∨
      0 < (p.eval t - p.eval interval.lower) * sampleSlope := by
    rcases eq_or_lt_of_le hLower with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr (certificate.eval_sub_mul_sampleDerivative_pos le_rfl hlt hUpper)
  have hright : t = interval.upper ∨
      0 < (p.eval interval.upper - p.eval t) * sampleSlope := by
    rcases eq_or_lt_of_le hUpper with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr
        (certificate.eval_sub_mul_sampleDerivative_pos hLower hlt le_rfl)
  rcases lt_or_gt_of_ne hsampleNe with hslopeNeg | hslopePos
  · right
    constructor
    · rcases hleft with rfl | hleft
      · exact le_rfl
      · nlinarith
    · rcases hright with rfl | hright
      · exact le_rfl
      · nlinarith
  · left
    constructor
    · rcases hleft with rfl | hleft
      · exact le_rfl
      · nlinarith
    · rcases hright with rfl | hright
      · exact le_rfl
      · nlinarith

/-- On a monotone cell whose endpoints have the same strict sign, the smaller
endpoint magnitude is a positive absolute-value lower bound. -/
theorem min_endpoint_abs_le_abs_eval {p : RatPolynomial}
    {interval : RationalInterval}
    (certificate : DerivativeMonotoneCertificate p interval)
    (endpointsSame : 0 < p.eval interval.lower * p.eval interval.upper)
    {t : ℚ} (hLower : interval.lower ≤ t) (hUpper : t ≤ interval.upper) :
    min |p.eval interval.lower| |p.eval interval.upper| ≤ |p.eval t| := by
  rcases mul_pos_iff.mp endpointsSame with endpointsPos | endpointsNeg
  · rw [abs_of_pos endpointsPos.1, abs_of_pos endpointsPos.2]
    rcases certificate.eval_between_endpoints hLower hUpper with increasing | decreasing
    · have htPos : 0 < p.eval t := endpointsPos.1.trans_le increasing.1
      rw [abs_of_pos htPos]
      exact (min_le_left _ _).trans increasing.1
    · have htPos : 0 < p.eval t := endpointsPos.2.trans_le decreasing.2
      rw [abs_of_pos htPos]
      exact (min_le_right _ _).trans decreasing.2
  · rw [abs_of_neg endpointsNeg.1, abs_of_neg endpointsNeg.2]
    rcases certificate.eval_between_endpoints hLower hUpper with increasing | decreasing
    · have htNeg : p.eval t < 0 := increasing.2.trans_lt endpointsNeg.2
      rw [abs_of_neg htNeg]
      have := increasing.2
      exact (min_le_right _ _).trans (by linarith)
    · have htNeg : p.eval t < 0 := decreasing.1.trans_lt endpointsNeg.1
      rw [abs_of_neg htNeg]
      have := decreasing.1
      exact (min_le_left _ _).trans (by linarith)

/-- Endpoint magnitudes therefore construct a squared positive lower-bound
certificate on a derivative-monotone, zero-free-sign cell. -/
def toPositiveLowerBound {p : RatPolynomial} {interval : RationalInterval}
    (certificate : DerivativeMonotoneCertificate p interval)
    (endpointsSame : 0 < p.eval interval.lower * p.eval interval.upper) :
    Certificate p interval where
  bound := (min |p.eval interval.lower| |p.eval interval.upper|) ^ 2
  positive := by
    apply sq_pos_of_pos
    exact lt_min (abs_pos.mpr (mul_ne_zero_iff.mp endpointsSame.ne').1)
      (abs_pos.mpr (mul_ne_zero_iff.mp endpointsSame.ne').2)
  lower := by
    intro t hLower hUpper
    have hlower := certificate.min_endpoint_abs_le_abs_eval endpointsSame
      hLower hUpper
    have hnonneg : 0 ≤ min |p.eval interval.lower| |p.eval interval.upper| :=
      le_min (abs_nonneg _) (abs_nonneg _)
    have hsquare := pow_le_pow_left₀ hnonneg hlower 2
    simpa [sq_abs] using hsquare

end DerivativeMonotoneCertificate

/-! ## Uniform local squarefree construction -/

/-- Root-ambient width below which a zero-count cell either resolves `p`
directly or resolves its derivative strongly enough for the monotone endpoint
constructor. -/
def widthResolution {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval) : ℚ :=
  let B := intervalMagnitude root.lower root.upper
  let exclusion := coprimeExclusionMargin input.squarefree B
  let derivativeMajorant := max 1 (denseEvalLipschitzBound (derivative p) B)
  let remainderMajorant := max 1 (denseTaylorHornerRemainderBound p B)
  min (ambientEventClassifierWidthResolution input root)
    (min (exclusion / (2 * derivativeMajorant))
      (exclusion / (2 * remainderMajorant)))

theorem widthResolution_pos {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval) : 0 < widthResolution input root := by
  let B := intervalMagnitude root.lower root.upper
  let exclusion := coprimeExclusionMargin input.squarefree B
  let derivativeMajorant := max 1 (denseEvalLipschitzBound (derivative p) B)
  let remainderMajorant := max 1 (denseTaylorHornerRemainderBound p B)
  have hB : 0 ≤ B := (intervalMagnitude_pos _ _).le
  have hexclusion : 0 < exclusion :=
    coprimeExclusionMargin_pos input.squarefree hB
  have hderivative : 0 < derivativeMajorant :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hremainder : 0 < remainderMajorant :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply lt_min
  · exact ambientEventClassifierWidthResolution_pos input root
  · apply lt_min
    · exact div_pos hexclusion (mul_pos (by norm_num) hderivative)
    · exact div_pos hexclusion (mul_pos (by norm_num) hremainder)

/-- Every nested proper cell below the local width inherits the squarefree
Bézout radius used to select between the polynomial and derivative margins. -/
theorem coprimeRadius_of_widthResolution {p : RatPolynomial}
    (input : SquarefreeInput p) (root interval : RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width < widthResolution input root) :
    intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
      coprimeCellRadius input.squarefree interval.lower interval.upper := by
  have hclassifier : interval.width <
      ambientEventClassifierWidthResolution input root :=
    hwidth.trans_le (by
      dsimp only [widthResolution]
      exact min_le_left _ _)
  have hfirst : interval.width <
      ambientFirstMemberWidthResolution input root :=
    hclassifier.trans_le (by
      dsimp only [ambientEventClassifierWidthResolution]
      exact min_le_left _ _)
  let rootB := intervalMagnitude root.lower root.upper
  have hmagnitude : intervalMagnitude interval.lower interval.upper ≤ rootB :=
    interval.intervalMagnitude_le_of_refines hrefines proper
  have hambientWidth : interval.width <
      2 * ambientCoprimeCellRadius input.squarefree rootB :=
    hfirst.trans_le (by
      dsimp only [ambientFirstMemberWidthResolution, rootB]
      exact min_le_left _ _)
  rw [interval.midpointRadius_eq_half_width proper]
  apply (show interval.width / 2 <
      ambientCoprimeCellRadius input.squarefree rootB by linarith).trans_le
  exact ambientCoprimeCellRadius_le_cellRadius input.squarefree hmagnitude

/-- A zero-count cell below the uniform width has an explicit positive
squared lower bound.  The proof follows the executable midpoint dichotomy;
the crossing alternative is ruled out by constructing the full first-chain
event certificate and contradicting the displayed zero count. -/
def ofSmallZeroCountCell {p : RatPolynomial} (input : SquarefreeInput p)
    (root interval : RationalInterval) (hrefines : interval.Refines root)
    (proper : interval.Proper)
    (lowerClear : p.eval interval.lower ≠ 0)
    (upperClear : p.eval interval.upper ≠ 0)
    (countZero : sturmRootCount2 p interval.lower interval.upper = 0)
    (hwidth : interval.width < widthResolution input root) :
    Certificate p interval := by
  by_cases pResolved : MidpointResolved interval p
  · exact Certificate.ofIntervalSign
      (midpointResolvedCertificate interval proper p pResolved)
  · let rootB := intervalMagnitude root.lower root.upper
    let subB := intervalMagnitude interval.lower interval.upper
    let exclusion := coprimeExclusionMargin input.squarefree rootB
    let derivativeMajorant :=
      max 1 (denseEvalLipschitzBound (derivative p) rootB)
    let remainderMajorant :=
      max 1 (denseTaylorHornerRemainderBound p rootB)
    have hmagnitude : subB ≤ rootB :=
      interval.intervalMagnitude_le_of_refines hrefines proper
    have hsubB : 0 ≤ subB := (intervalMagnitude_pos _ _).le
    have hrootB : 0 ≤ rootB := hsubB.trans hmagnitude
    have hexclusionPos : 0 < exclusion :=
      coprimeExclusionMargin_pos input.squarefree hrootB
    have hcoprimeRadius := coprimeRadius_of_widthResolution input root interval
      hrefines proper hwidth
    have derivativeResolved : MidpointResolved interval (derivative p) :=
      secondMidpointMarginOfFirstUnresolved input.squarefree proper
        hcoprimeRadius (by simpa [MidpointResolved] using pResolved)
    let derivativeSign := midpointResolvedCertificate interval proper
      (derivative p) derivativeResolved
    have hclassifier : interval.width <
        ambientEventClassifierWidthResolution input root :=
      hwidth.trans_le (by
        dsimp only [widthResolution]
        exact min_le_left _ _)
    have hderivativeWidth : interval.width <
        exclusion / (2 * derivativeMajorant) :=
      hwidth.trans_le (by
        dsimp only [widthResolution, rootB, exclusion, derivativeMajorant,
          remainderMajorant]
        exact (min_le_right _ _).trans (min_le_left _ _))
    have hremainderWidth : interval.width <
        exclusion / (2 * remainderMajorant) :=
      hwidth.trans_le (by
        dsimp only [widthResolution, rootB, exclusion, derivativeMajorant,
          remainderMajorant]
        exact (min_le_right _ _).trans (min_le_right _ _))
    have hderivativeMajorant : 0 < derivativeMajorant :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hremainderMajorant : 0 < remainderMajorant :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hderivativeScaled :
        derivativeMajorant * interval.width < exclusion / 2 := by
      have h := (lt_div_iff₀ (mul_pos (by norm_num) hderivativeMajorant)).mp
        hderivativeWidth
      nlinarith
    have hremainderScaled :
        remainderMajorant * interval.width < exclusion / 2 := by
      have h := (lt_div_iff₀ (mul_pos (by norm_num) hremainderMajorant)).mp
        hremainderWidth
      nlinarith
    have hderivativeSlope : denseEvalLipschitzBound (derivative p) subB ≤
        derivativeMajorant := by
      exact ((denseHornerBounds_mono (derivative p) hsubB hmagnitude).2).trans
        (le_max_right _ _)
    have hremainderBound : denseTaylorHornerRemainderBound p subB ≤
        remainderMajorant := by
      exact (denseTaylorHornerRemainderBound_mono p hsubB hmagnitude).trans
        (le_max_right _ _)
    have hradius : intervalRadius interval.lower interval.upper
        (midpoint interval.lower interval.upper) = interval.width / 2 :=
      interval.midpointRadius_eq_half_width proper
    have hpointExclusion : exclusion ≤
        |(derivative p).eval (midpoint interval.lower interval.upper)| := by
      apply (coprimeExclusionMargin_anti input.squarefree hsubB hmagnitude).trans
      exact coprimeExclusionMargin_le_abs_second_midpoint_of_first_unresolved
        input.squarefree proper hcoprimeRadius
          (by simpa [MidpointResolved] using pResolved)
    have hderivativeLoss :
        denseEvalLipschitzBound (derivative p) subB *
            intervalRadius interval.lower interval.upper
              (midpoint interval.lower interval.upper) < exclusion / 4 := by
      rw [hradius]
      have hwidthNonneg := (RationalInterval.width_pos proper).le
      have := mul_le_mul_of_nonneg_right hderivativeSlope hwidthNonneg
      nlinarith
    have htaylorPerWidth :
        denseTaylorHornerRemainderBound p subB * interval.width < exclusion / 2 := by
      have hwidthNonneg := (RationalInterval.width_pos proper).le
      exact (mul_le_mul_of_nonneg_right hremainderBound hwidthNonneg).trans_lt
        hremainderScaled
    have htaylorSmall : denseTaylorHornerRemainderBound p subB * interval.width <
        derivativeSign.absMargin := by
      change denseTaylorHornerRemainderBound p subB * interval.width <
        |(derivative p).eval (midpoint interval.lower interval.upper)| -
          denseEvalLipschitzBound (derivative p) subB *
            intervalRadius interval.lower interval.upper
              (midpoint interval.lower interval.upper)
      nlinarith
    let monotone : DerivativeMonotoneCertificate p interval :=
      { proper
        derivativeSign
        taylorSmall := by simpa only [subB] using htaylorSmall }
    have endpointsSame : 0 < p.eval interval.lower * p.eval interval.upper := by
      by_contra hnotPositive
      have productNonzero : p.eval interval.lower * p.eval interval.upper ≠ 0 :=
        mul_ne_zero lowerClear upperClear
      have crossing : p.eval interval.lower * p.eval interval.upper < 0 :=
        lt_of_le_of_ne (le_of_not_gt hnotPositive) productNonzero
      let denominator := reducedDenominator (derivative p) p
      let numerator := reducedNumerator (derivative p) p
      let reducedCoprime := derivativeReducedPairCertificate input
      have hrawCoprime :
          IsCoprime (derivative p).toPolynomial p.toPolynomial := by
        simpa [toPolynomial_derivative] using
          input.squarefree.isCoprimeDerivative.symm
      have denominatorCrossing : denominator.eval interval.lower *
          denominator.eval interval.upper < 0 := by
        exact FTA.DenseGCD.symmetricRightFactor_endpoint_mul_neg_of_isCoprime
          (p := derivative p) (q := p) input.nonzero hrawCoprime crossing
      have denominatorUnresolved : ¬MidpointResolved interval denominator := by
        intro resolved
        have hsame := (midpointResolvedCertificate interval proper denominator
          resolved).eval_mul_pos_between le_rfl proper.le proper.le le_rfl
        linarith
      have hchainWidth : interval.width <
          2 * signedChainAmbientRadius denominator numerator reducedCoprime rootB :=
        hclassifier.trans_le (by
          dsimp only [ambientEventClassifierWidthResolution, denominator,
            numerator, reducedCoprime, rootB]
          exact min_le_right _ _)
      have hchainRadius : intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
          signedChainAmbientRadius denominator numerator reducedCoprime rootB := by
        rw [interval.midpointRadius_eq_half_width proper]
        linarith
      have chainBounds : NeutralChainResolutionBounds interval denominator
          (signedRemainderChain denominator numerator).tail :=
        signedChainResolutionBoundsOfAmbient root interval hrefines proper
          denominator numerator reducedCoprime hchainRadius
      have restResult :=
        derivativeRestChainCertificates?_succeeds_of_resolutionBounds input
          interval proper chainBounds denominatorUnresolved
      have hfirstWidth : interval.width <
          ambientFirstMemberWidthResolution input root :=
        hclassifier.trans_le (by
          dsimp only [ambientEventClassifierWidthResolution]
          exact min_le_left _ _)
      have firstInequalities := firstMember_inequalities_of_refined_width input
        root interval hrefines proper crossing hfirstWidth
      let first := firstMemberCellCertificateOfSmallCrossing input interval
        proper crossing firstInequalities.1 firstInequalities.2
      let firstChain : FirstChainEventCertificate input interval :=
        { first, restStable := restResult.1 }
      have htwo := firstChain.count_eq_two
      linarith
    exact monotone.toPositiveLowerBound endpointsSame

/-! ## Finite global zero-count construction -/

/-- Explicit central-third depth making every terminal cell narrower than the
positive-lower-bound resolution. -/
def resolutionDepth {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval) : ℕ :=
  geometricDepth root.width (widthResolution input root / 2)

theorem resolutionDepth_sufficient {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval)
    (proper : root.Proper) :
    (2 / 3 : ℚ) ^ resolutionDepth input root * root.width <
      widthResolution input root := by
  have hhalf : 0 < widthResolution input root / 2 := by
    linarith [widthResolution_pos input root]
  have hgeometric := geometricDepth_sufficient
    (RationalInterval.width_pos proper).le hhalf
  calc
    (2 / 3 : ℚ) ^ resolutionDepth input root * root.width ≤
        widthResolution input root / 2 := by
      simpa [resolutionDepth] using hgeometric
    _ < widthResolution input root := by
      linarith [widthResolution_pos input root]

/-- Fixed-depth finite subdivision for a displayed zero-count interval.  Each
recursive split has two zero-count children by additivity and the already
computed nonnegativity law; terminal cells use `ofSmallZeroCountCell`, and
adjacent bounds combine by rational minimum. -/
def build {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval) :
    (fuel : ℕ) → (interval : RationalInterval) → interval.Refines root →
      (proper : interval.Proper) →
      p.eval interval.lower ≠ 0 → p.eval interval.upper ≠ 0 →
      sturmRootCount2 p interval.lower interval.upper = 0 →
      (2 / 3 : ℚ) ^ fuel * interval.width < widthResolution input root →
      Certificate p interval
  | 0, interval, hrefines, proper, lowerClear, upperClear, countZero,
      sufficient =>
      ofSmallZeroCountCell input root interval hrefines proper lowerClear
        upperClear countZero (by simpa using sufficient)
  | fuel + 1, interval, hrefines, proper, lowerClear, upperClear, countZero,
      sufficient => by
      let cut := guardedIntervalCut input interval proper
      let leftInterval := interval.left cut.point
      let rightInterval := interval.right cut.point
      have hleftNonnegative :
          0 ≤ sturmRootCount2 p interval.lower cut.point :=
        (computedEventPartitionProgram input).nonnegativeLaw cut.lowerLt
          lowerClear cut.clear
      have hrightNonnegative :
          0 ≤ sturmRootCount2 p cut.point interval.upper :=
        (computedEventPartitionProgram input).nonnegativeLaw cut.ltUpper
          cut.clear upperClear
      have hsum := sturmRootCount2_add p interval.lower cut.point interval.upper
      have hleftZero : sturmRootCount2 p interval.lower cut.point = 0 := by
        omega
      have hrightZero : sturmRootCount2 p cut.point interval.upper = 0 := by
        omega
      have hfactor : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
      have hleftWidth : leftInterval.width <
          (2 / 3 : ℚ) * interval.width := by
        simpa [cut, leftInterval] using
          guardedIntervalCut_left_width_lt input interval proper
      have hrightWidth : rightInterval.width <
          (2 / 3 : ℚ) * interval.width := by
        simpa [cut, rightInterval] using
          guardedIntervalCut_right_width_lt input interval proper
      have hleftSufficient : (2 / 3 : ℚ) ^ fuel * leftInterval.width <
          widthResolution input root := by
        calc
          (2 / 3 : ℚ) ^ fuel * leftInterval.width <
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_lt_mul_of_pos_left hleftWidth hfactor
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ < widthResolution input root := sufficient
      have hrightSufficient : (2 / 3 : ℚ) ^ fuel * rightInterval.width <
          widthResolution input root := by
        calc
          (2 / 3 : ℚ) ^ fuel * rightInterval.width <
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_lt_mul_of_pos_left hrightWidth hfactor
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ < widthResolution input root := sufficient
      have hleftRefines : leftInterval.Refines root :=
        RationalInterval.refines_trans
          (by simpa [cut, leftInterval] using
            guardedIntervalCut_left_refines input interval proper)
          hrefines
      have hrightRefines : rightInterval.Refines root :=
        RationalInterval.refines_trans
          (by simpa [cut, rightInterval] using
            guardedIntervalCut_right_refines input interval proper)
          hrefines
      have hleftZero' : sturmRootCount2 p leftInterval.lower
          leftInterval.upper = 0 := by
        simpa [leftInterval, RationalInterval.left] using hleftZero
      have hrightZero' : sturmRootCount2 p rightInterval.lower
          rightInterval.upper = 0 := by
        simpa [rightInterval, RationalInterval.right] using hrightZero
      have leftCertificate := build input root fuel leftInterval hleftRefines
        cut.lowerLt lowerClear cut.clear hleftZero' hleftSufficient
      have rightCertificate := build input root fuel rightInterval hrightRefines
        cut.ltUpper cut.clear upperClear hrightZero' hrightSufficient
      simpa [leftInterval, rightInterval, cut, RationalInterval.left,
        RationalInterval.right] using
        Certificate.combine leftCertificate rightCertificate

/-- Lemma 3.5 for a squarefree dense rational polynomial: from exact clear
endpoints and a displayed zero Sturm count, compute a positive rational whose
square lower-bounds every rational evaluation on the interval. -/
def compute {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval) (proper : root.Proper)
    (lowerClear : p.eval root.lower ≠ 0)
    (upperClear : p.eval root.upper ≠ 0)
    (countZero : sturmRootCount2 p root.lower root.upper = 0) :
    Certificate p root :=
  build input root (resolutionDepth input root) root
    (RationalInterval.refines_refl root) proper lowerClear upperClear countZero
    (resolutionDepth_sufficient input root proper)

/-! ## Rational-zero coverage of finite isolation -/

/-- A zero-count squarefree interval contains no exact rational zero.  This is
the pointwise consequence of the constructive positive lower bound, not an
appeal to a completed real root set. -/
theorem eval_ne_zero_of_sturmRootCount2_eq_zero
    {p : RatPolynomial} (input : SquarefreeInput p)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear : p.eval interval.lower ≠ 0)
    (upperClear : p.eval interval.upper ≠ 0)
    (countZero : sturmRootCount2 p interval.lower interval.upper = 0)
    {t : ℚ} (lower : interval.lower ≤ t) (upper : t ≤ interval.upper) :
    p.eval t ≠ 0 := by
  let certificate := compute input interval proper lowerClear upperClear countZero
  intro eventZero
  have bound := certificate.lower t lower upper
  rw [eventZero] at bound
  nlinarith [certificate.positive]

/-- A count-one subinterval retains every exact rational zero of a count-one
parent that it refines.  The two discarded side intervals have nonnegative
counts whose sum is zero, so their computed positive lower bounds exclude the
zero. -/
theorem CountOneInterval.rationalZero_mem_of_refines
    {p : RatPolynomial} (input : SquarefreeInput p)
    (parent child : CountOneInterval p)
    (refines : child.interval.Refines parent.interval)
    {t : ℚ} (lower : parent.interval.lower ≤ t)
    (upper : t ≤ parent.interval.upper) (eventZero : p.eval t = 0) :
    child.interval.lower ≤ t ∧ t ≤ child.interval.upper := by
  have nonnegative : SturmNonnegativeLaw input :=
    (computedEventPartitionProgram input).nonnegativeLaw
  have leftNonnegative :
      0 ≤ sturmRootCount2 p parent.interval.lower child.interval.lower := by
    rcases refines.1.eq_or_lt with equality | proper
    · simp [equality]
    · exact nonnegative proper parent.lowerClear child.lowerClear
  have rightNonnegative :
      0 ≤ sturmRootCount2 p child.interval.upper parent.interval.upper := by
    rcases refines.2.eq_or_lt with equality | proper
    · simp [equality]
    · exact nonnegative proper child.upperClear parent.upperClear
  have total :
      sturmRootCount2 p parent.interval.lower child.interval.lower +
          sturmRootCount2 p child.interval.lower child.interval.upper +
          sturmRootCount2 p child.interval.upper parent.interval.upper =
        sturmRootCount2 p parent.interval.lower parent.interval.upper := by
    rw [add_assoc, sturmRootCount2_add, sturmRootCount2_add]
  have leftZero :
      sturmRootCount2 p parent.interval.lower child.interval.lower = 0 := by
    rw [parent.countOne, child.countOne] at total
    omega
  have rightZero :
      sturmRootCount2 p child.interval.upper parent.interval.upper = 0 := by
    rw [parent.countOne, child.countOne] at total
    omega
  constructor
  · by_contra notLower
    have before : t < child.interval.lower := lt_of_not_ge notLower
    exact (eval_ne_zero_of_sturmRootCount2_eq_zero input
      ⟨parent.interval.lower, child.interval.lower⟩
      (lower.trans_lt before) parent.lowerClear child.lowerClear leftZero
      lower before.le) eventZero
  · by_contra notUpper
    have after : child.interval.upper < t := lt_of_not_ge notUpper
    exact (eval_ne_zero_of_sturmRootCount2_eq_zero input
      ⟨child.interval.upper, parent.interval.upper⟩
      (after.trans_le upper) child.upperClear parent.upperClear rightZero
      after.le upper) eventZero

/-- Every exact rational zero in a partition root lies in one of its returned
first-member transducers.  Interior leaves are excluded by the preceding
computed positive lower bound. -/
theorem EventPartition.rationalZero_mem_zeroTransducers
    {p : RatPolynomial} (input : SquarefreeInput p)
    {interval : RationalInterval} (partition : EventPartition p interval)
    {t : ℚ} (lower : interval.lower ≤ t) (upper : t ≤ interval.upper)
    (eventZero : p.eval t = 0) :
    ∃ child ∈ zeroTransducers interval partition,
      child.interval.lower ≤ t ∧ t ≤ child.interval.upper := by
  induction partition generalizing t with
  | @leaf leafInterval proper lowerClear upperClear kind countCertificate =>
      cases kind with
      | interior =>
          have countZero :
              sturmRootCount2 p leafInterval.lower leafInterval.upper = 0 :=
            by simpa [EventKind.contribution2] using countCertificate
          exact (eval_ne_zero_of_sturmRootCount2_eq_zero input leafInterval proper
            lowerClear upperClear countZero lower upper eventZero).elim
      | firstMember =>
          simp [zeroTransducers, lower, upper]
  | @split parent cut lowerLt ltUpper cutClear left right leftIH rightIH =>
      have notCut : t ≠ cut := by
        intro equality
        apply cutClear
        simpa [equality] using eventZero
      rcases lt_or_gt_of_ne notCut with before | after
      · rcases leftIH lower before.le eventZero with
          ⟨child, member, childLower, childUpper⟩
        exact ⟨child, by
          simp only [zeroTransducers, List.mem_append]
          exact Or.inl member, childLower, childUpper⟩
      · rcases rightIH after.le upper eventZero with
          ⟨child, member, childLower, childUpper⟩
        exact ⟨child, by
          simp only [zeroTransducers, List.mem_append]
          exact Or.inr member, childLower, childUpper⟩

/-- Proof-bearing isolation therefore covers every exact rational zero in its
input interval by one returned count-one transducer. -/
theorem IsolationResult.rationalZero_mem
    {p : RatPolynomial} (input : SquarefreeInput p)
    {root : RationalInterval} (result : IsolationResult p root)
    {t : ℚ} (lower : root.lower ≤ t) (upper : t ≤ root.upper)
    (eventZero : p.eval t = 0) :
    ∃ child ∈ result.transducers,
      child.interval.lower ≤ t ∧ t ≤ child.interval.upper := by
  rw [result.extracted]
  exact FTA.PositiveLowerBound.EventPartition.rationalZero_mem_zeroTransducers
    input result.partition lower upper eventZero

/-! ## Arbitrary-factor construction -/

/-- Multiply the independently computed bounds for a finite list of
squarefree factors. -/
def computeFactorProduct : (factors : List Factor) →
    (interval : RationalInterval) → interval.Proper →
    (factorProduct factors).eval interval.lower ≠ 0 →
    (factorProduct factors).eval interval.upper ≠ 0 →
    (∀ factor ∈ factors,
      sturmRootCount2 factor.polynomial interval.lower interval.upper = 0) →
    Certificate (factorProduct factors) interval
  | [], interval, _, _, _, _ =>
      { bound := 1
        positive := by norm_num
        lower := by
          intro t _ _
          norm_num [factorProduct, eval_constant] }
  | factor :: factors, interval, proper, lowerClear, upperClear, countsZero => by
      have hfactorLower : factor.polynomial.eval interval.lower ≠ 0 := by
        intro hzero
        apply lowerClear
        simp [factorProduct, hzero]
      have hfactorUpper : factor.polynomial.eval interval.upper ≠ 0 := by
        intro hzero
        apply upperClear
        simp [factorProduct, hzero]
      have htailLower : (factorProduct factors).eval interval.lower ≠ 0 := by
        intro hzero
        apply lowerClear
        simp [factorProduct, hzero]
      have htailUpper : (factorProduct factors).eval interval.upper ≠ 0 := by
        intro hzero
        apply upperClear
        simp [factorProduct, hzero]
      have hfactorZero := countsZero factor (by simp)
      have htailZero : ∀ other ∈ factors,
          sturmRootCount2 other.polynomial interval.lower interval.upper = 0 := by
        intro other hmem
        exact countsZero other (by simp [hmem])
      let headCertificate := compute factor.input interval proper hfactorLower
        hfactorUpper hfactorZero
      let tailCertificate := computeFactorProduct factors interval proper htailLower
        htailUpper htailZero
      exact Certificate.mul headCertificate tailCertificate

/-- Lemma 3.5 for every represented nonzero rational polynomial, using the
finite multiplicity-sensitive sum of its computed squarefree-factor Sturm
counts.  A zero sum supplies a zero-count certificate for every factor; their
positive bounds multiply, and the terminal nonzero scalar is restored
exactly. -/
def computeFromFactorCount {p : RatPolynomial} (hp : p.isZero = false)
    (root : RationalInterval) (proper : root.Proper)
    (lowerClear : p.eval root.lower ≠ 0)
    (upperClear : p.eval root.upper ≠ 0)
    (countZero : factorRootCount2 p hp root.lower root.upper = 0) :
    Certificate p root := by
  by_cases hdegree : p.natDegree = 0
  · exact Certificate.ofConstant hp hdegree root
  · let decomposition := decompose p hp hdegree
    have hdecompositionZero : decomposition.rootCount2 root.lower root.upper = 0 := by
      simpa [factorRootCount2, hdegree, decomposition] using countZero
    have hproductLower :
        (factorProduct decomposition.factors).eval root.lower ≠ 0 :=
      factorProduct_eval_ne_zero_of_decomposition_eval_ne_zero decomposition
        lowerClear
    have hproductUpper :
        (factorProduct decomposition.factors).eval root.upper ≠ 0 :=
      factorProduct_eval_ne_zero_of_decomposition_eval_ne_zero decomposition
        upperClear
    have hfactorCounts : ∀ factor ∈ decomposition.factors,
        sturmRootCount2 factor.polynomial root.lower root.upper = 0 := by
      intro factor hmem
      exact decomposition.factor_count_eq_zero_of_rootCount2_eq_zero proper
        lowerClear upperClear hdecompositionZero hmem
    let productCertificate := computeFactorProduct decomposition.factors root
      proper hproductLower hproductUpper hfactorCounts
    exact Certificate.ofScalarProduct decomposition.scalar
      decomposition.scalar_ne_zero productCertificate decomposition.eval_identity

private def linearPolynomial : RatPolynomial := ⟨[1, 2]⟩

private def linearInput : SquarefreeInput linearPolynomial where
  nonzero := by native_decide
  nonconstant := by native_decide
  squarefree :=
    { left := ⟨[]⟩
      right := ⟨[1]⟩
      polynomialIdentity := by
        rw [show derivative linearPolynomial = ⟨[1]⟩ by native_decide]
        simp [linearPolynomial, toPolynomial_eq_foldl_horner] }

/-- End-to-end regression for a zero-free linear polynomial on `[-1,1]`. -/
theorem compute_linear_example :
    let certificate := compute linearInput ⟨-1, 1⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)
    0 < certificate.bound ∧ certificate.bound ≤ linearPolynomial.eval 0 ^ 2 := by
  dsimp only
  constructor
  · exact (compute linearInput ⟨-1, 1⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)).positive
  · exact (compute linearInput ⟨-1, 1⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)).lower 0
        (by norm_num) (by norm_num)

private def repeatedCubicPolynomial : RatPolynomial := ⟨[1, -3, 3, -1]⟩

/-- End-to-end repeated-factor regression: `(T-1)^3` is zero-free on
`[-2,0]`, and the finite squarefree-factor count computes a positive bound
for the original cubic rather than merely for its squarefree quotient. -/
theorem compute_repeated_cubic_example :
    let certificate := computeFromFactorCount
      (p := repeatedCubicPolynomial) (by native_decide) ⟨-2, 0⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)
    0 < certificate.bound ∧
      certificate.bound ≤ repeatedCubicPolynomial.eval (-1) ^ 2 := by
  dsimp only
  constructor
  · exact (computeFromFactorCount
      (p := repeatedCubicPolynomial) (by native_decide) ⟨-2, 0⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)).positive
  · exact (computeFromFactorCount
      (p := repeatedCubicPolynomial) (by native_decide) ⟨-2, 0⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide) (by native_decide)).lower (-1)
        (by norm_num) (by norm_num)

end FTA.PositiveLowerBound
