import FTA.CCLPathIntersection
import FTA.SturmTransducer

/-!
# Quantitative finite sampling of projective CCL boundary arcs

Once a parameter cell excludes projective poles, coefficient-computed Horner
bounds give a rational modulus of variation for both affine coordinates of a
CCL boundary path.  The midpoint of any sufficiently narrow cell containing
an intersection is therefore a rational curve point within a requested
squared coordinate distance of the box.  The required central-third depth is
an explicit natural number.  This is the quantitative sampler used in the
zero-curve-count branch of Theorem 10.2.
-/

namespace FTA
namespace CCLIntersectionSampler

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.ProjectivePath
open FTA.CCLPathIntersection
open FTA.RationalPolynomialBounds
open FTA.SturmTransducer

abbrev QI := CCL.GaussianRat
abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- A positive whole-cell lower bound for the projective denominator norm. -/
structure DenominatorCertificate (path : Path) (interval : RationalInterval) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
    bound ≤ (denominatorNorm path).eval t

/-- A whole-cell sign certificate for the denominator norm directly yields
the positive denominator certificate consumed by the sampler. -/
def DenominatorCertificate.ofSignCertificate
    (path : Path) (interval : RationalInterval)
    (certificate : IntervalSignCertificate (denominatorNorm path)
      interval.lower interval.upper) :
    DenominatorCertificate path interval where
  bound := certificate.absMargin
  positive := certificate.absMargin_pos
  lower := by
    intro t lower upper
    have habs := certificate.absMargin_le_abs_eval lower upper
    rw [eval_denominatorNorm,
      abs_of_nonneg (normSq_nonneg (path.denominator.eval (ofRat t)))] at habs
    simpa only [eval_denominatorNorm] using habs

theorem DenominatorCertificate.denominator_ne
    {path : Path} {interval : RationalInterval}
    (certificate : DenominatorCertificate path interval) {t : ℚ}
    (lower : interval.lower ≤ t) (upper : t ≤ interval.upper) :
    path.denominator.eval (ofRat t) ≠ 0 := by
  intro zero
  have hbound := certificate.lower lower upper
  rw [eval_denominatorNorm, zero, normSq_zero] at hbound
  linarith [certificate.positive]

/-- Coefficient-computed Lipschitz coefficient for a rational quotient on a
cell where the denominator has the displayed positive lower bound. -/
def quotientVariationCoefficient
    (numerator denominator : RatPolynomial) (magnitude denominatorLower : ℚ) : ℚ :=
  (denseEvalLipschitzBound numerator magnitude *
      denseEvalAbsBound denominator magnitude +
    denseEvalAbsBound numerator magnitude *
      denseEvalLipschitzBound denominator magnitude) /
    denominatorLower ^ 2

theorem quotientVariationCoefficient_nonneg
    (numerator denominator : RatPolynomial) {magnitude denominatorLower : ℚ}
    (magnitudeNonnegative : 0 ≤ magnitude) :
    0 ≤ quotientVariationCoefficient numerator denominator
      magnitude denominatorLower := by
  have numeratorBounds := denseHornerBounds_nonneg numerator magnitudeNonnegative
  have denominatorBounds := denseHornerBounds_nonneg denominator magnitudeNonnegative
  unfold quotientVariationCoefficient
  apply div_nonneg
  · exact add_nonneg (mul_nonneg numeratorBounds.2 denominatorBounds.1)
      (mul_nonneg numeratorBounds.1 denominatorBounds.2)
  · exact sq_nonneg denominatorLower

/-- The numerator coefficient before division by the squared denominator
margin. -/
def crossVariationCoefficient
    (numerator denominator : RatPolynomial) (magnitude : ℚ) : ℚ :=
  denseEvalLipschitzBound numerator magnitude *
      denseEvalAbsBound denominator magnitude +
    denseEvalAbsBound numerator magnitude *
      denseEvalLipschitzBound denominator magnitude

theorem crossVariationCoefficient_nonneg
    (numerator denominator : RatPolynomial) {magnitude : ℚ}
    (magnitudeNonnegative : 0 ≤ magnitude) :
    0 ≤ crossVariationCoefficient numerator denominator magnitude := by
  have numeratorBounds := denseHornerBounds_nonneg numerator magnitudeNonnegative
  have denominatorBounds := denseHornerBounds_nonneg denominator magnitudeNonnegative
  exact add_nonneg (mul_nonneg numeratorBounds.2 denominatorBounds.1)
    (mul_nonneg numeratorBounds.1 denominatorBounds.2)

private theorem abs_cross_difference_le
    (numerator denominator : RatPolynomial) {a b s t : ℚ}
    (sLower : a ≤ s) (sUpper : s ≤ b)
    (tLower : a ≤ t) (tUpper : t ≤ b) :
    |(numerator.eval t - numerator.eval s) * denominator.eval s +
        numerator.eval s * (denominator.eval s - denominator.eval t)| ≤
      crossVariationCoefficient numerator denominator
        (intervalMagnitude a b) * |t - s| := by
  let magnitude := intervalMagnitude a b
  have magnitudeNonnegative : 0 ≤ magnitude := (intervalMagnitude_pos a b).le
  have numeratorBounds := denseHornerBounds_nonneg numerator magnitudeNonnegative
  have denominatorBounds := denseHornerBounds_nonneg denominator magnitudeNonnegative
  have sMagnitude : |s| ≤ magnitude :=
    abs_le_intervalMagnitude sLower sUpper
  have tMagnitude : |t| ≤ magnitude :=
    abs_le_intervalMagnitude tLower tUpper
  have numeratorAtS := abs_dense_eval_le_denseEvalAbsBound
    numerator magnitudeNonnegative sMagnitude
  have denominatorAtS := abs_dense_eval_le_denseEvalAbsBound
    denominator magnitudeNonnegative sMagnitude
  have numeratorDifference := abs_dense_eval_sub_eval_le_dense
    numerator magnitudeNonnegative tMagnitude sMagnitude
  have denominatorDifference := abs_dense_eval_sub_eval_le_dense
    denominator magnitudeNonnegative sMagnitude tMagnitude
  have denominatorDifference' :
      |denominator.eval s - denominator.eval t| ≤
        denseEvalLipschitzBound denominator magnitude * |t - s| := by
    simpa only [abs_sub_comm s t] using denominatorDifference
  have firstProduct :
      |numerator.eval t - numerator.eval s| * |denominator.eval s| ≤
        (denseEvalLipschitzBound numerator magnitude * |t - s|) *
          denseEvalAbsBound denominator magnitude := by
    exact mul_le_mul numeratorDifference denominatorAtS (abs_nonneg _)
      (mul_nonneg numeratorBounds.2 (abs_nonneg _))
  have secondProduct :
      |numerator.eval s| * |denominator.eval s - denominator.eval t| ≤
        denseEvalAbsBound numerator magnitude *
          (denseEvalLipschitzBound denominator magnitude * |t - s|) := by
    exact mul_le_mul numeratorAtS denominatorDifference' (abs_nonneg _)
      numeratorBounds.1
  calc
    |(numerator.eval t - numerator.eval s) * denominator.eval s +
        numerator.eval s * (denominator.eval s - denominator.eval t)| ≤
        |numerator.eval t - numerator.eval s| * |denominator.eval s| +
          |numerator.eval s| *
            |denominator.eval s - denominator.eval t| := by
      simpa only [abs_mul] using abs_add_le
        ((numerator.eval t - numerator.eval s) * denominator.eval s)
        (numerator.eval s * (denominator.eval s - denominator.eval t))
    _ ≤ (denseEvalLipschitzBound numerator magnitude * |t - s|) *
          denseEvalAbsBound denominator magnitude +
        denseEvalAbsBound numerator magnitude *
          (denseEvalLipschitzBound denominator magnitude * |t - s|) := by
      exact add_le_add firstProduct secondProduct
    _ = crossVariationCoefficient numerator denominator magnitude * |t - s| := by
      simp only [crossVariationCoefficient]
      ring

private theorem abs_div_sub_div_le_of_cross
    {numeratorT numeratorS denominatorT denominatorS coefficient
      denominatorLower distance : ℚ}
    (lowerPositive : 0 < denominatorLower)
    (lowerLeT : denominatorLower ≤ denominatorT)
    (lowerLeS : denominatorLower ≤ denominatorS)
    (coefficientNonnegative : 0 ≤ coefficient)
    (distanceNonnegative : 0 ≤ distance)
    (crossBound :
      |(numeratorT - numeratorS) * denominatorS +
          numeratorS * (denominatorS - denominatorT)| ≤
        coefficient * distance) :
    |numeratorT / denominatorT - numeratorS / denominatorS| ≤
      coefficient / denominatorLower ^ 2 * distance := by
  have denominatorTPositive : 0 < denominatorT := lowerPositive.trans_le lowerLeT
  have denominatorSPositive : 0 < denominatorS := lowerPositive.trans_le lowerLeS
  have productPositive : 0 < denominatorT * denominatorS :=
    mul_pos denominatorTPositive denominatorSPositive
  have lowerSqPositive : 0 < denominatorLower ^ 2 := sq_pos_of_pos lowerPositive
  have lowerSqLeProduct : denominatorLower ^ 2 ≤
      denominatorT * denominatorS := by
    simpa only [pow_two] using mul_le_mul lowerLeT lowerLeS
      lowerPositive.le denominatorTPositive.le
  have identity :
      numeratorT / denominatorT - numeratorS / denominatorS =
        ((numeratorT - numeratorS) * denominatorS +
          numeratorS * (denominatorS - denominatorT)) /
            (denominatorT * denominatorS) := by
    rw [div_sub_div numeratorT numeratorS denominatorTPositive.ne'
      denominatorSPositive.ne']
    congr 1
    ring
  rw [identity, abs_div, abs_of_pos productPositive]
  calc
    |(numeratorT - numeratorS) * denominatorS +
        numeratorS * (denominatorS - denominatorT)| /
          (denominatorT * denominatorS) ≤
        (coefficient * distance) / (denominatorT * denominatorS) :=
      div_le_div_of_nonneg_right crossBound productPositive.le
    _ ≤ (coefficient * distance) / denominatorLower ^ 2 := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg coefficientNonnegative distanceNonnegative
      · exact lowerSqPositive
      · exact lowerSqLeProduct
    _ = coefficient / denominatorLower ^ 2 * distance := by ring

/-- Rational quotient variation bound proved directly from the two Horner
value bounds, the two Horner slope bounds, and the positive denominator
margin. -/
theorem abs_eval_div_sub_eval_div_le
    (numerator denominator : RatPolynomial)
    {a b denominatorLower s t : ℚ}
    (denominatorLowerPositive : 0 < denominatorLower)
    (sLower : a ≤ s) (sUpper : s ≤ b)
    (tLower : a ≤ t) (tUpper : t ≤ b)
    (denominatorAtS : denominatorLower ≤ denominator.eval s)
    (denominatorAtT : denominatorLower ≤ denominator.eval t) :
    |numerator.eval t / denominator.eval t -
        numerator.eval s / denominator.eval s| ≤
      quotientVariationCoefficient numerator denominator
        (intervalMagnitude a b) denominatorLower * |t - s| := by
  apply abs_div_sub_div_le_of_cross denominatorLowerPositive
    denominatorAtT denominatorAtS
  · exact crossVariationCoefficient_nonneg numerator denominator
      (intervalMagnitude_pos a b).le
  · exact abs_nonneg _
  · exact abs_cross_difference_le numerator denominator
      sLower sUpper tLower tUpper

/-! ## Projective-path variation and explicit sampler depth -/

def realVariationCoefficient
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) : ℚ :=
  quotientVariationCoefficient (affineRealNumerator path)
    (denominatorNorm path)
    (intervalMagnitude interval.lower interval.upper) denominator.bound

def imagVariationCoefficient
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) : ℚ :=
  quotientVariationCoefficient (affineImagNumerator path)
    (denominatorNorm path)
    (intervalMagnitude interval.lower interval.upper) denominator.bound

def pathVariationCoefficient
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) : ℚ :=
  realVariationCoefficient path interval denominator ^ 2 +
    imagVariationCoefficient path interval denominator ^ 2

/-- A positive majorant is used so the width request also handles constant
paths without a special branch. -/
def pathVariationMajorant
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) : ℚ :=
  max 1 (pathVariationCoefficient path interval denominator)

theorem realVariationCoefficient_nonneg
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) :
    0 ≤ realVariationCoefficient path interval denominator := by
  exact quotientVariationCoefficient_nonneg _ _
    (intervalMagnitude_pos interval.lower interval.upper).le

theorem imagVariationCoefficient_nonneg
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) :
    0 ≤ imagVariationCoefficient path interval denominator := by
  exact quotientVariationCoefficient_nonneg _ _
    (intervalMagnitude_pos interval.lower interval.upper).le

theorem pathVariationCoefficient_nonneg
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) :
    0 ≤ pathVariationCoefficient path interval denominator := by
  unfold pathVariationCoefficient
  positivity

theorem pathVariationMajorant_pos
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) :
    0 < pathVariationMajorant path interval denominator :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem pathVariationCoefficient_le_majorant
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) :
    pathVariationCoefficient path interval denominator ≤
      pathVariationMajorant path interval denominator :=
  le_max_right _ _

theorem abs_path_value_re_sub_le
    {path : Path} {interval : RationalInterval}
    (denominator : DenominatorCertificate path interval) {s t : ℚ}
    (sLower : interval.lower ≤ s) (sUpper : s ≤ interval.upper)
    (tLower : interval.lower ≤ t) (tUpper : t ≤ interval.upper) :
    |(path.value t).re - (path.value s).re| ≤
      realVariationCoefficient path interval denominator * |t - s| := by
  rw [path_value_re path t (denominator.denominator_ne tLower tUpper),
    path_value_re path s (denominator.denominator_ne sLower sUpper)]
  exact abs_eval_div_sub_eval_div_le _ _ denominator.positive
    sLower sUpper tLower tUpper
    (denominator.lower sLower sUpper) (denominator.lower tLower tUpper)

theorem abs_path_value_im_sub_le
    {path : Path} {interval : RationalInterval}
    (denominator : DenominatorCertificate path interval) {s t : ℚ}
    (sLower : interval.lower ≤ s) (sUpper : s ≤ interval.upper)
    (tLower : interval.lower ≤ t) (tUpper : t ≤ interval.upper) :
    |(path.value t).im - (path.value s).im| ≤
      imagVariationCoefficient path interval denominator * |t - s| := by
  rw [path_value_im path t (denominator.denominator_ne tLower tUpper),
    path_value_im path s (denominator.denominator_ne sLower sUpper)]
  exact abs_eval_div_sub_eval_div_le _ _ denominator.positive
    sLower sUpper tLower tUpper
    (denominator.lower sLower sUpper) (denominator.lower tLower tUpper)

theorem normSq_path_value_sub_le
    {path : Path} {interval : RationalInterval}
    (denominator : DenominatorCertificate path interval) {s t : ℚ}
    (sLower : interval.lower ≤ s) (sUpper : s ≤ interval.upper)
    (tLower : interval.lower ≤ t) (tUpper : t ≤ interval.upper) :
    normSq (path.value t - path.value s) ≤
      pathVariationCoefficient path interval denominator * |t - s| ^ 2 := by
  have realBound := abs_path_value_re_sub_le denominator
    sLower sUpper tLower tUpper
  have imagBound := abs_path_value_im_sub_le denominator
    sLower sUpper tLower tUpper
  have realSq : ((path.value t).re - (path.value s).re) ^ 2 ≤
      (realVariationCoefficient path interval denominator * |t - s|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) realBound 2
  have imagSq : ((path.value t).im - (path.value s).im) ^ 2 ≤
      (imagVariationCoefficient path interval denominator * |t - s|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) imagBound 2
  simp only [normSq, sub_re, sub_im]
  calc
    ((path.value t).re - (path.value s).re) ^ 2 +
        ((path.value t).im - (path.value s).im) ^ 2 ≤
      (realVariationCoefficient path interval denominator * |t - s|) ^ 2 +
        (imagVariationCoefficient path interval denominator * |t - s|) ^ 2 :=
      add_le_add realSq imagSq
    _ = pathVariationCoefficient path interval denominator * |t - s| ^ 2 := by
      unfold pathVariationCoefficient
      ring

/-- Requested cell width ensuring a strict squared-distance error.  The
factor `2` leaves a strict margin even when the central-third width estimate
is attained exactly. -/
def samplingWidth
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) (epsilon : ℚ) : ℚ :=
  min 1 (epsilon / (2 * pathVariationMajorant path interval denominator))

theorem samplingWidth_pos
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) :
    0 < samplingWidth path interval denominator epsilon := by
  apply lt_min zero_lt_one
  exact div_pos epsilonPositive
    (mul_pos (by norm_num) (pathVariationMajorant_pos path interval denominator))

/-- Explicit requested number of central-third refinement calls. -/
def samplingDepth
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval) (epsilon : ℚ) : ℕ :=
  geometricDepth interval.width (samplingWidth path interval denominator epsilon)

theorem samplingDepth_sufficient
    (path : Path) (interval : RationalInterval)
    (denominator : DenominatorCertificate path interval)
    (proper : interval.Proper) {epsilon : ℚ} (epsilonPositive : 0 < epsilon) :
    (2 / 3 : ℚ) ^ samplingDepth path interval denominator epsilon *
        interval.width ≤ samplingWidth path interval denominator epsilon := by
  exact geometricDepth_sufficient (RationalInterval.width_pos proper).le
    (samplingWidth_pos path interval denominator epsilonPositive)

/-- A rational point lies within the requested squared coordinate distance of
a rational box when a box member supplies the displayed witness. -/
def WithinSqOfBox (box : RatBox) (point : QI) (epsilon : ℚ) : Prop :=
  ∃ witness : QI, box.Contains witness ∧ normSq (point - witness) < epsilon

theorem WithinSqOfBox.mono
    {box : RatBox} {point : QI} {epsilon larger : ℚ}
    (near : WithinSqOfBox box point epsilon) (le : epsilon ≤ larger) :
    WithinSqOfBox box point larger := by
  rcases near with ⟨witness, inside, distance⟩
  exact ⟨witness, inside, distance.trans_le le⟩

def clampCoordinate (lower upper value : ℚ) : ℚ :=
  max lower (min value upper)

theorem clampCoordinate_lower {lower upper value : ℚ} :
    lower ≤ clampCoordinate lower upper value :=
  le_max_left _ _

theorem clampCoordinate_upper {lower upper value : ℚ}
    (valid : lower ≤ upper) :
    clampCoordinate lower upper value ≤ upper := by
  apply max_le valid
  exact min_le_right _ _

theorem abs_sub_clampCoordinate_le
    {lower upper value margin : ℚ} (valid : lower ≤ upper)
    (marginNonnegative : 0 ≤ margin)
    (lowerSlack : lower - margin ≤ value)
    (upperSlack : value ≤ upper + margin) :
    |value - clampCoordinate lower upper value| ≤ margin := by
  by_cases below : value < lower
  · have valueLeUpper : value ≤ upper := below.le.trans valid
    rw [clampCoordinate, min_eq_left valueLeUpper, max_eq_left below.le]
    rw [abs_of_nonpos (sub_nonpos.mpr below.le)]
    linarith
  · have lowerLeValue : lower ≤ value := le_of_not_gt below
    by_cases above : upper < value
    · rw [clampCoordinate, min_eq_right above.le,
        max_eq_right valid]
      rw [abs_of_nonneg (sub_nonneg.mpr above.le)]
      linarith
    · have valueLeUpper : value ≤ upper := le_of_not_gt above
      rw [clampCoordinate, min_eq_left valueLeUpper,
        max_eq_right lowerLeValue]
      simpa using marginNonnegative

def clampToBox (box : RatBox) (point : QI) : QI :=
  ⟨clampCoordinate box.xLower box.xUpper point.re,
    clampCoordinate box.yLower box.yUpper point.im⟩

theorem clampToBox_contains (box : RatBox) (point : QI) :
    box.Contains (clampToBox box point) :=
  ⟨clampCoordinate_lower,
    clampCoordinate_upper box.x_valid,
    clampCoordinate_lower,
    clampCoordinate_upper box.y_valid⟩

/-- If a point is not strictly inside a box, its coordinatewise clamp lies
on one of the four box edges. -/
theorem clampToBox_boundary_coordinates_of_not_strictContains
    {box : RatBox} {point : QI} (notStrict : ¬box.StrictContains point) :
    box.Contains (clampToBox box point) ∧
      ((clampToBox box point).re = box.xLower ∨
        (clampToBox box point).re = box.xUpper ∨
        (clampToBox box point).im = box.yLower ∨
        (clampToBox box point).im = box.yUpper) := by
  refine ⟨clampToBox_contains box point, ?_⟩
  by_cases xBelow : point.re ≤ box.xLower
  · left
    simp [clampToBox, clampCoordinate,
      min_eq_left (xBelow.trans box.x_valid), max_eq_left xBelow]
  · have xLower : box.xLower < point.re := lt_of_not_ge xBelow
    by_cases xAbove : box.xUpper ≤ point.re
    · right
      left
      simp [clampToBox, clampCoordinate, min_eq_right xAbove,
        max_eq_right box.x_valid]
    · have xUpper : point.re < box.xUpper := lt_of_not_ge xAbove
      by_cases yBelow : point.im ≤ box.yLower
      · right
        right
        left
        simp [clampToBox, clampCoordinate,
          min_eq_left (yBelow.trans box.y_valid), max_eq_left yBelow]
      · have yLower : box.yLower < point.im := lt_of_not_ge yBelow
        by_cases yAbove : box.yUpper ≤ point.im
        · right
          right
          right
          simp [clampToBox, clampCoordinate, min_eq_right yAbove,
            max_eq_right box.y_valid]
        · have yUpper : point.im < box.yUpper := lt_of_not_ge yAbove
          exact (notStrict ⟨xLower, xUpper, yLower, yUpper⟩).elim

/-- The clamp point realizes the explicit squared-distance estimate used by
the sampler's coordinate-slack argument. -/
theorem normSq_sub_clampToBox_lt_of_coordinate_slack
    {box : RatBox} {point : QI} {margin : ℚ}
    (marginPositive : 0 < margin)
    (xLower : box.xLower - margin ≤ point.re)
    (xUpper : point.re ≤ box.xUpper + margin)
    (yLower : box.yLower - margin ≤ point.im)
    (yUpper : point.im ≤ box.yUpper + margin) :
    normSq (point - clampToBox box point) < 3 * margin ^ 2 := by
  let witness := clampToBox box point
  have realAbs : |point.re - witness.re| ≤ margin := by
    exact abs_sub_clampCoordinate_le box.x_valid marginPositive.le
      xLower xUpper
  have imagAbs : |point.im - witness.im| ≤ margin := by
    exact abs_sub_clampCoordinate_le box.y_valid marginPositive.le
      yLower yUpper
  have realSquare : (point.re - witness.re) ^ 2 ≤ margin ^ 2 := by
    calc
      (point.re - witness.re) ^ 2 = |point.re - witness.re| ^ 2 :=
        (sq_abs _).symm
      _ ≤ margin ^ 2 := pow_le_pow_left₀ (abs_nonneg _) realAbs 2
  have imagSquare : (point.im - witness.im) ^ 2 ≤ margin ^ 2 := by
    calc
      (point.im - witness.im) ^ 2 = |point.im - witness.im| ^ 2 :=
        (sq_abs _).symm
      _ ≤ margin ^ 2 := pow_le_pow_left₀ (abs_nonneg _) imagAbs 2
  simp only [normSq, sub_re, sub_im]
  have sumBound := add_le_add realSquare imagSquare
  nlinarith [sq_pos_of_pos marginPositive]

/-- Four rational coordinate slacks give an explicit point in the box and a
strict squared-distance certificate.  The factor three leaves a strict
margin over the sum of the two coordinate-square bounds. -/
theorem withinSqOfBox_of_coordinate_slack
    {box : RatBox} {point : QI} {margin : ℚ}
    (marginPositive : 0 < margin)
    (xLower : box.xLower - margin ≤ point.re)
    (xUpper : point.re ≤ box.xUpper + margin)
    (yLower : box.yLower - margin ≤ point.im)
    (yUpper : point.im ≤ box.yUpper + margin) :
    WithinSqOfBox box point (3 * margin ^ 2) := by
  exact ⟨clampToBox box point, clampToBox_contains box point,
    normSq_sub_clampToBox_lt_of_coordinate_slack marginPositive
      xLower xUpper yLower yUpper⟩

/-- Quantitative finite intersection sampler.  If a refined parameter cell
contains an actual rational path intersection with the box and has reached
the precomputed width, its rational midpoint is strictly within the requested
squared coordinate distance of the box. -/
theorem midpoint_withinSqOfBox
    {path : Path} {root cell : RationalInterval}
    (denominator : DenominatorCertificate path root)
    (cellRefines : cell.Refines root) (cellProper : cell.Proper)
    {box : RatBox} {intersectionParameter epsilon : ℚ}
    (epsilonPositive : 0 < epsilon)
    (widthSmall : cell.width ≤ samplingWidth path root denominator epsilon)
    (parameterLower : cell.lower ≤ intersectionParameter)
    (parameterUpper : intersectionParameter ≤ cell.upper)
    (intersection : box.Contains (path.value intersectionParameter)) :
    WithinSqOfBox box
      (path.value (midpoint cell.lower cell.upper)) epsilon := by
  let sample := midpoint cell.lower cell.upper
  have sampleLowerCell : cell.lower ≤ sample :=
    (lower_lt_midpoint cellProper).le
  have sampleUpperCell : sample ≤ cell.upper :=
    (midpoint_lt_upper cellProper).le
  have parameterLowerRoot : root.lower ≤ intersectionParameter :=
    cellRefines.1.trans parameterLower
  have parameterUpperRoot : intersectionParameter ≤ root.upper :=
    parameterUpper.trans cellRefines.2
  have sampleLowerRoot : root.lower ≤ sample :=
    cellRefines.1.trans sampleLowerCell
  have sampleUpperRoot : sample ≤ root.upper :=
    sampleUpperCell.trans cellRefines.2
  have distanceLeRadius : |sample - intersectionParameter| ≤
      intervalRadius cell.lower cell.upper sample :=
    abs_sample_sub_le_intervalRadius parameterLower parameterUpper
  have distanceLeWidth : |sample - intersectionParameter| ≤ cell.width := by
    calc
      |sample - intersectionParameter| ≤
          intervalRadius cell.lower cell.upper sample := distanceLeRadius
      _ = cell.width / 2 := by
        simpa only [sample] using cell.midpointRadius_eq_half_width cellProper
      _ ≤ cell.width := by
        linarith [RationalInterval.width_pos cellProper]
  let majorant := pathVariationMajorant path root denominator
  have majorantPositive : 0 < majorant :=
    pathVariationMajorant_pos path root denominator
  have widthNonnegative : 0 ≤ cell.width :=
    (RationalInterval.width_pos cellProper).le
  have widthAtMostOne : cell.width ≤ 1 :=
    widthSmall.trans (min_le_left _ _)
  have widthAtMostError :
      cell.width ≤ epsilon / (2 * majorant) :=
    widthSmall.trans (min_le_right _ _)
  have widthSqLeWidth : cell.width ^ 2 ≤ cell.width := by
    nlinarith
  have distanceSqLeWidthSq :
      |sample - intersectionParameter| ^ 2 ≤ cell.width ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) distanceLeWidth 2
  have variationBound := normSq_path_value_sub_le denominator
    parameterLowerRoot parameterUpperRoot sampleLowerRoot sampleUpperRoot
  have coefficientLeMajorant :=
    pathVariationCoefficient_le_majorant path root denominator
  have errorLe : normSq
      (path.value sample - path.value intersectionParameter) ≤
      majorant * cell.width := by
    calc
      normSq (path.value sample - path.value intersectionParameter) ≤
          pathVariationCoefficient path root denominator *
            |sample - intersectionParameter| ^ 2 := variationBound
      _ ≤ majorant * |sample - intersectionParameter| ^ 2 := by
        exact mul_le_mul_of_nonneg_right coefficientLeMajorant (sq_nonneg _)
      _ ≤ majorant * cell.width ^ 2 :=
        mul_le_mul_of_nonneg_left distanceSqLeWidthSq majorantPositive.le
      _ ≤ majorant * cell.width :=
        mul_le_mul_of_nonneg_left widthSqLeWidth majorantPositive.le
  have majorantWidthLeHalf : majorant * cell.width ≤ epsilon / 2 := by
    have scaled := (le_div_iff₀
      (mul_pos (by norm_num) majorantPositive)).mp widthAtMostError
    nlinarith
  refine ⟨path.value intersectionParameter, intersection, ?_⟩
  simpa only [sample] using errorLe.trans_lt
    (majorantWidthLeHalf.trans_lt (by linarith))

/-- Direct finite-depth form: any central-third descendant satisfying the
standard geometric contraction after the computed number of calls is already
small enough for the midpoint sampler. -/
theorem midpoint_withinSqOfBox_of_samplingDepth
    {path : Path} {root cell : RationalInterval}
    (denominator : DenominatorCertificate path root)
    (rootProper : root.Proper)
    (cellRefines : cell.Refines root) (cellProper : cell.Proper)
    {box : RatBox} {intersectionParameter epsilon : ℚ}
    (epsilonPositive : 0 < epsilon)
    (widthBound : cell.width ≤
      (2 / 3 : ℚ) ^ samplingDepth path root denominator epsilon * root.width)
    (parameterLower : cell.lower ≤ intersectionParameter)
    (parameterUpper : intersectionParameter ≤ cell.upper)
    (intersection : box.Contains (path.value intersectionParameter)) :
    WithinSqOfBox box
      (path.value (midpoint cell.lower cell.upper)) epsilon := by
  apply midpoint_withinSqOfBox denominator cellRefines cellProper
    epsilonPositive
  · exact widthBound.trans
      (samplingDepth_sufficient path root denominator rootProper epsilonPositive)
  · exact parameterLower
  · exact parameterUpper
  · exact intersection

/-! ## Executable fixed-depth sampler cells -/

/-- One terminal parameter cell produced at the precomputed sampler depth. -/
structure SamplingCell
    (path : Path) (root : RationalInterval)
    (denominator : DenominatorCertificate path root) (epsilon : ℚ) where
  interval : RationalInterval
  refines : interval.Refines root
  proper : interval.Proper
  widthSmall : interval.width ≤ samplingWidth path root denominator epsilon

/-- Binary midpoint subdivision with a proof that every returned interval
has reached the sampler width.  The displayed `2/3` estimate deliberately
over-approximates the actual halving contraction. -/
def buildSamplingCells
    (path : Path) (root : RationalInterval)
    (denominator : DenominatorCertificate path root) (epsilon : ℚ) :
    (fuel : ℕ) → (interval : RationalInterval) →
      interval.Refines root → interval.Proper →
      (2 / 3 : ℚ) ^ fuel * interval.width ≤
        samplingWidth path root denominator epsilon →
      List (SamplingCell path root denominator epsilon)
  | 0, interval, refines, proper, sufficient =>
      [{ interval := interval
         refines := refines
         proper := proper
         widthSmall := by simpa using sufficient }]
  | fuel + 1, interval, refines, proper, sufficient => by
      let cut := midpoint interval.lower interval.upper
      let left := interval.left cut
      let right := interval.right cut
      have lowerLt : interval.lower < cut := lower_lt_midpoint proper
      have ltUpper : cut < interval.upper := midpoint_lt_upper proper
      have leftProper : left.Proper := by
        change interval.lower < cut
        exact lowerLt
      have rightProper : right.Proper := by
        change cut < interval.upper
        exact ltUpper
      have leftRefines : left.Refines root :=
        RationalInterval.refines_trans
          (by exact ⟨le_rfl, ltUpper.le⟩) refines
      have rightRefines : right.Refines root :=
        RationalInterval.refines_trans
          (by exact ⟨lowerLt.le, le_rfl⟩) refines
      have leftWidth : left.width < (2 / 3 : ℚ) * interval.width := by
        have widthPositive := RationalInterval.width_pos proper
        dsimp [left, cut, RationalInterval.left, RationalInterval.width,
          RationalPolynomialBounds.midpoint]
        dsimp [RationalInterval.width] at widthPositive
        linarith
      have rightWidth : right.width < (2 / 3 : ℚ) * interval.width := by
        have widthPositive := RationalInterval.width_pos proper
        dsimp [right, cut, RationalInterval.right, RationalInterval.width,
          RationalPolynomialBounds.midpoint]
        dsimp [RationalInterval.width] at widthPositive
        linarith
      have factorPositive : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
      have leftSufficient :
          (2 / 3 : ℚ) ^ fuel * left.width ≤
            samplingWidth path root denominator epsilon := by
        calc
          (2 / 3 : ℚ) ^ fuel * left.width ≤
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_le_mul_of_nonneg_left leftWidth.le factorPositive.le
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ ≤ samplingWidth path root denominator epsilon := sufficient
      have rightSufficient :
          (2 / 3 : ℚ) ^ fuel * right.width ≤
            samplingWidth path root denominator epsilon := by
        calc
          (2 / 3 : ℚ) ^ fuel * right.width ≤
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_le_mul_of_nonneg_left rightWidth.le factorPositive.le
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ ≤ samplingWidth path root denominator epsilon := sufficient
      exact buildSamplingCells path root denominator epsilon fuel left
          leftRefines leftProper leftSufficient ++
        buildSamplingCells path root denominator epsilon fuel right
          rightRefines rightProper rightSufficient

/-- The executable list at exactly the coefficient-computed sampler depth. -/
def samplingCells
    (path : Path) (root : RationalInterval)
    (denominator : DenominatorCertificate path root)
    (rootProper : root.Proper) (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    List (SamplingCell path root denominator epsilon) :=
  buildSamplingCells path root denominator epsilon
    (samplingDepth path root denominator epsilon) root
    (RationalInterval.refines_refl root) rootProper
    (samplingDepth_sufficient path root denominator rootProper epsilonPositive)

/-- Every rational parameter in the root interval lies in a returned sampler
cell. -/
theorem buildSamplingCells_cover
    (path : Path) (root : RationalInterval)
    (denominator : DenominatorCertificate path root) (epsilon : ℚ)
    (fuel : ℕ) (interval : RationalInterval)
    (refines : interval.Refines root) (proper : interval.Proper)
    (sufficient : (2 / 3 : ℚ) ^ fuel * interval.width ≤
      samplingWidth path root denominator epsilon)
    {t : ℚ} (lower : interval.lower ≤ t) (upper : t ≤ interval.upper) :
    ∃ cell ∈ buildSamplingCells path root denominator epsilon fuel interval
        refines proper sufficient,
      cell.interval.lower ≤ t ∧ t ≤ cell.interval.upper := by
  induction fuel generalizing interval with
  | zero =>
      refine ⟨{ interval := interval
                refines := refines
                proper := proper
                widthSmall := by simpa using sufficient }, ?_, lower, upper⟩
      simp [buildSamplingCells]
  | succ fuel inductionHypothesis =>
      let cut := midpoint interval.lower interval.upper
      let left := interval.left cut
      let right := interval.right cut
      have lowerLt : interval.lower < cut := lower_lt_midpoint proper
      have ltUpper : cut < interval.upper := midpoint_lt_upper proper
      have leftProper : left.Proper := by
        change interval.lower < cut
        exact lowerLt
      have rightProper : right.Proper := by
        change cut < interval.upper
        exact ltUpper
      have leftRefines : left.Refines root :=
        RationalInterval.refines_trans
          (by exact ⟨le_rfl, ltUpper.le⟩) refines
      have rightRefines : right.Refines root :=
        RationalInterval.refines_trans
          (by exact ⟨lowerLt.le, le_rfl⟩) refines
      have leftWidth : left.width < (2 / 3 : ℚ) * interval.width := by
        have widthPositive := RationalInterval.width_pos proper
        dsimp [left, cut, RationalInterval.left, RationalInterval.width,
          RationalPolynomialBounds.midpoint]
        dsimp [RationalInterval.width] at widthPositive
        linarith
      have rightWidth : right.width < (2 / 3 : ℚ) * interval.width := by
        have widthPositive := RationalInterval.width_pos proper
        dsimp [right, cut, RationalInterval.right, RationalInterval.width,
          RationalPolynomialBounds.midpoint]
        dsimp [RationalInterval.width] at widthPositive
        linarith
      have factorPositive : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
      have leftSufficient :
          (2 / 3 : ℚ) ^ fuel * left.width ≤
            samplingWidth path root denominator epsilon := by
        calc
          (2 / 3 : ℚ) ^ fuel * left.width ≤
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_le_mul_of_nonneg_left leftWidth.le factorPositive.le
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ ≤ samplingWidth path root denominator epsilon := sufficient
      have rightSufficient :
          (2 / 3 : ℚ) ^ fuel * right.width ≤
            samplingWidth path root denominator epsilon := by
        calc
          (2 / 3 : ℚ) ^ fuel * right.width ≤
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_le_mul_of_nonneg_left rightWidth.le factorPositive.le
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ ≤ samplingWidth path root denominator epsilon := sufficient
      by_cases leftSide : t ≤ cut
      · rcases inductionHypothesis left leftRefines leftProper leftSufficient
          lower leftSide with ⟨cell, member, cellLower, cellUpper⟩
        refine ⟨cell, ?_, cellLower, cellUpper⟩
        simp only [buildSamplingCells, List.mem_append]
        exact Or.inl member
      · have rightLower : cut ≤ t := (lt_of_not_ge leftSide).le
        rcases inductionHypothesis right rightRefines rightProper
            rightSufficient rightLower upper with
          ⟨cell, member, cellLower, cellUpper⟩
        refine ⟨cell, ?_, cellLower, cellUpper⟩
        simp only [buildSamplingCells, List.mem_append]
        exact Or.inr member

theorem samplingCells_cover
    (path : Path) (root : RationalInterval)
    (denominator : DenominatorCertificate path root)
    (rootProper : root.Proper) (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    {t : ℚ} (lower : root.lower ≤ t) (upper : t ≤ root.upper) :
    ∃ cell ∈ samplingCells path root denominator rootProper epsilon
        epsilonPositive,
      cell.interval.lower ≤ t ∧ t ≤ cell.interval.upper := by
  exact buildSamplingCells_cover path root denominator epsilon
    (samplingDepth path root denominator epsilon) root
    (RationalInterval.refines_refl root) rootProper
    (samplingDepth_sufficient path root denominator rootProper epsilonPositive)
    lower upper

end CCLIntersectionSampler
end FTA
