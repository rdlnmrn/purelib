import FTA.PositiveLowerBound
import FTA.CCLIntersectionEventSigns

/-!
# Divisibility transfer for executable root counts

A squarefree count-one divisor forces a positive multiplicity-sensitive root
count for its nonzero multiple on any clear ambient interval containing that
cell.  The proof remains entirely rational: a hypothetical zero count gives a
coefficient-computed positive lower bound for the multiple, while finite
count-one refinement produces an endpoint where the divisor, and hence the
multiple, is too small.
-/

namespace FTA
namespace RootCountDivisibility

open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.CCLIntersectionEventSigns
open FTA.DenseDerivative
open FTA.PositiveLowerBound
open FTA.RationalPolynomialBounds
open FTA.SquarefreeFactorization
open FTA.Sturm
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

private theorem remainder_isZero_of_toPolynomial_dvd
    {small large : RatPolynomial}
    (smallNonzero : small.isZero = false)
    (divides : small.toPolynomial ∣ large.toPolynomial) :
    (divMod large small).remainder.isZero = true := by
  exact divMod_remainder_isZero_of_toPolynomial_dvd smallNonzero divides

private theorem abs_left_le_abs_sub_of_mul_neg {x y : ℚ}
    (opposite : x * y < 0) : |x| ≤ |x - y| := by
  rcases mul_neg_iff.mp opposite with ⟨xPositive, yNegative⟩ |
      ⟨xNegative, yPositive⟩
  · rw [abs_of_pos xPositive, abs_of_pos (sub_pos.mpr (yNegative.trans xPositive))]
    linarith
  · rw [abs_of_neg xNegative, abs_of_neg (sub_neg.mpr (xNegative.trans yPositive))]
    linarith

/-! ## Quantitative rational approximation of a count-one divisor root -/

def approximationMagnitude {small : RatPolynomial}
    (root : CountOneInterval small) : ℚ :=
  intervalMagnitude root.interval.lower root.interval.upper

def approximationSlope (small : RatPolynomial)
    (root : CountOneInterval small) : ℚ :=
  denseEvalLipschitzBound small (approximationMagnitude root)

def approximationQuotientBound
    (large small : RatPolynomial) (root : CountOneInterval small) : ℚ :=
  denseEvalAbsBound (divMod large small).quotient
    (approximationMagnitude root)

def approximationBound
    (large small : RatPolynomial) (root : CountOneInterval small)
    (epsilon : ℚ) : ℚ :=
  approximationSlope small root * epsilon *
    approximationQuotientBound large small root

def approximationCoefficient
    (large small : RatPolynomial) (root : CountOneInterval small) : ℚ :=
  approximationSlope small root *
    approximationQuotientBound large small root

theorem approximationBound_eq_coefficient_mul
    (large small : RatPolynomial) (root : CountOneInterval small)
    (epsilon : ℚ) :
    approximationBound large small root epsilon =
      approximationCoefficient large small root * epsilon := by
  unfold approximationBound approximationCoefficient
  ring

theorem approximationCoefficient_nonneg
    (large small : RatPolynomial) (root : CountOneInterval small) :
    0 ≤ approximationCoefficient large small root := by
  apply mul_nonneg
  · exact (denseHornerBounds_nonneg small
      (intervalMagnitude_pos root.interval.lower root.interval.upper).le).2
  · exact (denseHornerBounds_nonneg (divMod large small).quotient
      (intervalMagnitude_pos root.interval.lower root.interval.upper).le).1

/-- A rational point in the original count-one interval where any displayed
polynomial multiple of the isolated squarefree factor is explicitly small.
The point is computed by the ordinary fixed-depth event refinement. -/
structure MultipleApproximation
    (large small : RatPolynomial) (root : CountOneInterval small)
    (epsilon : ℚ) where
  parameter : ℚ
  lower : root.interval.lower ≤ parameter
  upper : parameter ≤ root.interval.upper
  smallValue : |large.eval parameter| ≤
    approximationBound large small root epsilon

/-- The small proof package returned before transferring the estimate through
polynomial divisibility. -/
structure NarrowEventApproximation
    {small : RatPolynomial} (input : SquarefreeInput small)
    (root : CountOneInterval small) (epsilon : ℚ) where
  refined : CountOneInterval small
  refines : refined.interval.Refines root.interval
  width : refined.interval.width ≤ epsilon
  crossing : small.eval refined.interval.lower *
    small.eval refined.interval.upper < 0

def approximationWidth
    {small : RatPolynomial} (input : SquarefreeInput small)
    (root : CountOneInterval small) (epsilon : ℚ) : ℚ :=
  min epsilon
    (ambientEventClassifierWidthResolution input root.interval / 2)

theorem approximationWidth_pos
    {small : RatPolynomial} (input : SquarefreeInput small)
    (root : CountOneInterval small) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) :
    0 < approximationWidth input root epsilon := by
  apply lt_min epsilonPositive
  exact div_pos (ambientEventClassifierWidthResolution_pos input root.interval)
    (by norm_num)

theorem approximationWidth_le
    {small : RatPolynomial} (input : SquarefreeInput small)
    (root : CountOneInterval small) (epsilon : ℚ) :
    approximationWidth input root epsilon ≤ epsilon :=
  min_le_left _ _

theorem approximationWidth_lt_resolution
    {small : RatPolynomial} (input : SquarefreeInput small)
    (root : CountOneInterval small) (epsilon : ℚ) :
    approximationWidth input root epsilon <
      ambientEventClassifierWidthResolution input root.interval := by
  have positive :=
    ambientEventClassifierWidthResolution_pos input root.interval
  exact (min_le_right _ _).trans_lt (by linarith)

def narrowEventApproximation
    {small : RatPolynomial} (input : SquarefreeInput small)
    (root : CountOneInterval small) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    NarrowEventApproximation input root epsilon := by
  let requested := approximationWidth input root epsilon
  have requestedPositive : 0 < requested :=
    approximationWidth_pos input root epsilonPositive
  let refined := runToWidth input (computedEventPartitionProgram input) root
    requested requestedPositive
  have refines : refined.interval.Refines root.interval :=
    runToWidth_refines input (computedEventPartitionProgram input) root
      requested requestedPositive
  have widthRequested : refined.interval.width ≤ requested :=
    runToWidth_le input (computedEventPartitionProgram input) root
      requested requestedPositive
  have width : refined.interval.width ≤ epsilon :=
    widthRequested.trans (approximationWidth_le input root epsilon)
  have widthResolution : refined.interval.width <
      ambientEventClassifierWidthResolution input root.interval :=
    widthRequested.trans_lt
      (approximationWidth_lt_resolution input root epsilon)
  have crossing := endpoint_mul_neg_of_countOne_refined_width input
    root.interval refined.interval refines refined.proper refined.lowerClear
      refined.upperClear refined.countOne widthResolution
  exact ⟨refined, refines, width, crossing⟩

/-- The executable narrowing always performs the hidden classifier-resolution
cap, independently of the caller's requested approximation width. -/
theorem narrowEventApproximation_width_lt_resolution
    {small : RatPolynomial} (input : SquarefreeInput small)
    (root : CountOneInterval small) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    (narrowEventApproximation input root epsilon
      epsilonPositive).refined.interval.width <
        ambientEventClassifierWidthResolution input root.interval := by
  let requested := approximationWidth input root epsilon
  have widthRequested :
      (runToWidth input (computedEventPartitionProgram input) root requested
        (approximationWidth_pos input root epsilonPositive)).interval.width ≤
          requested :=
    runToWidth_le input (computedEventPartitionProgram input) root requested
      (approximationWidth_pos input root epsilonPositive)
  exact widthRequested.trans_lt
    (approximationWidth_lt_resolution input root epsilon)

/-- Every actual narrow approximation inherits the canonical lower-endpoint
orientation against the squarefree event derivative. -/
theorem narrowEventApproximation_lower_derivative_mul_neg
    {small : RatPolynomial} (input : SquarefreeInput small)
    (root : CountOneInterval small) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    small.eval (narrowEventApproximation input root epsilon
        epsilonPositive).refined.interval.lower *
      (derivative small).eval (narrowEventApproximation input root epsilon
        epsilonPositive).refined.interval.lower < 0 := by
  let approximation := narrowEventApproximation input root epsilon
    epsilonPositive
  exact lower_derivative_mul_neg_of_countOne_refined_width input root.interval
    approximation.refined.interval approximation.refines
    approximation.refined.proper approximation.refined.lowerClear
    approximation.refined.upperClear approximation.refined.countOne
    (narrowEventApproximation_width_lt_resolution input root epsilon
      epsilonPositive)

/-- A nonzero polynomial of degree at most one which is divisible by a
nonconstant squarefree event factor differs from that factor by one nonzero
constant.  Consequently any same-side sign comparison for the factor
transfers to the multiple. -/
theorem evals_mul_pos_of_dvd_natDegree_le_one
    {small large : RatPolynomial} (input : SquarefreeInput small)
    (largeNonzero : large.isZero = false)
    (largeDegree : large.natDegree ≤ 1)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    {left right : ℚ}
    (smallSign : 0 < small.eval left * small.eval right) :
    0 < large.eval left * large.eval right := by
  rcases divides with ⟨cofactor, identity⟩
  have smallPolynomialNonzero : small.toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false input.nonzero
  have largePolynomialNonzero : large.toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false largeNonzero
  have cofactorNonzero : cofactor ≠ 0 := by
    intro zero
    rw [zero, mul_zero] at identity
    exact largePolynomialNonzero identity
  have degrees := congrArg Polynomial.natDegree identity
  rw [Polynomial.natDegree_mul smallPolynomialNonzero cofactorNonzero,
    natDegree_toPolynomial largeNonzero,
    natDegree_toPolynomial input.nonzero] at degrees
  have smallDegreePositive : 0 < small.natDegree :=
    Nat.pos_of_ne_zero input.nonconstant
  have cofactorDegree : cofactor.natDegree = 0 := by
    omega
  have cofactorEq : cofactor = Polynomial.C (cofactor.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero cofactorDegree
  have coefficientNonzero : cofactor.coeff 0 ≠ 0 := by
    intro zero
    apply cofactorNonzero
    rw [cofactorEq, zero, map_zero]
  have evaluationIdentity (t : ℚ) :
      large.eval t = small.eval t * cofactor.coeff 0 := by
    have cofactorEvaluation :
        Polynomial.eval t cofactor = cofactor.coeff 0 := by
      conv_lhs => rw [cofactorEq]
      rw [Polynomial.eval_C]
    calc
      large.eval t = Polynomial.eval t large.toPolynomial :=
        (eval_toPolynomial large t).symm
      _ = Polynomial.eval t (small.toPolynomial * cofactor) := by
        rw [identity]
      _ = small.eval t * Polynomial.eval t cofactor := by
        rw [Polynomial.eval_mul, eval_toPolynomial]
      _ = small.eval t * cofactor.coeff 0 := by rw [cofactorEvaluation]
  calc
    0 < (small.eval left * small.eval right) *
        (cofactor.coeff 0 * cofactor.coeff 0) :=
      mul_pos smallSign (mul_self_pos.mpr coefficientNonzero)
    _ = large.eval left * large.eval right := by
      rw [evaluationIdentity left, evaluationIdentity right]
      ring

theorem NarrowEventApproximation.divisorSmall
    {small : RatPolynomial} {input : SquarefreeInput small}
    {root : CountOneInterval small} {epsilon : ℚ}
    (approximation : NarrowEventApproximation input root epsilon) :
    |small.eval approximation.refined.interval.lower| ≤
      approximationSlope small root * epsilon := by
  let magnitude := approximationMagnitude root
  have magnitudeNonnegative : 0 ≤ magnitude :=
    (intervalMagnitude_pos root.interval.lower root.interval.upper).le
  have lowerMagnitude : |approximation.refined.interval.lower| ≤ magnitude :=
    abs_le_intervalMagnitude
      (approximation.refines.1.trans le_rfl)
      (approximation.refined.proper.le.trans approximation.refines.2)
  have upperMagnitude : |approximation.refined.interval.upper| ≤ magnitude :=
    abs_le_intervalMagnitude
      (approximation.refines.1.trans approximation.refined.proper.le)
      (le_rfl.trans approximation.refines.2)
  have divisorDifference := abs_dense_eval_sub_eval_le_dense small
    magnitudeNonnegative lowerMagnitude upperMagnitude
  have parameterDifference :
      |approximation.refined.interval.lower -
          approximation.refined.interval.upper| =
        approximation.refined.interval.width := by
    rw [abs_of_neg (sub_neg.mpr approximation.refined.proper)]
    simp [RationalInterval.width]
  calc
    |small.eval approximation.refined.interval.lower| ≤
        |small.eval approximation.refined.interval.lower -
          small.eval approximation.refined.interval.upper| :=
      abs_left_le_abs_sub_of_mul_neg approximation.crossing
    _ ≤ approximationSlope small root *
        |approximation.refined.interval.lower -
          approximation.refined.interval.upper| := divisorDifference
    _ = approximationSlope small root *
        approximation.refined.interval.width := by rw [parameterDifference]
    _ ≤ approximationSlope small root * epsilon :=
      mul_le_mul_of_nonneg_left approximation.width
        (denseHornerBounds_nonneg small magnitudeNonnegative).2

/-- The same crossing argument bounds the divisor at every rational point of
the refined count-one interval, not only at its lower endpoint.  Whichever
sign the queried value has, one of the two opposite-sign endpoints supplies
the Lipschitz comparison. -/
theorem NarrowEventApproximation.divisorSmallAt
    {small : RatPolynomial} {input : SquarefreeInput small}
    {root : CountOneInterval small} {epsilon : ℚ}
    (approximation : NarrowEventApproximation input root epsilon)
    {t : ℚ} (lower : approximation.refined.interval.lower ≤ t)
    (upper : t ≤ approximation.refined.interval.upper) :
    |small.eval t| ≤ approximationSlope small root * epsilon := by
  let magnitude := approximationMagnitude root
  let slope := approximationSlope small root
  have magnitudeNonnegative : 0 ≤ magnitude :=
    (intervalMagnitude_pos root.interval.lower root.interval.upper).le
  have tMagnitude : |t| ≤ magnitude :=
    abs_le_intervalMagnitude
      (approximation.refines.1.trans lower)
      (upper.trans approximation.refines.2)
  have lowerMagnitude : |approximation.refined.interval.lower| ≤ magnitude :=
    abs_le_intervalMagnitude approximation.refines.1
      (approximation.refined.proper.le.trans approximation.refines.2)
  have upperMagnitude : |approximation.refined.interval.upper| ≤ magnitude :=
    abs_le_intervalMagnitude
      (approximation.refines.1.trans approximation.refined.proper.le)
      approximation.refines.2
  have slopeNonnegative : 0 ≤ slope :=
    (denseHornerBounds_nonneg small magnitudeNonnegative).2
  have compareAt
      (s : ℚ) (sMagnitude : |s| ≤ magnitude)
      (sLower : approximation.refined.interval.lower ≤ s)
      (sUpper : s ≤ approximation.refined.interval.upper)
      (opposite : small.eval t * small.eval s < 0) :
      |small.eval t| ≤ slope * epsilon := by
    have difference := abs_dense_eval_sub_eval_le_dense small
      magnitudeNonnegative tMagnitude sMagnitude
    have distanceWidth : |t - s| ≤ approximation.refined.interval.width := by
      rw [abs_le]
      constructor
      · dsimp only [RationalInterval.width]
        linarith
      · dsimp only [RationalInterval.width]
        linarith
    calc
      |small.eval t| ≤ |small.eval t - small.eval s| :=
        abs_left_le_abs_sub_of_mul_neg opposite
      _ ≤ slope * |t - s| := by
        simpa [slope, approximationSlope, approximationMagnitude,
          magnitude] using difference
      _ ≤ slope * approximation.refined.interval.width :=
        mul_le_mul_of_nonneg_left distanceWidth slopeNonnegative
      _ ≤ slope * epsilon :=
        mul_le_mul_of_nonneg_left approximation.width slopeNonnegative
  rcases mul_neg_iff.mp approximation.crossing with
      ⟨lowerPositive, upperNegative⟩ | ⟨lowerNegative, upperPositive⟩
  · by_cases valuePositive : 0 < small.eval t
    · exact compareAt approximation.refined.interval.upper upperMagnitude
        approximation.refined.proper.le le_rfl
          (mul_neg_of_pos_of_neg valuePositive upperNegative)
    · by_cases valueNegative : small.eval t < 0
      · exact compareAt approximation.refined.interval.lower lowerMagnitude
          le_rfl approximation.refined.proper.le
            (mul_neg_of_neg_of_pos valueNegative lowerPositive)
      · have valueZero : small.eval t = 0 := by linarith
        rw [valueZero, abs_zero]
        exact mul_nonneg slopeNonnegative
          ((RationalInterval.width_pos approximation.refined.proper).le.trans
            approximation.width)
  · by_cases valuePositive : 0 < small.eval t
    · exact compareAt approximation.refined.interval.lower lowerMagnitude
        le_rfl approximation.refined.proper.le
          (mul_neg_of_pos_of_neg valuePositive lowerNegative)
    · by_cases valueNegative : small.eval t < 0
      · exact compareAt approximation.refined.interval.upper upperMagnitude
          approximation.refined.proper.le le_rfl
            (mul_neg_of_neg_of_pos valueNegative upperPositive)
      · have valueZero : small.eval t = 0 := by linarith
        rw [valueZero, abs_zero]
        exact mul_nonneg slopeNonnegative
          ((RationalInterval.width_pos approximation.refined.proper).le.trans
            approximation.width)

theorem eval_eq_mul_divMod_quotient_of_dvd
    {small large : RatPolynomial}
    (smallNonzero : small.isZero = false)
    (divides : small.toPolynomial ∣ large.toPolynomial) (t : ℚ) :
    large.eval t = small.eval t * (divMod large small).quotient.eval t := by
  have remainderZero : (divMod large small).remainder.isZero = true :=
    remainder_isZero_of_toPolynomial_dvd smallNonzero divides
  have division := divMod_eval_equation large small t
  rw [eval_eq_zero_of_isZero remainderZero, zero_add] at division
  exact division.symm

theorem NarrowEventApproximation.quotientSmall
    {small large : RatPolynomial} {input : SquarefreeInput small}
    {root : CountOneInterval small} {epsilon : ℚ}
    (approximation : NarrowEventApproximation input root epsilon) :
    |(divMod large small).quotient.eval
        approximation.refined.interval.lower| ≤
      approximationQuotientBound large small root := by
  apply abs_dense_eval_le_denseEvalAbsBound
  · exact (intervalMagnitude_pos root.interval.lower root.interval.upper).le
  · apply abs_le_intervalMagnitude
    · exact approximation.refines.1
    · exact approximation.refined.proper.le.trans approximation.refines.2

theorem NarrowEventApproximation.quotientSmallAt
    {small large : RatPolynomial} {input : SquarefreeInput small}
    {root : CountOneInterval small} {epsilon : ℚ}
    (approximation : NarrowEventApproximation input root epsilon)
    {t : ℚ} (lower : approximation.refined.interval.lower ≤ t)
    (upper : t ≤ approximation.refined.interval.upper) :
    |(divMod large small).quotient.eval t| ≤
      approximationQuotientBound large small root := by
  apply abs_dense_eval_le_denseEvalAbsBound
  · exact (intervalMagnitude_pos root.interval.lower
      root.interval.upper).le
  · exact abs_le_intervalMagnitude
      (approximation.refines.1.trans lower)
      (upper.trans approximation.refines.2)

theorem NarrowEventApproximation.multipleSmall
    {small large : RatPolynomial} {input : SquarefreeInput small}
    {root : CountOneInterval small} {epsilon : ℚ}
    (approximation : NarrowEventApproximation input root epsilon)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (epsilonNonnegative : 0 ≤ epsilon) :
    |large.eval approximation.refined.interval.lower| ≤
      approximationBound large small root epsilon := by
  rw [eval_eq_mul_divMod_quotient_of_dvd input.nonzero divides, abs_mul]
  exact mul_le_mul approximation.divisorSmall approximation.quotientSmall
    (abs_nonneg _)
    (mul_nonneg
      (denseHornerBounds_nonneg small
        (intervalMagnitude_pos root.interval.lower root.interval.upper).le).2
      epsilonNonnegative)

/-- Every point of the refined event interval makes any displayed polynomial
multiple uniformly small. -/
theorem NarrowEventApproximation.multipleSmallAt
    {small large : RatPolynomial} {input : SquarefreeInput small}
    {root : CountOneInterval small} {epsilon : ℚ}
    (approximation : NarrowEventApproximation input root epsilon)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (epsilonNonnegative : 0 ≤ epsilon)
    {t : ℚ} (lower : approximation.refined.interval.lower ≤ t)
    (upper : t ≤ approximation.refined.interval.upper) :
    |large.eval t| ≤ approximationBound large small root epsilon := by
  rw [eval_eq_mul_divMod_quotient_of_dvd input.nonzero divides, abs_mul]
  exact mul_le_mul (approximation.divisorSmallAt lower upper)
    (approximation.quotientSmallAt lower upper) (abs_nonneg _)
      (mul_nonneg
        (denseHornerBounds_nonneg small
          (intervalMagnitude_pos root.interval.lower root.interval.upper).le).2
        epsilonNonnegative)

/-- Narrow a count-one factor below a requested rational width, use its
opposite endpoint signs to make the divisor small at a rational endpoint, and
transfer that estimate through exact dense divisibility. -/
def approximateMultiple
    {small large : RatPolynomial} (input : SquarefreeInput small)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (root : CountOneInterval small) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    MultipleApproximation large small root epsilon := by
  let approximation := narrowEventApproximation input root epsilon
    epsilonPositive
  refine
    { parameter := approximation.refined.interval.lower
      lower := approximation.refines.1
      upper := approximation.refined.proper.le.trans approximation.refines.2
      smallValue := ?_ }
  exact approximation.multipleSmall divides epsilonPositive.le

/-! ## Whole-neighborhood smallness for a polynomial multiple -/

/-- Positive requested width making the displayed polynomial multiple smaller
than half of a supplied positive margin throughout the refined event cell. -/
def multipleNeighborhoodWidth
    (large small : RatPolynomial) (root : CountOneInterval small)
    (margin : ℚ) : ℚ :=
  margin / (2 * max 1 (approximationCoefficient large small root))

theorem multipleNeighborhoodWidth_pos
    (large small : RatPolynomial) (root : CountOneInterval small)
    {margin : ℚ} (marginPositive : 0 < margin) :
    0 < multipleNeighborhoodWidth large small root margin :=
  div_pos marginPositive (mul_pos (by norm_num)
    (zero_lt_one.trans_le (le_max_left _ _)))

/-- Computed count-one refinement on which the selected multiple is uniformly
small. -/
def narrowMultipleNeighborhood
    {small : RatPolynomial} (input : SquarefreeInput small)
    (large : RatPolynomial) (root : CountOneInterval small)
    (margin : ℚ) (marginPositive : 0 < margin) :
    NarrowEventApproximation input root
      (multipleNeighborhoodWidth large small root margin) :=
  narrowEventApproximation input root
    (multipleNeighborhoodWidth large small root margin)
      (multipleNeighborhoodWidth_pos large small root marginPositive)

theorem narrowMultipleNeighborhood_abs_lt
    {small large : RatPolynomial} (input : SquarefreeInput small)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (root : CountOneInterval small) {margin : ℚ}
    (marginPositive : 0 < margin) {t : ℚ}
    (lower : (narrowMultipleNeighborhood input large root margin
      marginPositive).refined.interval.lower ≤ t)
    (upper : t ≤ (narrowMultipleNeighborhood input large root margin
      marginPositive).refined.interval.upper) :
    |large.eval t| < margin := by
  let coefficient := approximationCoefficient large small root
  let scale := max 1 coefficient
  let width := multipleNeighborhoodWidth large small root margin
  let neighborhood := narrowMultipleNeighborhood input large root margin
    marginPositive
  have coefficientNonnegative : 0 ≤ coefficient :=
    approximationCoefficient_nonneg large small root
  have coefficientLe : coefficient ≤ scale := le_max_right _ _
  have scalePositive : 0 < scale := zero_lt_one.trans_le (le_max_left _ _)
  have widthPositive : 0 < width :=
    multipleNeighborhoodWidth_pos large small root marginPositive
  have smallBound := neighborhood.multipleSmallAt divides widthPositive.le
    (by simpa only [neighborhood] using lower)
    (by simpa only [neighborhood] using upper)
  have coefficientBound :
      approximationBound large small root width ≤ scale * width := by
    rw [approximationBound_eq_coefficient_mul]
    exact mul_le_mul_of_nonneg_right coefficientLe widthPositive.le
  have scaleWidth : scale * width = margin / 2 := by
    dsimp only [width, multipleNeighborhoodWidth, scale, coefficient]
    field_simp
  calc
    |large.eval t| ≤ approximationBound large small root width := by
      simpa only [neighborhood, width] using smallBound
    _ ≤ scale * width := coefficientBound
    _ = margin / 2 := scaleWidth
    _ < margin := by linarith

/-- A squarefree count-one interval cannot carry a uniform positive squared
lower bound for its defining polynomial.  This is the rational substitute
for realizing the isolated algebraic root: finite count-one refinement makes
one endpoint value smaller than any displayed positive certificate. -/
theorem CountOneInterval.no_positiveLowerBound
    {p : RatPolynomial} (input : SquarefreeInput p)
    (root : CountOneInterval p)
    (certificate : FTA.PositiveLowerBound.Certificate p root.interval) :
    False := by
  let slope := approximationSlope p root
  let scale := max 1 slope
  let margin := min 1 certificate.bound
  let epsilon := margin / (4 * scale)
  have scalePositive : 0 < scale :=
    zero_lt_one.trans_le (le_max_left _ _)
  have slopeNonnegative : 0 ≤ slope := by
    exact (denseHornerBounds_nonneg p
      (intervalMagnitude_pos root.interval.lower root.interval.upper).le).2
  have slopeLeScale : slope ≤ scale := le_max_right _ _
  have marginPositive : 0 < margin := lt_min zero_lt_one certificate.positive
  have marginLeOne : margin ≤ 1 := min_le_left _ _
  have marginLeBound : margin ≤ certificate.bound := min_le_right _ _
  have epsilonPositive : 0 < epsilon :=
    div_pos marginPositive (mul_pos (by norm_num) scalePositive)
  let approximation := narrowEventApproximation input root epsilon
    epsilonPositive
  have small := approximation.divisorSmall
  have endpointLower := certificate.lower
    approximation.refined.interval.lower approximation.refines.1
    (approximation.refined.proper.le.trans approximation.refines.2)
  have scaled : slope * epsilon ≤ margin / 4 := by
    unfold epsilon
    apply (mul_le_mul_of_nonneg_right slopeLeScale
      (div_nonneg marginPositive.le
        (mul_pos (by norm_num) scalePositive).le)).trans_eq
    field_simp
  have absSmall : |p.eval approximation.refined.interval.lower| ≤
      margin / 4 := small.trans scaled
  have squareSmall :
      p.eval approximation.refined.interval.lower ^ 2 < margin := by
    have squareIdentity :
        p.eval approximation.refined.interval.lower ^ 2 =
          |p.eval approximation.refined.interval.lower| ^ 2 := by
      rw [sq_abs]
    rw [squareIdentity]
    nlinarith [abs_nonneg (p.eval approximation.refined.interval.lower)]
  exact (not_lt_of_ge endpointLower) (squareSmall.trans_le marginLeBound)

/-- No polynomial multiple of a squarefree count-one factor can carry a
uniform positive squared lower bound on the represented interval. -/
theorem CountOneInterval.no_positiveLowerBound_of_dvd
    {small large : RatPolynomial} (input : SquarefreeInput small)
    (root : CountOneInterval small)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (certificate : FTA.PositiveLowerBound.Certificate large root.interval) :
    False := by
  let coefficient := approximationCoefficient large small root
  let scale := max 1 coefficient
  let margin := min 1 certificate.bound
  let epsilon := margin / (4 * scale)
  have coefficientNonnegative : 0 ≤ coefficient :=
    approximationCoefficient_nonneg large small root
  have scalePositive : 0 < scale :=
    zero_lt_one.trans_le (le_max_left _ _)
  have coefficientLeScale : coefficient ≤ scale := le_max_right _ _
  have marginPositive : 0 < margin := lt_min zero_lt_one certificate.positive
  have marginLeOne : margin ≤ 1 := min_le_left _ _
  have marginLeBound : margin ≤ certificate.bound := min_le_right _ _
  have epsilonPositive : 0 < epsilon :=
    div_pos marginPositive (mul_pos (by norm_num) scalePositive)
  let approximation := approximateMultiple input divides root epsilon
    epsilonPositive
  have endpointLower := certificate.lower approximation.parameter
    approximation.lower approximation.upper
  have scaled : coefficient * epsilon ≤ margin / 4 := by
    unfold epsilon
    apply (mul_le_mul_of_nonneg_right coefficientLeScale
      (div_nonneg marginPositive.le
        (mul_pos (by norm_num) scalePositive).le)).trans_eq
    field_simp
  have absSmall : |large.eval approximation.parameter| ≤ margin / 4 := by
    apply approximation.smallValue.trans
    rw [approximationBound_eq_coefficient_mul]
    exact scaled
  have squareSmall : large.eval approximation.parameter ^ 2 < margin := by
    have squareIdentity : large.eval approximation.parameter ^ 2 =
        |large.eval approximation.parameter| ^ 2 := by
      rw [sq_abs]
    rw [squareIdentity]
    nlinarith [abs_nonneg (large.eval approximation.parameter)]
  exact (not_lt_of_ge endpointLower) (squareSmall.trans_le marginLeBound)

/-- A squarefree count-one divisor on a nested cell contributes positively to
the executable multiplicity-sensitive root count of every nonzero multiple
on a clear ambient interval. -/
theorem factorRootCount2_pos_of_dvd_countOne_refines
    {small large : RatPolynomial} (input : SquarefreeInput small)
    (largeNonzero : large.isZero = false)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (ambient : RationalInterval) (ambientProper : ambient.Proper)
    (largeLower : large.eval ambient.lower ≠ 0)
    (largeUpper : large.eval ambient.upper ≠ 0)
    (root : CountOneInterval small)
    (rootRefines : root.interval.Refines ambient) :
    0 < factorRootCount2 large largeNonzero
      ambient.lower ambient.upper := by
  have countNonnegative := factorRootCount2_nonnegative largeNonzero
    ambientProper largeLower largeUpper
  apply lt_of_le_of_ne countNonnegative
  intro countZero
  let certificate := computeFromFactorCount largeNonzero ambient
    ambientProper largeLower largeUpper countZero.symm
  let quotient := (divMod large small).quotient
  let magnitude := intervalMagnitude ambient.lower ambient.upper
  let slope := denseEvalLipschitzBound small magnitude
  let quotientBound := denseEvalAbsBound quotient magnitude
  let scale := max 1 ((slope * quotientBound) ^ 2)
  let epsilon := min 1 certificate.bound / (4 * scale)
  have magnitudeNonnegative : 0 ≤ magnitude :=
    (intervalMagnitude_pos ambient.lower ambient.upper).le
  have slopeNonnegative : 0 ≤ slope :=
    (denseHornerBounds_nonneg small magnitudeNonnegative).2
  have quotientBoundNonnegative : 0 ≤ quotientBound :=
    (denseHornerBounds_nonneg quotient magnitudeNonnegative).1
  have scalePositive : 0 < scale :=
    zero_lt_one.trans_le (le_max_left _ _)
  have epsilonPositive : 0 < epsilon := by
    apply div_pos
    · exact lt_min zero_lt_one certificate.positive
    · positivity
  let narrow := runToWidth input (computedEventPartitionProgram input) root
    epsilon epsilonPositive
  let signs := computeCommonEventSigns input [] narrow
  have signsRefineRoot : signs.refined.interval.Refines root.interval :=
    RationalInterval.refines_trans signs.refines
      (runToWidth_refines input (computedEventPartitionProgram input) root
        epsilon epsilonPositive)
  have signsRefineAmbient : signs.refined.interval.Refines ambient :=
    RationalInterval.refines_trans signsRefineRoot rootRefines
  have widthBound : signs.refined.interval.width ≤ epsilon :=
    (show signs.refined.interval.width ≤ narrow.interval.width by
      dsimp only [RationalInterval.width]
      linarith [signs.refines.1, signs.refines.2]).trans
        (runToWidth_le input (computedEventPartitionProgram input) root
          epsilon epsilonPositive)
  have lowerMagnitude : |signs.refined.interval.lower| ≤ magnitude :=
    abs_le_intervalMagnitude
      (signsRefineAmbient.1.trans le_rfl)
      (signs.refined.proper.le.trans signsRefineAmbient.2)
  have upperMagnitude : |signs.refined.interval.upper| ≤ magnitude :=
    abs_le_intervalMagnitude
      (signsRefineAmbient.1.trans signs.refined.proper.le)
      (le_rfl.trans signsRefineAmbient.2)
  have divisorDifference := abs_dense_eval_sub_eval_le_dense small
    magnitudeNonnegative lowerMagnitude upperMagnitude
  have parameterDifference :
      |signs.refined.interval.lower - signs.refined.interval.upper| =
        signs.refined.interval.width := by
    rw [abs_of_neg (sub_neg.mpr signs.refined.proper)]
    simp [RationalInterval.width]
  have divisorSmall : |small.eval signs.refined.interval.lower| ≤
      slope * epsilon := by
    calc
      |small.eval signs.refined.interval.lower| ≤
          |small.eval signs.refined.interval.lower -
            small.eval signs.refined.interval.upper| :=
        abs_left_le_abs_sub_of_mul_neg signs.crossing
      _ ≤ slope *
          |signs.refined.interval.lower - signs.refined.interval.upper| :=
        divisorDifference
      _ = slope * signs.refined.interval.width := by
        rw [parameterDifference]
      _ ≤ slope * epsilon :=
        mul_le_mul_of_nonneg_left widthBound slopeNonnegative
  have quotientSmall : |quotient.eval signs.refined.interval.lower| ≤
      quotientBound :=
    abs_dense_eval_le_denseEvalAbsBound quotient magnitudeNonnegative
      lowerMagnitude
  have remainderZero : (divMod large small).remainder.isZero = true :=
    remainder_isZero_of_toPolynomial_dvd input.nonzero divides
  have largeIdentity : large.eval signs.refined.interval.lower =
      small.eval signs.refined.interval.lower *
        quotient.eval signs.refined.interval.lower := by
    have division := divMod_eval_equation large small
      signs.refined.interval.lower
    rw [eval_eq_zero_of_isZero remainderZero, zero_add] at division
    exact division.symm
  have largeAbs : |large.eval signs.refined.interval.lower| ≤
      slope * epsilon * quotientBound := by
    rw [largeIdentity, abs_mul]
    exact mul_le_mul divisorSmall quotientSmall (abs_nonneg _)
      (mul_nonneg slopeNonnegative epsilonPositive.le)
  have lowerInAmbient : ambient.lower ≤ signs.refined.interval.lower :=
    signsRefineAmbient.1
  have upperInAmbient : signs.refined.interval.lower ≤ ambient.upper :=
    signs.refined.proper.le.trans signsRefineAmbient.2
  have certificateLower := certificate.lower signs.refined.interval.lower
    lowerInAmbient upperInAmbient
  have largeSquareUpper : large.eval signs.refined.interval.lower ^ 2 ≤
      (slope * epsilon * quotientBound) ^ 2 := by
    calc
      large.eval signs.refined.interval.lower ^ 2 =
          |large.eval signs.refined.interval.lower| ^ 2 :=
        (sq_abs _).symm
      _ ≤ (slope * epsilon * quotientBound) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) largeAbs 2
  have scaleDominates : (slope * quotientBound) ^ 2 ≤ scale :=
    le_max_right _ _
  have epsilonLeOne : epsilon ≤ 1 := by
    dsimp only [epsilon]
    have numeratorLeOne : min 1 certificate.bound ≤ 1 := min_le_left _ _
    have denominatorGeOne : 1 ≤ 4 * scale := by
      nlinarith [le_max_left (1 : ℚ) ((slope * quotientBound) ^ 2)]
    exact (div_le_one (by positivity)).2
      (numeratorLeOne.trans denominatorGeOne)
  have scaledSmall : (slope * epsilon * quotientBound) ^ 2 <
      certificate.bound := by
    have numeratorPositive : 0 < min 1 certificate.bound :=
      lt_min zero_lt_one certificate.positive
    have epsilonEquation : 4 * scale * epsilon =
        min 1 certificate.bound := by
      dsimp only [epsilon]
      field_simp
    have boundLe : min 1 certificate.bound ≤ certificate.bound :=
      min_le_right _ _
    have epsilonNonnegative : 0 ≤ epsilon := epsilonPositive.le
    calc
      (slope * epsilon * quotientBound) ^ 2 =
          (slope * quotientBound) ^ 2 * epsilon ^ 2 := by ring
      _ ≤ scale * epsilon ^ 2 :=
        mul_le_mul_of_nonneg_right scaleDominates (sq_nonneg epsilon)
      _ ≤ scale * epsilon := by
        nlinarith
      _ < min 1 certificate.bound := by
        nlinarith
      _ ≤ certificate.bound := boundLe
  exact (not_lt_of_ge certificateLower)
    (largeSquareUpper.trans_lt scaledSmall)

/-- Same-interval specialization of the nested divisibility transfer. -/
theorem factorRootCount2_pos_of_dvd_countOne
    {small large : RatPolynomial} (input : SquarefreeInput small)
    (largeNonzero : large.isZero = false)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (root : CountOneInterval small)
    (largeLower : large.eval root.interval.lower ≠ 0)
    (largeUpper : large.eval root.interval.upper ≠ 0) :
    0 < factorRootCount2 large largeNonzero
      root.interval.lower root.interval.upper :=
  factorRootCount2_pos_of_dvd_countOne_refines input largeNonzero divides
    root.interval root.proper largeLower largeUpper root
    (RationalInterval.refines_refl root.interval)

/-! ## Uniqueness of a divisor root inside a count-one parent -/

/-- A common-sign refinement aligning a squarefree divisor's count-one cell
with a count-one cell for its squarefree multiple.  The two stored cells have
definitionally the same rational interval, and zeros agree throughout it. -/
structure DivisorCountOneAlignment
    {small large : RatPolynomial}
    (largeRoot : CountOneInterval large)
    (smallRoot : CountOneInterval small) where
  refined : CountOneInterval small
  refinesSmall : refined.interval.Refines smallRoot.interval
  multiple : CountOneInterval large
  sameInterval : multiple.interval = refined.interval
  refinesLarge : multiple.interval.Refines largeRoot.interval
  zero_iff : ∀ {t : ℚ}, refined.interval.lower ≤ t →
    t ≤ refined.interval.upper → (small.eval t = 0 ↔ large.eval t = 0)

/-- Construct the aligned divisor/multiple cell using only exact division,
squarefreeness, Bézout sign refinement, parity, and Sturm additivity. -/
def alignDivisorCountOne
    {small large : RatPolynomial}
    (smallInput : SquarefreeInput small)
    (largeInput : SquarefreeInput large)
    (largeRoot : CountOneInterval large)
    (smallRoot : CountOneInterval small)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (refines : smallRoot.interval.Refines largeRoot.interval) :
    DivisorCountOneAlignment largeRoot smallRoot := by
  let quotient := (divMod large small).quotient
  have remainderPolynomial :
      (divMod large small).remainder.toPolynomial = 0 := by
    exact (toPolynomial_eq_zero_iff_isZero _).2
      (divMod_remainder_isZero_of_toPolynomial_dvd smallInput.nonzero divides)
  have productPolynomial : large.toPolynomial =
      small.toPolynomial * quotient.toPolynomial := by
    calc
      large.toPolynomial = small.toPolynomial *
          (divMod large small).quotient.toPolynomial +
          (divMod large small).remainder.toPolynomial :=
        divMod_toPolynomial_equation large small
      _ = small.toPolynomial * quotient.toPolynomial := by
        rw [remainderPolynomial, add_zero]
  have largeSquarefree : Squarefree large.toPolynomial :=
    largeInput.squarefree.sparseSquarefree
  have productSquarefree :
      Squarefree (small.toPolynomial * quotient.toPolynomial) := by
    rw [← productPolynomial]
    exact largeSquarefree
  have quotientCoprimeSparse :
      IsCoprime small.toPolynomial quotient.toPolynomial :=
    (IsRelPrime.of_squarefree_mul productSquarefree).isCoprime
  let quotientCoprime := FTA.DenseSquarefree.certificateOfIsCoprime
    small quotient smallInput.nonzero quotientCoprimeSparse
  let quotientCondition : CoprimeCondition small :=
    { polynomial := quotient
      coprime := quotientCoprime }
  let signs := computeCommonEventSigns smallInput [quotientCondition]
    smallRoot
  have signsRefineLarge : signs.refined.interval.Refines largeRoot.interval :=
    RationalInterval.refines_trans signs.refines refines
  have quotientSign := signs.signs quotientCondition (by simp)
  have largeLowerClear : large.eval signs.refined.interval.lower ≠ 0 := by
    rw [eval_eq_mul_divMod_quotient_of_dvd smallInput.nonzero divides]
    exact mul_ne_zero signs.refined.lowerClear
      (quotientSign.eval_ne_zero le_rfl signs.refined.proper.le)
  have largeUpperClear : large.eval signs.refined.interval.upper ≠ 0 := by
    rw [eval_eq_mul_divMod_quotient_of_dvd smallInput.nonzero divides]
    exact mul_ne_zero signs.refined.upperClear
      (quotientSign.eval_ne_zero signs.refined.proper.le le_rfl)
  have middleNonnegative : 0 ≤ sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper :=
    (computedEventPartitionProgram largeInput).nonnegativeLaw
      signs.refined.proper largeLowerClear largeUpperClear
  have middleNonzero : sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper ≠ 0 := by
    intro middleZero
    let certificate := FTA.PositiveLowerBound.compute largeInput
      signs.refined.interval signs.refined.proper largeLowerClear
        largeUpperClear middleZero
    exact CountOneInterval.no_positiveLowerBound_of_dvd smallInput
      signs.refined divides certificate
  have middleEven : Even (sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper) :=
    sturmRootCount2_even largeInput.nonzero largeInput.nonconstant
      largeLowerClear largeUpperClear
  have middleAtLeastTwo : 2 ≤ sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper := by
    rcases middleEven with ⟨count, countEquation⟩
    omega
  have leftNonnegative : 0 ≤ sturmRootCount2 large
      largeRoot.interval.lower signs.refined.interval.lower := by
    rcases signsRefineLarge.1.eq_or_lt with equality | proper
    · rw [equality]
      simp
    · exact (computedEventPartitionProgram largeInput).nonnegativeLaw proper
        largeRoot.lowerClear largeLowerClear
  have rightNonnegative : 0 ≤ sturmRootCount2 large
      signs.refined.interval.upper largeRoot.interval.upper := by
    rcases signsRefineLarge.2.eq_or_lt with equality | proper
    · rw [← equality]
      simp
    · exact (computedEventPartitionProgram largeInput).nonnegativeLaw proper
        largeUpperClear largeRoot.upperClear
  have total :
      sturmRootCount2 large largeRoot.interval.lower
          signs.refined.interval.lower +
        sturmRootCount2 large signs.refined.interval.lower
          signs.refined.interval.upper +
        sturmRootCount2 large signs.refined.interval.upper
          largeRoot.interval.upper = 2 := by
    rw [add_assoc, sturmRootCount2_add, sturmRootCount2_add,
      largeRoot.countOne]
  have middleCountOne : sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper = 2 := by
    omega
  let multiple : CountOneInterval large :=
    { interval := signs.refined.interval
      proper := signs.refined.proper
      countOne := middleCountOne
      lowerClear := largeLowerClear
      upperClear := largeUpperClear }
  exact
    { refined := signs.refined
      refinesSmall := signs.refines
      multiple := multiple
      sameInterval := rfl
      refinesLarge := signsRefineLarge
      zero_iff := by
        intro t lower upper
        have quotientNonzero : quotient.eval t ≠ 0 :=
          quotientSign.eval_ne_zero lower upper
        constructor
        · intro smallZero
          rw [eval_eq_mul_divMod_quotient_of_dvd smallInput.nonzero divides,
            smallZero, zero_mul]
        · intro largeZero
          have productZero : small.eval t * quotient.eval t = 0 := by
            rw [← eval_eq_mul_divMod_quotient_of_dvd smallInput.nonzero divides]
            exact largeZero
          exact (mul_eq_zero.mp productZero).resolve_right quotientNonzero }

/-- A positive squared-value lower bound for a count-one polynomial at every
point of a parent count-one cell lying outside a nested count-one child. -/
structure CountOneComplementCertificate
    {p : RatPolynomial} (parent child : CountOneInterval p) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ {t : ℚ}, parent.interval.lower ≤ t →
    t ≤ parent.interval.upper →
    ¬(child.interval.lower ≤ t ∧ t ≤ child.interval.upper) →
      bound ≤ p.eval t ^ 2

/-- Compute the two zero-count side certificates left by a nested count-one
child and combine their bounds.  Degenerate sides are discharged by order,
so the result stays positive even when the child shares a parent endpoint. -/
def countOneComplementCertificate
    {p : RatPolynomial} (input : SquarefreeInput p)
    (parent child : CountOneInterval p)
    (refines : child.interval.Refines parent.interval) :
    CountOneComplementCertificate parent child := by
  have leftNonnegative : 0 ≤ sturmRootCount2 p parent.interval.lower
      child.interval.lower := by
    rcases refines.1.eq_or_lt with equality | proper
    · rw [equality]
      simp
    · exact (computedEventPartitionProgram input).nonnegativeLaw proper
        parent.lowerClear child.lowerClear
  have rightNonnegative : 0 ≤ sturmRootCount2 p child.interval.upper
      parent.interval.upper := by
    rcases refines.2.eq_or_lt with equality | proper
    · rw [← equality]
      simp
    · exact (computedEventPartitionProgram input).nonnegativeLaw proper
        child.upperClear parent.upperClear
  have total :
      sturmRootCount2 p parent.interval.lower child.interval.lower +
        sturmRootCount2 p child.interval.lower child.interval.upper +
        sturmRootCount2 p child.interval.upper parent.interval.upper = 2 := by
    rw [add_assoc, sturmRootCount2_add, sturmRootCount2_add,
      parent.countOne]
  have leftZero : sturmRootCount2 p parent.interval.lower
      child.interval.lower = 0 := by
    rw [child.countOne] at total
    omega
  have rightZero : sturmRootCount2 p child.interval.upper
      parent.interval.upper = 0 := by
    rw [child.countOne] at total
    omega
  by_cases leftProper : parent.interval.lower < child.interval.lower
  · let leftInterval : RationalInterval :=
      { lower := parent.interval.lower
        upper := child.interval.lower }
    let leftCertificate := FTA.PositiveLowerBound.compute input leftInterval
      leftProper parent.lowerClear child.lowerClear leftZero
    by_cases rightProper : child.interval.upper < parent.interval.upper
    · let rightInterval : RationalInterval :=
        { lower := child.interval.upper
          upper := parent.interval.upper }
      let rightCertificate := FTA.PositiveLowerBound.compute input
        rightInterval rightProper child.upperClear parent.upperClear rightZero
      exact
        { bound := min leftCertificate.bound rightCertificate.bound
          positive := lt_min leftCertificate.positive rightCertificate.positive
          lower := by
            intro t lower upper notInside
            have location : t < child.interval.lower ∨
                child.interval.upper < t := by
              by_contra neither
              apply notInside
              have notLeft : ¬t < child.interval.lower :=
                fun left => neither (Or.inl left)
              have notRight : ¬child.interval.upper < t :=
                fun right => neither (Or.inr right)
              exact ⟨le_of_not_gt notLeft, le_of_not_gt notRight⟩
            rcases location with left | right
            · exact (min_le_left _ _).trans
                (leftCertificate.lower t lower left.le)
            · exact (min_le_right _ _).trans
                (rightCertificate.lower t right.le upper) }
    · have rightEquality : child.interval.upper = parent.interval.upper :=
        le_antisymm refines.2 (le_of_not_gt rightProper)
      exact
        { bound := leftCertificate.bound
          positive := leftCertificate.positive
          lower := by
            intro t lower upper notInside
            have left : t < child.interval.lower := by
              by_contra notLeft
              apply notInside
              exact ⟨le_of_not_gt notLeft, by rw [rightEquality]; exact upper⟩
            exact leftCertificate.lower t lower left.le }
  · have leftEquality : parent.interval.lower = child.interval.lower :=
      le_antisymm refines.1 (le_of_not_gt leftProper)
    by_cases rightProper : child.interval.upper < parent.interval.upper
    · let rightInterval : RationalInterval :=
        { lower := child.interval.upper
          upper := parent.interval.upper }
      let rightCertificate := FTA.PositiveLowerBound.compute input
        rightInterval rightProper child.upperClear parent.upperClear rightZero
      exact
        { bound := rightCertificate.bound
          positive := rightCertificate.positive
          lower := by
            intro t lower upper notInside
            have right : child.interval.upper < t := by
              by_contra notRight
              apply notInside
              exact ⟨by rw [← leftEquality]; exact lower,
                le_of_not_gt notRight⟩
            exact rightCertificate.lower t right.le upper }
    · have rightEquality : child.interval.upper = parent.interval.upper :=
        le_antisymm refines.2 (le_of_not_gt rightProper)
      exact
        { bound := 1
          positive := zero_lt_one
          lower := by
            intro t lower upper notInside
            exact (notInside ⟨by rw [← leftEquality]; exact lower,
              by rw [rightEquality]; exact upper⟩).elim }

/-- A count-one interval for a squarefree divisor nested inside a count-one
interval for a squarefree multiple represents the same rational zero.  The
proof is entirely finite.  Squarefreeness makes the divisor coprime to its
exact quotient, so one common-sign refinement has clear endpoints for the
multiple.  The divisor makes the multiple's count there positive; parity,
nonnegativity, and additivity make it exactly one.  Ordinary rational-zero
retention for that multiple interval then proves both containment and
vanishing of the divisor. -/
theorem CountOneInterval.divisor_rationalZero_mem_of_refines
    {small large : RatPolynomial}
    (smallInput : SquarefreeInput small)
    (largeInput : SquarefreeInput large)
    (largeRoot : CountOneInterval large)
    (smallRoot : CountOneInterval small)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (refines : smallRoot.interval.Refines largeRoot.interval)
    {t : ℚ} (lower : largeRoot.interval.lower ≤ t)
    (upper : t ≤ largeRoot.interval.upper)
    (largeZero : large.eval t = 0) :
    smallRoot.interval.lower ≤ t ∧ t ≤ smallRoot.interval.upper ∧
      small.eval t = 0 := by
  let quotient := (divMod large small).quotient
  have remainderPolynomial :
      (divMod large small).remainder.toPolynomial = 0 := by
    exact (toPolynomial_eq_zero_iff_isZero _).2
      (divMod_remainder_isZero_of_toPolynomial_dvd smallInput.nonzero divides)
  have productPolynomial : large.toPolynomial =
      small.toPolynomial * quotient.toPolynomial := by
    calc
      large.toPolynomial = small.toPolynomial *
          (divMod large small).quotient.toPolynomial +
          (divMod large small).remainder.toPolynomial :=
        divMod_toPolynomial_equation large small
      _ = small.toPolynomial * quotient.toPolynomial := by
        rw [remainderPolynomial, add_zero]
  have largeSquarefree : Squarefree large.toPolynomial :=
    largeInput.squarefree.sparseSquarefree
  have productSquarefree :
      Squarefree (small.toPolynomial * quotient.toPolynomial) := by
    rw [← productPolynomial]
    exact largeSquarefree
  have quotientCoprimeSparse :
      IsCoprime small.toPolynomial quotient.toPolynomial :=
    (IsRelPrime.of_squarefree_mul productSquarefree).isCoprime
  let quotientCoprime := FTA.DenseSquarefree.certificateOfIsCoprime
    small quotient smallInput.nonzero quotientCoprimeSparse
  let quotientCondition : CoprimeCondition small :=
    { polynomial := quotient
      coprime := quotientCoprime }
  let signs := computeCommonEventSigns smallInput [quotientCondition]
    smallRoot
  have signsRefineSmall : signs.refined.interval.Refines smallRoot.interval :=
    signs.refines
  have signsRefineLarge : signs.refined.interval.Refines largeRoot.interval :=
    RationalInterval.refines_trans signsRefineSmall refines
  have quotientSign := signs.signs quotientCondition (by simp)
  have largeLowerClear : large.eval signs.refined.interval.lower ≠ 0 := by
    rw [eval_eq_mul_divMod_quotient_of_dvd smallInput.nonzero divides]
    exact mul_ne_zero signs.refined.lowerClear
      (quotientSign.eval_ne_zero le_rfl signs.refined.proper.le)
  have largeUpperClear : large.eval signs.refined.interval.upper ≠ 0 := by
    rw [eval_eq_mul_divMod_quotient_of_dvd smallInput.nonzero divides]
    exact mul_ne_zero signs.refined.upperClear
      (quotientSign.eval_ne_zero signs.refined.proper.le le_rfl)
  have middleNonnegative : 0 ≤ sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper :=
    (computedEventPartitionProgram largeInput).nonnegativeLaw
      signs.refined.proper largeLowerClear largeUpperClear
  have middleNonzero : sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper ≠ 0 := by
    intro middleZero
    let certificate := FTA.PositiveLowerBound.compute largeInput
      signs.refined.interval signs.refined.proper largeLowerClear
        largeUpperClear middleZero
    exact CountOneInterval.no_positiveLowerBound_of_dvd smallInput
      signs.refined divides certificate
  have middleEven : Even (sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper) :=
    sturmRootCount2_even largeInput.nonzero largeInput.nonconstant
      largeLowerClear largeUpperClear
  have middleAtLeastTwo : 2 ≤ sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper := by
    rcases middleEven with ⟨count, countEquation⟩
    omega
  have leftNonnegative : 0 ≤ sturmRootCount2 large
      largeRoot.interval.lower signs.refined.interval.lower := by
    rcases signsRefineLarge.1.eq_or_lt with equality | proper
    · rw [equality]
      simp
    · exact (computedEventPartitionProgram largeInput).nonnegativeLaw proper
        largeRoot.lowerClear largeLowerClear
  have rightNonnegative : 0 ≤ sturmRootCount2 large
      signs.refined.interval.upper largeRoot.interval.upper := by
    rcases signsRefineLarge.2.eq_or_lt with equality | proper
    · rw [← equality]
      simp
    · exact (computedEventPartitionProgram largeInput).nonnegativeLaw proper
        largeUpperClear largeRoot.upperClear
  have total :
      sturmRootCount2 large largeRoot.interval.lower
          signs.refined.interval.lower +
        sturmRootCount2 large signs.refined.interval.lower
          signs.refined.interval.upper +
        sturmRootCount2 large signs.refined.interval.upper
          largeRoot.interval.upper = 2 := by
    rw [add_assoc, sturmRootCount2_add, sturmRootCount2_add,
      largeRoot.countOne]
  have middleCountOne : sturmRootCount2 large
      signs.refined.interval.lower signs.refined.interval.upper = 2 := by
    omega
  let largeChild : CountOneInterval large :=
    { interval := signs.refined.interval
      proper := signs.refined.proper
      countOne := middleCountOne
      lowerClear := largeLowerClear
      upperClear := largeUpperClear }
  have tInside :=
    FTA.PositiveLowerBound.CountOneInterval.rationalZero_mem_of_refines
      largeInput largeRoot largeChild signsRefineLarge lower upper largeZero
  have quotientNonzeroAtT : quotient.eval t ≠ 0 :=
    quotientSign.eval_ne_zero tInside.1 tInside.2
  have smallZero : small.eval t = 0 := by
    have productZero : small.eval t * quotient.eval t = 0 := by
      rw [← eval_eq_mul_divMod_quotient_of_dvd smallInput.nonzero divides]
      exact largeZero
    exact (mul_eq_zero.mp productZero).resolve_right quotientNonzeroAtT
  exact ⟨signsRefineSmall.1.trans tInside.1,
    tInside.2.trans signsRefineSmall.2, smallZero⟩

/-- Vanishing-only projection of divisor-root uniqueness. -/
theorem CountOneInterval.divisor_eval_eq_zero_of_refines
    {small large : RatPolynomial}
    (smallInput : SquarefreeInput small)
    (largeInput : SquarefreeInput large)
    (largeRoot : CountOneInterval large)
    (smallRoot : CountOneInterval small)
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (refines : smallRoot.interval.Refines largeRoot.interval)
    {t : ℚ} (lower : largeRoot.interval.lower ≤ t)
    (upper : t ≤ largeRoot.interval.upper)
    (largeZero : large.eval t = 0) :
    small.eval t = 0 :=
  (FTA.RootCountDivisibility.CountOneInterval.divisor_rationalZero_mem_of_refines
    smallInput largeInput largeRoot smallRoot divides refines lower upper
      largeZero).2.2

end RootCountDivisibility
end FTA
