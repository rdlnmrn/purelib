import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Curve.BoxConditions
import RFAP.Sturm.IntervalSign
import RFAP.Sturm.EventPartition
import CCL.Geometry.Chordal

/-!
# Quantitative projective bounds for finite rational curves

The homogeneous numerator and denominator of a rational curve are ordinary
finite coordinate polynomials.  Componentwise Horner bounds therefore give
an explicit Lipschitz coefficient for their projective cross product.  Once
the denominator coordinates carry a positive Bézout clearance on a bounded
parameter interval, this becomes a squared-chordal image bound proportional
to the square of the parameter width.

No affine division, square root, completed point, or limiting argument is
used.  The result is the finite shrinking-cylinder estimate needed to compare
a persistent curve event with a simultaneously shrinking winding box.
-/

namespace CCL.RationalCurveBounds

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev RationalCurve := CCL.RationalCurve.RationalCurve
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval
abbrev DenominatorClearance := RFAP.PathClearance.Certificate
abbrev Proj := CCL.GaussianProjective.Proj

open RFAP.ConstructiveGaussian.Gaussian

def numeratorValueBound (curve : RationalCurve) (interval : Interval) :
    Coordinate :=
  RFAP.PathClearance.evalSqBound
      (CCL.CurveBoxConditions.numeratorReal curve) interval +
    RFAP.PathClearance.evalSqBound
      (CCL.CurveBoxConditions.numeratorImaginary curve) interval

def denominatorValueBound (curve : RationalCurve) (interval : Interval) :
    Coordinate :=
  RFAP.PathClearance.evalSqBound
      (CCL.CurveBoxConditions.denominatorReal curve) interval +
    RFAP.PathClearance.evalSqBound
      (CCL.CurveBoxConditions.denominatorImaginary curve) interval

def numeratorLipschitzBound (curve : RationalCurve) (interval : Interval) :
    Coordinate :=
  RFAP.IntervalSign.denseEvalSqLipschitzBound
      (CCL.CurveBoxConditions.numeratorReal curve) interval +
    RFAP.IntervalSign.denseEvalSqLipschitzBound
      (CCL.CurveBoxConditions.numeratorImaginary curve) interval

def denominatorLipschitzBound (curve : RationalCurve) (interval : Interval) :
    Coordinate :=
  RFAP.IntervalSign.denseEvalSqLipschitzBound
      (CCL.CurveBoxConditions.denominatorReal curve) interval +
    RFAP.IntervalSign.denseEvalSqLipschitzBound
      (CCL.CurveBoxConditions.denominatorImaginary curve) interval

/-- Coefficient for the homogeneous cross-product variation. -/
def crossVariationCoefficient (curve : RationalCurve) (interval : Interval) :
    Coordinate :=
  2 * (numeratorLipschitzBound curve interval *
      denominatorValueBound curve interval +
    numeratorValueBound curve interval *
      denominatorLipschitzBound curve interval)

/-- Coefficient for squared-chordal variation after dividing by the square
of a positive denominator clearance. -/
def chordalVariationCoefficient
    (curve : RationalCurve) (interval : Interval)
    (clearance : DenominatorClearance
      (CCL.CurveBoxConditions.denominatorReal curve)
      (CCL.CurveBoxConditions.denominatorImaginary curve)
      interval) : Coordinate :=
  crossVariationCoefficient curve interval / clearance.bound ^ 2

theorem numeratorValueBound_nonneg
    (curve : RationalCurve) (interval : Interval) :
    0 ≤ numeratorValueBound curve interval :=
  add_nonneg
    (RFAP.PathClearance.evalSqBound_nonneg _ _)
    (RFAP.PathClearance.evalSqBound_nonneg _ _)

theorem denominatorValueBound_nonneg
    (curve : RationalCurve) (interval : Interval) :
    0 ≤ denominatorValueBound curve interval :=
  add_nonneg
    (RFAP.PathClearance.evalSqBound_nonneg _ _)
    (RFAP.PathClearance.evalSqBound_nonneg _ _)

theorem numeratorLipschitzBound_nonneg
    (curve : RationalCurve) (interval : Interval) :
    0 ≤ numeratorLipschitzBound curve interval :=
  add_nonneg
    (RFAP.IntervalSign.denseHornerSqBounds_nonneg _ _).2
    (RFAP.IntervalSign.denseHornerSqBounds_nonneg _ _).2

theorem denominatorLipschitzBound_nonneg
    (curve : RationalCurve) (interval : Interval) :
    0 ≤ denominatorLipschitzBound curve interval :=
  add_nonneg
    (RFAP.IntervalSign.denseHornerSqBounds_nonneg _ _).2
    (RFAP.IntervalSign.denseHornerSqBounds_nonneg _ _).2

theorem crossVariationCoefficient_nonneg
    (curve : RationalCurve) (interval : Interval) :
    0 ≤ crossVariationCoefficient curve interval := by
  apply RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
  exact add_nonneg
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (numeratorLipschitzBound_nonneg curve interval)
      (denominatorValueBound_nonneg curve interval))
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (numeratorValueBound_nonneg curve interval)
      (denominatorLipschitzBound_nonneg curve interval))

theorem chordalVariationCoefficient_nonneg
    (curve : RationalCurve) (interval : Interval)
    (clearance : DenominatorClearance
      (CCL.CurveBoxConditions.denominatorReal curve)
      (CCL.CurveBoxConditions.denominatorImaginary curve)
      interval) :
    0 ≤ chordalVariationCoefficient curve interval clearance :=
  RFAP.ConstructiveFraction.div_nonneg_direct
    (crossVariationCoefficient_nonneg curve interval)
    (RFAP.ConstructiveFraction.sq_nonneg_direct clearance.bound)

theorem normSq_numeratorAt_le
    (curve : RationalCurve) (interval : Interval) {parameter : Coordinate}
    (inside : interval.Contains parameter) :
    normSq (curve.numeratorAt parameter) ≤
      numeratorValueBound curve interval := by
  have bounds := add_le_add
    (RFAP.PathClearance.eval_sq_le_evalSqBound
      (CCL.CurveBoxConditions.numeratorReal curve)
      interval inside)
    (RFAP.PathClearance.eval_sq_le_evalSqBound
      (CCL.CurveBoxConditions.numeratorImaginary curve)
      interval inside)
  simpa only [numeratorValueBound,
    CCL.CurveBoxConditions.numeratorReal,
    CCL.CurveBoxConditions.numeratorImaginary,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    CCL.RationalCurve.RationalCurve.numeratorAt, normSq] using
      bounds

theorem normSq_denominatorAt_le
    (curve : RationalCurve) (interval : Interval) {parameter : Coordinate}
    (inside : interval.Contains parameter) :
    normSq (curve.denominatorAt parameter) ≤
      denominatorValueBound curve interval := by
  have bounds := add_le_add
    (RFAP.PathClearance.eval_sq_le_evalSqBound
      (CCL.CurveBoxConditions.denominatorReal curve)
      interval inside)
    (RFAP.PathClearance.eval_sq_le_evalSqBound
      (CCL.CurveBoxConditions.denominatorImaginary curve)
      interval inside)
  simpa only [denominatorValueBound,
    CCL.CurveBoxConditions.denominatorReal,
    CCL.CurveBoxConditions.denominatorImaginary,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    CCL.RationalCurve.RationalCurve.denominatorAt, normSq] using
      bounds

theorem normSq_numeratorAt_sub_le
    (curve : RationalCurve) (interval : Interval) {left right : Coordinate}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    normSq (curve.numeratorAt left - curve.numeratorAt right) ≤
      numeratorLipschitzBound curve interval * (left - right) ^ 2 := by
  have bounds :
      ((CCL.CurveBoxConditions.numeratorReal curve).eval left -
          (CCL.CurveBoxConditions.numeratorReal curve).eval right) ^ 2 +
        ((CCL.CurveBoxConditions.numeratorImaginary curve).eval left -
          (CCL.CurveBoxConditions.numeratorImaginary curve).eval
            right) ^ 2 ≤
        numeratorLipschitzBound curve interval * (left - right) ^ 2 := calc
    _ ≤ RFAP.IntervalSign.denseEvalSqLipschitzBound
          (CCL.CurveBoxConditions.numeratorReal curve) interval *
            (left - right) ^ 2 +
        RFAP.IntervalSign.denseEvalSqLipschitzBound
          (CCL.CurveBoxConditions.numeratorImaginary curve) interval *
            (left - right) ^ 2 :=
      add_le_add
        (RFAP.IntervalSign.eval_sub_sq_le _ interval
          leftInside rightInside)
        (RFAP.IntervalSign.eval_sub_sq_le _ interval
          leftInside rightInside)
    _ = numeratorLipschitzBound curve interval * (left - right) ^ 2 := by
      dsimp only [numeratorLipschitzBound]
      ring1
  simpa only [CCL.CurveBoxConditions.numeratorReal,
    CCL.CurveBoxConditions.numeratorImaginary,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    CCL.RationalCurve.RationalCurve.numeratorAt, normSq,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im] using bounds

theorem normSq_denominatorAt_sub_le
    (curve : RationalCurve) (interval : Interval) {left right : Coordinate}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    normSq (curve.denominatorAt left - curve.denominatorAt right) ≤
      denominatorLipschitzBound curve interval * (left - right) ^ 2 := by
  have bounds :
      ((CCL.CurveBoxConditions.denominatorReal curve).eval left -
          (CCL.CurveBoxConditions.denominatorReal curve).eval right) ^ 2 +
        ((CCL.CurveBoxConditions.denominatorImaginary curve).eval left -
          (CCL.CurveBoxConditions.denominatorImaginary curve).eval
            right) ^ 2 ≤
        denominatorLipschitzBound curve interval * (left - right) ^ 2 := calc
    _ ≤ RFAP.IntervalSign.denseEvalSqLipschitzBound
          (CCL.CurveBoxConditions.denominatorReal curve) interval *
            (left - right) ^ 2 +
        RFAP.IntervalSign.denseEvalSqLipschitzBound
          (CCL.CurveBoxConditions.denominatorImaginary curve) interval *
            (left - right) ^ 2 :=
      add_le_add
        (RFAP.IntervalSign.eval_sub_sq_le _ interval
          leftInside rightInside)
        (RFAP.IntervalSign.eval_sub_sq_le _ interval
          leftInside rightInside)
    _ = denominatorLipschitzBound curve interval * (left - right) ^ 2 := by
      dsimp only [denominatorLipschitzBound]
      ring1
  simpa only [CCL.CurveBoxConditions.denominatorReal,
    CCL.CurveBoxConditions.denominatorImaginary,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    CCL.RationalCurve.RationalCurve.denominatorAt, normSq,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im] using bounds

/-- Homogeneous curve value at one displayed parameter. -/
def projective (curve : RationalCurve) (parameter : Coordinate) : Proj :=
  ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩

/-- Away from its displayed pole, a rational curve's homogeneous pair is
exactly equivalent to the affine point computed from that pair. -/
theorem projective_equivalent_affine
    (curve : RationalCurve) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (projective curve parameter).Equivalent
      (CCL.Proj.affine (curve.point parameter)) := by
  dsimp only [projective, CCL.Proj.Equivalent, CCL.Proj.affine]
  rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
  exact curve.numeratorAt_eq_point_mul_denominatorAt parameter
    denominatorNonzero

/-- Squared-chordal distance can therefore be transported exactly between a
non-pole curve parameter and its affine value. -/
theorem chordalSq_projective_eq_affine
    (curve : RationalCurve) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (other : Proj) :
    CCL.Chordal.chordalSq (projective curve parameter) other =
      CCL.Chordal.chordalSq
        (CCL.Proj.affine (curve.point parameter)) other := by
  exact CCL.Chordal.chordalSq_eq_of_equivalent_left
    (Or.inr denominatorNonzero)
    (CCL.Chordal.Proj.affine_hasNonzeroCoordinate
      (curve.point parameter))
    (projective_equivalent_affine curve parameter denominatorNonzero) other

theorem denominatorNormSq_lower
    (curve : RationalCurve) (interval : Interval)
    (clearance : DenominatorClearance
      (CCL.CurveBoxConditions.denominatorReal curve)
      (CCL.CurveBoxConditions.denominatorImaginary curve)
      interval)
    {parameter : Coordinate} (inside : interval.Contains parameter) :
    clearance.bound ≤ normSq (curve.denominatorAt parameter) := by
  simpa only [CCL.CurveBoxConditions.denominatorReal,
    CCL.CurveBoxConditions.denominatorImaginary,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    CCL.RationalCurve.RationalCurve.denominatorAt, normSq] using
      clearance.lower parameter inside

theorem denominatorAt_ne
    (curve : RationalCurve) (interval : Interval)
    (clearance : DenominatorClearance
      (CCL.CurveBoxConditions.denominatorReal curve)
      (CCL.CurveBoxConditions.denominatorImaginary curve)
      interval)
    {parameter : Coordinate} (inside : interval.Contains parameter) :
    curve.denominatorAt parameter ≠ 0 := by
  intro denominatorZero
  have lower := denominatorNormSq_lower curve interval clearance inside
  rw [denominatorZero, normSq_zero] at lower
  exact (not_lt_of_ge lower) clearance.positive

theorem projective_valid
    (curve : RationalCurve) (interval : Interval)
    (clearance : DenominatorClearance
      (CCL.CurveBoxConditions.denominatorReal curve)
      (CCL.CurveBoxConditions.denominatorImaginary curve)
      interval)
    {parameter : Coordinate} (inside : interval.Contains parameter) :
    CCL.Chordal.Proj.HasNonzeroCoordinate
      (projective curve parameter) :=
  Or.inr (denominatorAt_ne curve interval clearance inside)

/-- The projective cross product contracts quadratically with parameter
distance on a bounded interval. -/
theorem normSq_cross_le
    (curve : RationalCurve) (interval : Interval) {left right : Coordinate}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    normSq (CCL.Chordal.Proj.cross
      (projective curve left) (projective curve right)) ≤
      crossVariationCoefficient curve interval * (left - right) ^ 2 := by
  let leftNumerator := curve.numeratorAt left
  let rightNumerator := curve.numeratorAt right
  let leftDenominator := curve.denominatorAt left
  let rightDenominator := curve.denominatorAt right
  have crossIdentity :
      leftNumerator * rightDenominator - rightNumerator * leftDenominator =
        (leftNumerator - rightNumerator) * rightDenominator +
          rightNumerator * (rightDenominator - leftDenominator) := by
    symm
    calc
      (leftNumerator - rightNumerator) * rightDenominator +
            rightNumerator * (rightDenominator - leftDenominator) =
          (leftNumerator * rightDenominator +
              -(rightNumerator * rightDenominator)) +
            (rightNumerator * rightDenominator +
              -(rightNumerator * leftDenominator)) := by
        rw [RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg,
          RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg,
          RFAP.ConstructiveGaussian.Gaussian.right_distrib,
          RFAP.ConstructiveGaussian.Gaussian.left_distrib,
          _root_.neg_mul, _root_.mul_neg]
      _ = leftNumerator * rightDenominator +
          (-(rightNumerator * rightDenominator) +
            (rightNumerator * rightDenominator +
              -(rightNumerator * leftDenominator))) :=
        RFAP.ConstructiveGaussian.Gaussian.add_assoc _ _ _
      _ = leftNumerator * rightDenominator +
          ((-(rightNumerator * rightDenominator) +
              rightNumerator * rightDenominator) +
            -(rightNumerator * leftDenominator)) := by
        rw [RFAP.ConstructiveGaussian.Gaussian.add_assoc]
      _ = leftNumerator * rightDenominator +
          (0 + -(rightNumerator * leftDenominator)) := by
        rw [neg_add_cancel]
      _ = leftNumerator * rightDenominator +
          -(rightNumerator * leftDenominator) := by
        rw [RFAP.ConstructiveGaussian.Gaussian.zero_add]
      _ = leftNumerator * rightDenominator -
          rightNumerator * leftDenominator :=
        (RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg _ _).symm
  have firstBound :
      normSq ((leftNumerator - rightNumerator) * rightDenominator) ≤
        (numeratorLipschitzBound curve interval * (left - right) ^ 2) *
          denominatorValueBound curve interval := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (normSq_numeratorAt_sub_le curve interval leftInside rightInside)
      (normSq_denominatorAt_le curve interval rightInside)
      (normSq_nonneg rightDenominator)
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (numeratorLipschitzBound_nonneg curve interval)
        (RFAP.ConstructiveFraction.sq_nonneg_direct (left - right)))
  have secondBound :
      normSq (rightNumerator * (rightDenominator - leftDenominator)) ≤
        numeratorValueBound curve interval *
          (denominatorLipschitzBound curve interval * (left - right) ^ 2) := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (normSq_numeratorAt_le curve interval rightInside)
      (by
        have reversed := normSq_denominatorAt_sub_le curve interval
          leftInside rightInside
        have differenceIdentity :
            rightDenominator - leftDenominator =
              -(leftDenominator - rightDenominator) := by
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg,
            _root_.neg_add_rev, neg_neg]
        rw [differenceIdentity, normSq_neg]
        exact reversed)
      (normSq_nonneg (rightDenominator - leftDenominator))
      (numeratorValueBound_nonneg curve interval)
  change normSq
    (leftNumerator * rightDenominator - rightNumerator * leftDenominator) ≤ _
  rw [crossIdentity]
  calc
    normSq ((leftNumerator - rightNumerator) * rightDenominator +
        rightNumerator * (rightDenominator - leftDenominator)) ≤
      2 * (normSq ((leftNumerator - rightNumerator) * rightDenominator) +
        normSq (rightNumerator *
          (rightDenominator - leftDenominator))) :=
      normSq_add_le_two _ _
    _ ≤ 2 *
        ((numeratorLipschitzBound curve interval * (left - right) ^ 2) *
            denominatorValueBound curve interval +
          numeratorValueBound curve interval *
            (denominatorLipschitzBound curve interval *
              (left - right) ^ 2)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstBound secondBound) (by decide)
    _ = crossVariationCoefficient curve interval * (left - right) ^ 2 := by
      dsimp only [crossVariationCoefficient]
      ring1

/-- A denominator-cleared bounded parameter cell has an explicitly shrinking
squared-chordal image. -/
theorem chordalSq_projective_le
    (curve : RationalCurve) (interval : Interval)
    (clearance : DenominatorClearance
      (CCL.CurveBoxConditions.denominatorReal curve)
      (CCL.CurveBoxConditions.denominatorImaginary curve)
      interval)
    {left right : Coordinate}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    CCL.Chordal.chordalSq
        (projective curve left) (projective curve right) ≤
      chordalVariationCoefficient curve interval clearance *
        (left - right) ^ 2 := by
  let leftPoint := projective curve left
  let rightPoint := projective curve right
  let actualDenominator :=
    CCL.Chordal.Proj.weight leftPoint *
      CCL.Chordal.Proj.weight rightPoint
  let clearanceSq := clearance.bound ^ 2
  let upper := crossVariationCoefficient curve interval * (left - right) ^ 2
  have leftValid := projective_valid curve interval clearance leftInside
  have rightValid := projective_valid curve interval clearance rightInside
  have actualPositive : 0 < actualDenominator :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (CCL.Chordal.Proj.weight_pos leftValid)
      (CCL.Chordal.Proj.weight_pos rightValid)
  have clearanceSqPositive : 0 < clearanceSq :=
    RFAP.ConstructiveFraction.pow_pos_direct clearance.positive 2
  have leftWeightLower : clearance.bound ≤
      CCL.Chordal.Proj.weight leftPoint := by
    change clearance.bound ≤
      normSq (curve.numeratorAt left) + normSq (curve.denominatorAt left)
    exact (denominatorNormSq_lower curve interval clearance leftInside).trans
      (le_add_of_nonneg_left (normSq_nonneg (curve.numeratorAt left)))
  have rightWeightLower : clearance.bound ≤
      CCL.Chordal.Proj.weight rightPoint := by
    change clearance.bound ≤
      normSq (curve.numeratorAt right) + normSq (curve.denominatorAt right)
    exact (denominatorNormSq_lower curve interval clearance rightInside).trans
      (le_add_of_nonneg_left (normSq_nonneg (curve.numeratorAt right)))
  have actualLower : clearanceSq ≤ actualDenominator := by
    dsimp only [clearanceSq, actualDenominator]
    simpa only [pow_two] using
      (RFAP.ConstructiveFraction.mul_le_mul_direct
        leftWeightLower rightWeightLower clearance.positive.le
        (CCL.Chordal.Proj.weight_pos leftValid).le)
  have upperNonnegative : 0 ≤ upper :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (crossVariationCoefficient_nonneg curve interval)
      (RFAP.ConstructiveFraction.sq_nonneg_direct (left - right))
  calc
    CCL.Chordal.chordalSq leftPoint rightPoint =
        normSq (CCL.Chordal.Proj.cross leftPoint rightPoint) /
          actualDenominator := rfl
    _ ≤ upper / actualDenominator := by
      apply (RFAP.ConstructiveFraction.div_le_iff_pos actualPositive).2
      have cancel : upper / actualDenominator * actualDenominator = upper :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne upper actualDenominator
          actualPositive.ne'
      rw [cancel]
      exact normSq_cross_le curve interval leftInside rightInside
    _ ≤ upper / clearanceSq :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        upperNonnegative clearanceSqPositive actualLower
    _ = chordalVariationCoefficient curve interval clearance *
        (left - right) ^ 2 := by
      simp only [chordalVariationCoefficient,
        RFAP.ExplicitField.div_eq_mul_inv]
      rw [RFAP.ConstructiveFraction.mul_assoc,
        RFAP.ConstructiveFraction.mul_comm ((left - right) ^ 2),
        ← RFAP.ConstructiveFraction.mul_assoc]

/-- Any two parameters in a displayed interval differ by at most its width,
in the square-only form used by projective quadrance. -/
theorem parameter_sub_sq_le_width_sq
    (interval : Interval) {left right : Coordinate}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    (left - right) ^ 2 ≤
      (RFAP.SturmEventPartition.Interval.width interval) ^ 2 := by
  let width := RFAP.SturmEventPartition.Interval.width interval
  have lower : -width ≤ left - right := by
    dsimp only [width, RFAP.SturmEventPartition.Interval.width]
    calc
      -(interval.upper - interval.lower) =
          interval.lower + -interval.upper := by ring1
      _ ≤ left + -right := add_le_add leftInside.1
        (RFAP.ConstructiveFraction.neg_le_neg_direct rightInside.2)
      _ = left - right := by ring1
  have upper : left - right ≤ width := by
    dsimp only [width, RFAP.SturmEventPartition.Interval.width]
    calc
      left - right = left + -right := by ring1
      _ ≤ interval.upper + -interval.lower := add_le_add leftInside.2
        (RFAP.ConstructiveFraction.neg_le_neg_direct rightInside.1)
      _ = interval.upper - interval.lower := by ring1
  have square := RFAP.Boxes.Box.sq_le_endpoint_max lower upper
  simpa only [neg_sq, max_self] using square

/-- Width-only corollary: a parameter cell of width `w` has projective image
diameter at most the displayed coefficient times `w²`. -/
theorem chordalSq_projective_le_width
    (curve : RationalCurve) (interval : Interval)
    (clearance : DenominatorClearance
      (CCL.CurveBoxConditions.denominatorReal curve)
      (CCL.CurveBoxConditions.denominatorImaginary curve)
      interval)
    {left right : Coordinate}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    CCL.Chordal.chordalSq
        (projective curve left) (projective curve right) ≤
      chordalVariationCoefficient curve interval clearance *
        (RFAP.SturmEventPartition.Interval.width interval) ^ 2 :=
  (chordalSq_projective_le curve interval clearance leftInside rightInside).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (parameter_sub_sq_le_width_sq interval leftInside rightInside)
      (chordalVariationCoefficient_nonneg curve interval clearance))

end CCL.RationalCurveBounds
