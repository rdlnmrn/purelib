import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Persistent.ProfileRequestFamily

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace CCL.PersistentCCLInteriorGap

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box

open RFAP.ConstructiveGaussian.Gaussian

/-! ## Uniform separation of a finite box from projective infinity -/

/-- Positive squared-chordal gap from projective infinity to every affine
point of a displayed finite rational box. -/
def infinityBoxGap (box : Box) : Coordinate :=
  1 / (1 + box.normSqBound)

theorem infinityBoxGap_pos (box : Box) : 0 < infinityBoxGap box :=
  RFAP.ConstructiveFraction.div_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg (by decide) box.normSqBound_nonneg)

/-- Every affine point in the box is at least the computed rational gap from
`ω`; no compactification or limiting point is introduced. -/
theorem infinityBoxGap_le_affine
    {box : Box} {point : Gaussian} (inside : box.Contains point) :
    infinityBoxGap box ≤
      CCL.Chordal.chordalSq
        (CCL.Proj.affine point) CCL.Proj.omega := by
  rw [CCL.Chordal.chordalSq_omega]
  exact RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
    (by decide)
    (add_pos_of_pos_of_nonneg (by decide)
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg point))
    (add_le_add le_rfl (box.normSq_le_normSqBound inside))

/-- A homogeneous denominator residual below the chart-weight-scaled
infinity gap excludes the corresponding explicit non-pole affine point from
the finite box. -/
theorem denominator_residual_excludes_box
    {form : CCL.CCLGeometry.HermitianForm}
    (chart : CCL.CCLBoundaryCharts.BoundedChart form)
    (box : Box) (parameter : Coordinate)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (small :
      (CCL.CurveBoxConditions.denominatorNormSq
          chart.parameterization.curve).eval parameter ^ 2 <
        (chart.parameterization.weightLower * infinityBoxGap box) ^ 2) :
    ¬box.Contains
      (chart.parameterization.curve.point parameter) := by
  let denominatorNorm := normSq
    (chart.parameterization.curve.denominatorAt parameter)
  let weight := CCL.Chordal.Proj.weight
    (chart.projective parameter)
  let gap := infinityBoxGap box
  let cap := chart.parameterization.weightLower * gap
  have gapPositive : 0 < gap := by
    simpa only [gap] using infinityBoxGap_pos box
  have lowerPositive : 0 < chart.parameterization.weightLower :=
    chart.parameterization.weightLowerPositive
  have capPositive : 0 < cap :=
    RFAP.ConstructiveFraction.mul_pos_direct lowerPositive gapPositive
  have denominatorSquareSmall : denominatorNorm ^ 2 < cap ^ 2 := by
    simpa only [denominatorNorm, cap,
      CCL.CurveBoxConditions.eval_denominatorNormSq] using small
  have denominatorLtCap : denominatorNorm < cap :=
    RFAP.CauchyResolution.lt_of_sq_lt_sq_of_nonneg capPositive.le
      denominatorSquareSmall
  have denominatorNonnegative : 0 ≤ denominatorNorm := normSq_nonneg _
  have weightPositive : 0 < weight := by
    simpa only [weight] using chart.projective_weight_pos parameter
  have lowerLeWeight : chart.parameterization.weightLower ≤ weight := by
    simpa only [weight] using chart.weightLower_le_projective parameter
  have quotientLe : denominatorNorm / weight ≤
      denominatorNorm / chart.parameterization.weightLower :=
    RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      denominatorNonnegative lowerPositive lowerLeWeight
  have quotientLtGap :
      denominatorNorm / chart.parameterization.weightLower < gap := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos lowerPositive).2
    simpa only [cap, RFAP.ConstructiveFraction.mul_comm] using denominatorLtCap
  have projectiveClose :
      CCL.Chordal.chordalSq
          (chart.projective parameter) CCL.Proj.omega < gap := by
    have identity :
        CCL.Chordal.chordalSq
            (chart.projective parameter) CCL.Proj.omega =
          denominatorNorm / weight := by
      simp only [CCL.CCLBoundaryCharts.BoundedChart.projective,
        CCL.RationalCurveBounds.projective,
        CCL.Chordal.chordalSq, CCL.Proj.omega,
        CCL.Chordal.Proj.weight, denominatorNorm, weight,
        RFAP.ConstructiveGaussian.Gaussian.mul_zero,
        RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_sub,
        RFAP.ConstructiveGaussian.Gaussian.normSq_neg,
        RFAP.ConstructiveGaussian.Gaussian.normSq_one,
        RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
      congr 1
      ring1
    rw [identity]
    exact quotientLe.trans_lt quotientLtGap
  intro inside
  have gapLower := infinityBoxGap_le_affine inside
  have projectiveEq :=
    CCL.RationalCurveBounds.chordalSq_projective_eq_affine
      chart.parameterization.curve parameter denominatorNonzero CCL.Proj.omega
  rw [← projectiveEq] at gapLower
  exact (not_lt_of_ge gapLower) projectiveClose

private theorem div_le_div_of_cross
    {leftNumerator rightNumerator leftDenominator rightDenominator :
      Coordinate}
    (leftDenominatorPositive : 0 < leftDenominator)
    (rightDenominatorPositive : 0 < rightDenominator)
    (cross : leftNumerator * rightDenominator ≤
      rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator ≤
      rightNumerator / rightDenominator := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    rightDenominatorPositive).2
  have quotientIdentity :
      (leftNumerator / leftDenominator) * rightDenominator =
        (leftNumerator * rightDenominator) / leftDenominator := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (leftNumerator * leftDenominator⁻¹) * rightDenominator =
          leftNumerator * (leftDenominator⁻¹ * rightDenominator) :=
        RFAP.ConstructiveFraction.mul_assoc _ _ _
      _ = leftNumerator * (rightDenominator * leftDenominator⁻¹) :=
        congrArg (fun value => leftNumerator * value)
          (RFAP.ConstructiveFraction.mul_comm _ _)
      _ = (leftNumerator * rightDenominator) * leftDenominator⁻¹ :=
        (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
  rw [quotientIdentity]
  exact (RFAP.ConstructiveFraction.div_le_iff_pos
    leftDenominatorPositive).2 cross

/-- Minimum of the four displayed coordinate gaps around a strict interior
point. -/
def strictCoordinateGap (box : Box) (point : Gaussian) : Coordinate :=
  min (point.re - box.xLower)
    (min (box.xUpper - point.re)
      (min (point.im - box.yLower) (box.yUpper - point.im)))

/-- Minimum of the four rational margins from a strictly interior box to its
outer box. -/
def strictBoxGap (inner outer : Box) : Coordinate :=
  min (inner.xLower - outer.xLower)
    (min (outer.xUpper - inner.xUpper)
      (min (inner.yLower - outer.yLower)
        (outer.yUpper - inner.yUpper)))

theorem strictBoxGap_pos
    {inner outer : Box} (strict : inner.StrictInterior outer) :
    0 < strictBoxGap inner outer := by
  unfold strictBoxGap
  exact lt_min (RFAP.ConstructiveFraction.sub_pos_direct strict.left)
    (lt_min (RFAP.ConstructiveFraction.sub_pos_direct strict.right)
      (lt_min (RFAP.ConstructiveFraction.sub_pos_direct strict.bottom)
        (RFAP.ConstructiveFraction.sub_pos_direct strict.top)))

/-- A point within the computed coordinate radius of a strictly interior box
is already in the outer box. -/
theorem contains_of_within_strictBoxGap
    {inner outer : Box} {point : Gaussian}
    (near :
      inner.xLower - strictBoxGap inner outer < point.re ∧
      point.re < inner.xUpper + strictBoxGap inner outer ∧
      inner.yLower - strictBoxGap inner outer < point.im ∧
      point.im < inner.yUpper + strictBoxGap inner outer) :
    outer.Contains point := by
  let gap := strictBoxGap inner outer
  have gapLeft : gap ≤ inner.xLower - outer.xLower := by
    simpa only [gap, strictBoxGap] using
      (min_le_left (inner.xLower - outer.xLower)
        (min (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper))))
  have gapRight : gap ≤ outer.xUpper - inner.xUpper := by
    simpa only [gap, strictBoxGap] using
      (min_le_right (inner.xLower - outer.xLower)
        (min (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper)))).trans (min_le_left _ _)
  have gapBottom : gap ≤ inner.yLower - outer.yLower := by
    simpa only [gap, strictBoxGap] using
      (min_le_right (inner.xLower - outer.xLower)
        (min (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper)))).trans
        ((min_le_right (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper))).trans (min_le_left _ _))
  have gapTop : gap ≤ outer.yUpper - inner.yUpper := by
    simpa only [gap, strictBoxGap] using
      (min_le_right (inner.xLower - outer.xLower)
        (min (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper)))).trans
        ((min_le_right (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper))).trans (min_le_right _ _))
  have outerLeft : outer.xLower ≤ inner.xLower - gap := by
    apply (le_sub_iff_add_le).2
    simpa only [RFAP.ConstructiveFraction.add_comm] using
      (le_sub_iff_add_le.mp gapLeft)
  have outerRight : inner.xUpper + gap ≤ outer.xUpper := by
    simpa only [RFAP.ConstructiveFraction.add_comm] using
      (le_sub_iff_add_le.mp gapRight)
  have outerBottom : outer.yLower ≤ inner.yLower - gap := by
    apply (le_sub_iff_add_le).2
    simpa only [RFAP.ConstructiveFraction.add_comm] using
      (le_sub_iff_add_le.mp gapBottom)
  have outerTop : inner.yUpper + gap ≤ outer.yUpper := by
    simpa only [RFAP.ConstructiveFraction.add_comm] using
      (le_sub_iff_add_le.mp gapTop)
  exact
    ⟨outerLeft.trans_lt near.1 |>.le,
      near.2.1.trans_le outerRight |>.le,
      outerBottom.trans_lt near.2.2.1 |>.le,
      near.2.2.2.trans_le outerTop |>.le⟩

theorem strictCoordinateGap_pos
    {box : Box} {point : Gaussian} (strict : box.StrictContains point) :
    0 < strictCoordinateGap box point := by
  unfold strictCoordinateGap
  exact lt_min (RFAP.ConstructiveFraction.sub_pos_direct strict.1)
    (lt_min (RFAP.ConstructiveFraction.sub_pos_direct strict.2.1)
      (lt_min (RFAP.ConstructiveFraction.sub_pos_direct strict.2.2.1)
        (RFAP.ConstructiveFraction.sub_pos_direct strict.2.2.2)))

private theorem sq_le_normSq_sub_of_real_forward
    {gap : Coordinate} (gapNonnegative : 0 ≤ gap)
    {left right : Gaussian} (lower : gap ≤ left.re - right.re) :
    gap ^ 2 ≤ normSq (left - right) := by
  have squares := RFAP.ConstructiveFraction.pow_le_pow_direct
    gapNonnegative lower 2
  calc
    gap ^ 2 ≤ (left.re - right.re) ^ 2 := squares
    _ = (left.re - right.re) ^ 2 + 0 := by ring1
    _ ≤ normSq (left - right) :=
      add_le_add (le_refl _)
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (left.im - right.im))

private theorem sq_le_normSq_sub_of_real_reverse
    {gap : Coordinate} (gapNonnegative : 0 ≤ gap)
    {left right : Gaussian} (lower : gap ≤ right.re - left.re) :
    gap ^ 2 ≤ normSq (left - right) := by
  have squares := RFAP.ConstructiveFraction.pow_le_pow_direct
    gapNonnegative lower 2
  calc
    gap ^ 2 ≤ (right.re - left.re) ^ 2 := squares
    _ = (left.re - right.re) ^ 2 + 0 := by ring1
    _ ≤ normSq (left - right) :=
      add_le_add (le_refl _)
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (left.im - right.im))

private theorem sq_le_normSq_sub_of_imaginary_forward
    {gap : Coordinate} (gapNonnegative : 0 ≤ gap)
    {left right : Gaussian} (lower : gap ≤ left.im - right.im) :
    gap ^ 2 ≤ normSq (left - right) := by
  have squares := RFAP.ConstructiveFraction.pow_le_pow_direct
    gapNonnegative lower 2
  calc
    gap ^ 2 ≤ (left.im - right.im) ^ 2 := squares
    _ = 0 + (left.im - right.im) ^ 2 := by ring1
    _ ≤ normSq (left - right) :=
      add_le_add
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (left.re - right.re))
        (le_refl _)

private theorem sq_le_normSq_sub_of_imaginary_reverse
    {gap : Coordinate} (gapNonnegative : 0 ≤ gap)
    {left right : Gaussian} (lower : gap ≤ right.im - left.im) :
    gap ^ 2 ≤ normSq (left - right) := by
  have squares := RFAP.ConstructiveFraction.pow_le_pow_direct
    gapNonnegative lower 2
  calc
    gap ^ 2 ≤ (right.im - left.im) ^ 2 := squares
    _ = 0 + (left.im - right.im) ^ 2 := by ring1
    _ ≤ normSq (left - right) :=
      add_le_add
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (left.re - right.re))
        (le_refl _)

/-- Leaving a box costs at least the square of the minimum strict coordinate
gap in ordinary Gaussian quadrance. -/
theorem strictCoordinateGap_sq_le_normSq_sub_of_outside
    {box : Box} {point other : Gaussian}
    (strict : box.StrictContains point) (outside : ¬box.Contains other) :
    strictCoordinateGap box point ^ 2 ≤ normSq (point - other) := by
  let gap := strictCoordinateGap box point
  have gapNonnegative : 0 ≤ gap := (strictCoordinateGap_pos strict).le
  by_cases left : box.xLower ≤ other.re
  · by_cases right : other.re ≤ box.xUpper
    · by_cases bottom : box.yLower ≤ other.im
      · by_cases top : other.im ≤ box.yUpper
        · exact (outside ⟨left, right, bottom, top⟩).elim
        · have above : box.yUpper < other.im := lt_of_not_ge top
          have gapLeEdge : gap ≤ box.yUpper - point.im := by
            exact (min_le_right _ _).trans
              ((min_le_right _ _).trans (min_le_right _ _))
          have edgeLe : box.yUpper - point.im ≤ other.im - point.im :=
            RFAP.ConstructiveFraction.sub_le_sub_right_direct above.le point.im
          exact sq_le_normSq_sub_of_imaginary_reverse gapNonnegative
            (gapLeEdge.trans edgeLe)
      · have below : other.im < box.yLower := lt_of_not_ge bottom
        have gapLeEdge : gap ≤ point.im - box.yLower := by
          exact (min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _))
        have edgeLe : point.im - box.yLower ≤ point.im - other.im :=
          RFAP.ConstructiveFraction.sub_le_sub_left_direct below.le point.im
        exact sq_le_normSq_sub_of_imaginary_forward gapNonnegative
          (gapLeEdge.trans edgeLe)
    · have rightOf : box.xUpper < other.re := lt_of_not_ge right
      have gapLeEdge : gap ≤ box.xUpper - point.re :=
        (min_le_right _ _).trans (min_le_left _ _)
      have edgeLe : box.xUpper - point.re ≤ other.re - point.re :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct rightOf.le point.re
      exact sq_le_normSq_sub_of_real_reverse gapNonnegative
        (gapLeEdge.trans edgeLe)
  · have leftOf : other.re < box.xLower := lt_of_not_ge left
    have gapLeEdge : gap ≤ point.re - box.xLower := min_le_left _ _
    have edgeLe : point.re - box.xLower ≤ point.re - other.re :=
      RFAP.ConstructiveFraction.sub_le_sub_left_direct leftOf.le point.re
    exact sq_le_normSq_sub_of_real_forward gapNonnegative
      (gapLeEdge.trans edgeLe)

/-- Conservative projective gap from a strict interior rational point to
the complete affine complement of its box. -/
def strictChordalGap (box : Box) (point : Gaussian) : Coordinate :=
  let gapSq := strictCoordinateGap box point ^ 2
  gapSq /
    ((1 + normSq point) *
      (1 + 2 * normSq point + 2 * gapSq))

theorem strictChordalGap_pos
    {box : Box} {point : Gaussian} (strict : box.StrictContains point) :
    0 < strictChordalGap box point := by
  let gap := strictCoordinateGap box point
  have gapPositive : 0 < gap := strictCoordinateGap_pos strict
  have gapSqPositive : 0 < gap ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct gapPositive 2
  have firstPositive : 0 < 1 + normSq point :=
    add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg point)
  have secondPositive : 0 <
      1 + 2 * normSq point + 2 * gap ^ 2 :=
    add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (normSq_nonneg point)))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct gap))
  exact RFAP.ConstructiveFraction.div_pos_direct gapSqPositive
    (RFAP.ConstructiveFraction.mul_pos_direct firstPositive secondPositive)

/-- The computed rational projective gap is below the squared-chordal
distance from the strict point to every displayed affine point outside the
box. -/
theorem strictChordalGap_le_affine_of_outside
    {box : Box} {point other : Gaussian}
    (strict : box.StrictContains point) (outside : ¬box.Contains other) :
    strictChordalGap box point ≤
      CCL.Chordal.chordalSq
        (CCL.Proj.affine point) (CCL.Proj.affine other) := by
  let gap := strictCoordinateGap box point
  let gapSq := gap ^ 2
  let distance := normSq (point - other)
  let pointNorm := normSq point
  let otherNorm := normSq other
  let common := 1 + pointNorm
  let targetPart := 1 + 2 * pointNorm + 2 * gapSq
  let actualPart := 1 + otherNorm
  have gapSqLe : gapSq ≤ distance := by
    simpa only [gapSq, gap, distance] using
      strictCoordinateGap_sq_le_normSq_sub_of_outside strict outside
  have gapSqNonnegative : 0 ≤ gapSq := by
    exact RFAP.ConstructiveFraction.sq_nonneg_direct gap
  have distanceNonnegative : 0 ≤ distance := normSq_nonneg _
  have pointNormNonnegative : 0 ≤ pointNorm := normSq_nonneg _
  have otherNormNonnegative : 0 ≤ otherNorm := normSq_nonneg _
  have commonPositive : 0 < common :=
    add_pos_of_pos_of_nonneg (by decide) pointNormNonnegative
  have targetPartPositive : 0 < targetPart := by
    dsimp only [targetPart]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          pointNormNonnegative))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        gapSqNonnegative)
  have actualPartPositive : 0 < actualPart :=
    add_pos_of_pos_of_nonneg (by decide) otherNormNonnegative
  have otherNormUpper : otherNorm ≤ 2 * (pointNorm + distance) := by
    have raw := normSq_sub_le_two point (point - other)
    have identity : point - (point - other) = other := by
      exact sub_sub_cancel point other
    rw [identity] at raw
    simpa only [otherNorm, pointNorm, distance] using raw
  have actualPartUpper : actualPart ≤
      1 + 2 * pointNorm + 2 * distance := by
    dsimp only [actualPart]
    calc
      1 + otherNorm ≤ 1 + 2 * (pointNorm + distance) := by
        calc
          1 + otherNorm = otherNorm + 1 := by ring1
          _ ≤ 2 * (pointNorm + distance) + 1 :=
            RFAP.ConstructiveFraction.add_le_add_right_direct
              otherNormUpper 1
          _ = 1 + 2 * (pointNorm + distance) := by ring1
      _ = 1 + 2 * pointNorm + 2 * distance := by ring1
  have cross : gapSq * actualPart ≤ distance * targetPart := by
    calc
      gapSq * actualPart ≤
          gapSq * (1 + 2 * pointNorm + 2 * distance) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          actualPartUpper gapSqNonnegative
      _ = gapSq * (1 + 2 * pointNorm) + 2 * gapSq * distance := by
        ring1
      _ ≤ distance * (1 + 2 * pointNorm) + 2 * distance * gapSq :=
        add_le_add
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            gapSqLe
            (add_nonneg (by decide)
              (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                pointNormNonnegative)))
          (le_of_eq (by ring1))
      _ = distance * targetPart := by
        dsimp only [targetPart]
        ring1
  have targetDenominatorPositive : 0 < common * targetPart :=
    RFAP.ConstructiveFraction.mul_pos_direct commonPositive targetPartPositive
  have actualDenominatorPositive : 0 < common * actualPart :=
    RFAP.ConstructiveFraction.mul_pos_direct commonPositive actualPartPositive
  have crossWithCommon : gapSq * (common * actualPart) ≤
      distance * (common * targetPart) := by
    calc
      gapSq * (common * actualPart) = common * (gapSq * actualPart) := by
        ring1
      _ ≤ common * (distance * targetPart) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct cross
          commonPositive.le
      _ = distance * (common * targetPart) := by ring1
  rw [CCL.Chordal.chordalSq_affine]
  change gapSq / (common * targetPart) ≤
    distance / (common * actualPart)
  exact div_le_div_of_cross targetDenominatorPositive
    actualDenominatorPositive crossWithCommon

/-! ## A point-independent gap from a uniform interior strip -/

/-- Squared-chordal gap shared by every in-box point carrying the displayed
positive coordinate margin.  The box norm majorant removes the point from
the numerical value of the bound. -/
def interiorStripChordalGap (box : Box) (radius : Coordinate) : Coordinate :=
  let radiusSq := radius ^ 2
  radiusSq /
    ((1 + box.normSqBound) *
      (1 + 2 * box.normSqBound + 2 * radiusSq))

theorem interiorStripChordalGap_pos
    (box : Box) {radius : Coordinate} (positive : 0 < radius) :
    0 < interiorStripChordalGap box radius := by
  have radiusSqPositive : 0 < radius ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct positive 2
  have firstPositive : 0 < 1 + box.normSqBound :=
    add_pos_of_pos_of_nonneg (by decide) box.normSqBound_nonneg
  have secondPositive : 0 <
      1 + 2 * box.normSqBound + 2 * radius ^ 2 :=
    add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          box.normSqBound_nonneg))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct radius))
  exact RFAP.ConstructiveFraction.div_pos_direct radiusSqPositive
    (RFAP.ConstructiveFraction.mul_pos_direct firstPositive secondPositive)

private theorem radius_le_strictCoordinateGap
    {box : Box} {point : Gaussian} {radius : Coordinate}
    (left : box.xLower + radius < point.re)
    (right : point.re + radius < box.xUpper)
    (bottom : box.yLower + radius < point.im)
    (top : point.im + radius < box.yUpper) :
    radius ≤ strictCoordinateGap box point := by
  have leftGap : radius < point.re - box.xLower := by
    calc
      radius = (box.xLower + radius) + -box.xLower := by ring1
      _ < point.re + -box.xLower :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct left (-box.xLower)
      _ = point.re - box.xLower := by ring1
  have rightGap : radius < box.xUpper - point.re := by
    calc
      radius = (point.re + radius) + -point.re := by ring1
      _ < box.xUpper + -point.re :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct right (-point.re)
      _ = box.xUpper - point.re := by ring1
  have bottomGap : radius < point.im - box.yLower := by
    calc
      radius = (box.yLower + radius) + -box.yLower := by ring1
      _ < point.im + -box.yLower :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct bottom (-box.yLower)
      _ = point.im - box.yLower := by ring1
  have topGap : radius < box.yUpper - point.im := by
    calc
      radius = (point.im + radius) + -point.im := by ring1
      _ < box.yUpper + -point.im :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct top (-point.im)
      _ = box.yUpper - point.im := by ring1
  unfold strictCoordinateGap
  exact le_min leftGap.le (le_min rightGap.le (le_min bottomGap.le topGap.le))

/-- The uniform four-coordinate strip supplies the same ordinary distance
lower bound at every point carrying it. -/
theorem interiorStripRadius_sq_le_normSq_sub_of_outside
    {box : Box} {point other : Gaussian} {radius : Coordinate}
    (positive : 0 < radius)
    (left : box.xLower + radius < point.re)
    (right : point.re + radius < box.xUpper)
    (bottom : box.yLower + radius < point.im)
    (top : point.im + radius < box.yUpper)
    (outside : ¬box.Contains other) :
    radius ^ 2 ≤ normSq (point - other) := by
  have strict : box.StrictContains point :=
    ⟨(show box.xLower < box.xLower + radius by
        calc
          box.xLower = box.xLower + 0 := by ring1
          _ < box.xLower + radius :=
            RFAP.ConstructiveFraction.add_lt_add_left_direct positive
              box.xLower).trans left,
      (show point.re < point.re + radius by
        calc
          point.re = point.re + 0 := by ring1
          _ < point.re + radius :=
            RFAP.ConstructiveFraction.add_lt_add_left_direct positive
              point.re).trans right,
      (show box.yLower < box.yLower + radius by
        calc
          box.yLower = box.yLower + 0 := by ring1
          _ < box.yLower + radius :=
            RFAP.ConstructiveFraction.add_lt_add_left_direct positive
              box.yLower).trans bottom,
      (show point.im < point.im + radius by
        calc
          point.im = point.im + 0 := by ring1
          _ < point.im + radius :=
            RFAP.ConstructiveFraction.add_lt_add_left_direct positive
              point.im).trans top⟩
  have radiusLe := radius_le_strictCoordinateGap left right bottom top
  have squareLe := RFAP.ConstructiveFraction.pow_le_pow_direct positive.le
    radiusLe 2
  exact squareLe.trans
    (strictCoordinateGap_sq_le_normSq_sub_of_outside strict outside)

/-- A uniform positive coordinate strip gives a point-independent projective
gap from all of its points to the whole affine complement of the box. -/
theorem interiorStripChordalGap_le_affine_of_outside
    {box : Box} {point other : Gaussian} {radius : Coordinate}
    (positive : 0 < radius)
    (contains : box.Contains point)
    (left : box.xLower + radius < point.re)
    (right : point.re + radius < box.xUpper)
    (bottom : box.yLower + radius < point.im)
    (top : point.im + radius < box.yUpper)
    (outside : ¬box.Contains other) :
    interiorStripChordalGap box radius ≤
      CCL.Chordal.chordalSq
        (CCL.Proj.affine point) (CCL.Proj.affine other) := by
  let radiusSq := radius ^ 2
  let distance := normSq (point - other)
  let pointNorm := normSq point
  let otherNorm := normSq other
  let bound := box.normSqBound
  let targetCommon := 1 + bound
  let targetPart := 1 + 2 * bound + 2 * radiusSq
  let actualCommon := 1 + pointNorm
  let actualPart := 1 + otherNorm
  have radiusSqLe : radiusSq ≤ distance := by
    simpa only [radiusSq, distance] using
      interiorStripRadius_sq_le_normSq_sub_of_outside positive left
        right bottom top outside
  have radiusSqNonnegative : 0 ≤ radiusSq :=
    RFAP.ConstructiveFraction.sq_nonneg_direct radius
  have distanceNonnegative : 0 ≤ distance := normSq_nonneg _
  have pointNormNonnegative : 0 ≤ pointNorm := normSq_nonneg _
  have otherNormNonnegative : 0 ≤ otherNorm := normSq_nonneg _
  have boundNonnegative : 0 ≤ bound := box.normSqBound_nonneg
  have pointNormLe : pointNorm ≤ bound := by
    simpa only [pointNorm, bound] using box.normSq_le_normSqBound contains
  have actualCommonLe : actualCommon ≤ targetCommon := by
    dsimp only [actualCommon, targetCommon]
    calc
      1 + pointNorm = pointNorm + 1 := by ring1
      _ ≤ bound + 1 :=
        RFAP.ConstructiveFraction.add_le_add_right_direct pointNormLe 1
      _ = 1 + bound := by ring1
  have targetCommonPositive : 0 < targetCommon :=
    add_pos_of_pos_of_nonneg (by decide) boundNonnegative
  have targetPartPositive : 0 < targetPart := by
    dsimp only [targetPart]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          boundNonnegative))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        radiusSqNonnegative)
  have actualCommonPositive : 0 < actualCommon :=
    add_pos_of_pos_of_nonneg (by decide) pointNormNonnegative
  have actualPartPositive : 0 < actualPart :=
    add_pos_of_pos_of_nonneg (by decide) otherNormNonnegative
  have otherNormUpper : otherNorm ≤ 2 * (pointNorm + distance) := by
    have raw := normSq_sub_le_two point (point - other)
    have identity : point - (point - other) = other := by
      exact sub_sub_cancel point other
    rw [identity] at raw
    simpa only [otherNorm, pointNorm, distance] using raw
  have actualPartUpper : actualPart ≤
      1 + 2 * bound + 2 * distance := by
    dsimp only [actualPart]
    calc
      1 + otherNorm ≤ 1 + 2 * (pointNorm + distance) := by
        calc
          1 + otherNorm = otherNorm + 1 := by ring1
          _ ≤ 2 * (pointNorm + distance) + 1 :=
            RFAP.ConstructiveFraction.add_le_add_right_direct otherNormUpper 1
          _ = 1 + 2 * (pointNorm + distance) := by ring1
      _ ≤ 1 + 2 * bound + 2 * distance := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            pointNormLe (show (0 : Coordinate) ≤ 2 by decide)
        calc
          1 + 2 * (pointNorm + distance) =
              2 * pointNorm + (1 + 2 * distance) := by ring1
          _ ≤ 2 * bound + (1 + 2 * distance) :=
            RFAP.ConstructiveFraction.add_le_add_right_direct scaled
              (1 + 2 * distance)
          _ = 1 + 2 * bound + 2 * distance := by ring1
      _ = 1 + 2 * bound + 2 * distance := by ring1
  have cross :
      radiusSq * (actualCommon * actualPart) ≤
        distance * (targetCommon * targetPart) := by
    calc
      radiusSq * (actualCommon * actualPart) ≤
          radiusSq *
            (targetCommon * (1 + 2 * bound + 2 * distance)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (RFAP.ConstructiveFraction.mul_le_mul_direct actualCommonLe
            actualPartUpper actualPartPositive.le targetCommonPositive.le)
          radiusSqNonnegative
      _ = targetCommon *
          (radiusSq * (1 + 2 * bound) + 2 * radiusSq * distance) := by
        ring1
      _ ≤ targetCommon *
          (distance * (1 + 2 * bound) + 2 * distance * radiusSq) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              radiusSqLe
              (add_nonneg (by decide)
                (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                  boundNonnegative)))
            (le_of_eq (by ring1)))
          targetCommonPositive.le
      _ = distance * (targetCommon * targetPart) := by
        dsimp only [targetPart]
        ring1
  have targetDenominatorPositive : 0 < targetCommon * targetPart :=
    RFAP.ConstructiveFraction.mul_pos_direct targetCommonPositive
      targetPartPositive
  have actualDenominatorPositive : 0 < actualCommon * actualPart :=
    RFAP.ConstructiveFraction.mul_pos_direct actualCommonPositive
      actualPartPositive
  rw [CCL.Chordal.chordalSq_affine]
  change radiusSq / (targetCommon * targetPart) ≤
    distance / (actualCommon * actualPart)
  exact div_le_div_of_cross targetDenominatorPositive
    actualDenominatorPositive cross

/-! ## Keeping a complete requested event inside one owner box -/

/-- If one rational sample of a globally controlled event has the displayed
uniform interior strip, and the global diameter target is below the strip's
projective gap, then every non-pole rational point of that complete event is
inside the same box.  This upgrades sample ownership to whole-cylinder
ownership without manufacturing a parameter root. -/
theorem controlled_event_contains_of_uniform_strip
    {p : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {reference : CCL.GaussianProjective.Mat2}
    {current : Box} {denominatorMargin : Coordinate}
    {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CCL.PersistentCCLDispatch.CurveBoundary p
      reference current denominatorMargin marginPositive atom}
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary
        (CCL.PersistentCCLProfileRequestFamily.boundaryControlledRequestWidth
          boundary boxes pairwise target))
    (box : Box) {radius : Coordinate} (radiusPositive : 0 < radius)
    (sampleParameter : Coordinate)
    (sampleInside : entry.child.cell.interval.Contains sampleParameter)
    (sampleDenominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        sampleParameter ≠ 0)
    (samplePointInside : box.Contains
      (entry.parent.parent.chart.parameterization.curve.point sampleParameter))
    (sampleLeft : box.xLower + radius <
      (entry.parent.parent.chart.parameterization.curve.point
        sampleParameter).re)
    (sampleRight :
      (entry.parent.parent.chart.parameterization.curve.point
        sampleParameter).re + radius < box.xUpper)
    (sampleBottom : box.yLower + radius <
      (entry.parent.parent.chart.parameterization.curve.point
        sampleParameter).im)
    (sampleTop :
      (entry.parent.parent.chart.parameterization.curve.point
        sampleParameter).im + radius < box.yUpper)
    (targetLeGap : target ≤ interiorStripChordalGap box radius)
    {parameter : Coordinate}
    (parameterInside : entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0) :
    box.Contains
      (entry.parent.parent.chart.parameterization.curve.point parameter) := by
  let curve := entry.parent.parent.chart.parameterization.curve
  let samplePoint := curve.point sampleParameter
  let point := curve.point parameter
  by_cases contained : box.Contains point
  · exact contained
  · have eventUpper := entry.chordalSq_le
        (CCL.PersistentCCLProfileRequestFamily.boundaryControlledRequestWidth_pos
          boundary boxes pairwise targetPositive)
        sampleInside parameterInside
    have leftTransport :
        CCL.Chordal.chordalSq
            (entry.parent.parent.chart.projective sampleParameter)
            (entry.parent.parent.chart.projective parameter) =
          CCL.Chordal.chordalSq
            (CCL.Proj.affine samplePoint)
            (entry.parent.parent.chart.projective parameter) := by
      simpa only [curve, samplePoint,
        CCL.CCLBoundaryCharts.BoundedChart.projective] using
        CCL.RationalCurveBounds.chordalSq_projective_eq_affine
          curve sampleParameter sampleDenominatorNonzero
            (entry.parent.parent.chart.projective parameter)
    have rightEquivalent :
        (entry.parent.parent.chart.projective parameter).Equivalent
          (CCL.Proj.affine point) := by
      simpa only [curve, point,
        CCL.CCLBoundaryCharts.BoundedChart.projective] using
        CCL.RationalCurveBounds.projective_equivalent_affine
          curve parameter denominatorNonzero
    have rightTransport :
        CCL.Chordal.chordalSq
            (CCL.Proj.affine samplePoint)
            (entry.parent.parent.chart.projective parameter) =
          CCL.Chordal.chordalSq
            (CCL.Proj.affine samplePoint) (CCL.Proj.affine point) :=
      CCL.Chordal.chordalSq_eq_of_equivalent_right
        (entry.parent.parent.chart.projective_valid parameter)
        (CCL.Chordal.Proj.affine_hasNonzeroCoordinate point)
        rightEquivalent (CCL.Proj.affine samplePoint)
    have affineUpper :
        CCL.Chordal.chordalSq
            (CCL.Proj.affine samplePoint) (CCL.Proj.affine point) ≤
          entry.parent.parent.chart.uniformChordalVariationCoefficient *
            CCL.PersistentCCLProfileRequestFamily.boundaryControlledRequestWidth
              boundary boxes pairwise target ^ 2 := by
      rw [← rightTransport, ← leftTransport]
      exact eventUpper
    have diameterSmall :
        entry.parent.parent.chart.uniformChordalVariationCoefficient *
            CCL.PersistentCCLProfileRequestFamily.boundaryControlledRequestWidth
              boundary boxes pairwise target ^ 2 <
          interiorStripChordalGap box radius :=
      (entry.controlled_chordal_diameter_lt targetPositive).trans_le targetLeGap
    have affineLower : interiorStripChordalGap box radius ≤
        CCL.Chordal.chordalSq
          (CCL.Proj.affine samplePoint) (CCL.Proj.affine point) := by
      exact interiorStripChordalGap_le_affine_of_outside radiusPositive
        (by simpa only [curve, samplePoint] using samplePointInside)
        (by simpa only [curve, samplePoint] using sampleLeft)
        (by simpa only [curve, samplePoint] using sampleRight)
        (by simpa only [curve, samplePoint] using sampleBottom)
        (by simpa only [curve, samplePoint] using sampleTop)
        (by simpa only [curve, point] using contained)
    exact (not_lt_of_ge affineLower) (affineUpper.trans_lt diameterSmall) |>.elim

end CCL.PersistentCCLInteriorGap
