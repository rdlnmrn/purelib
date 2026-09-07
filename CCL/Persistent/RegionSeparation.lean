import mathlib.Tactic.QuotientFreeRing
import CCL.Persistent.BoundaryEvents

/-!
# Separating persistent CCL events across winding regions

Finite winding boxes and finite boundary-event cylinders now shrink in the
same squared-chordal metric.  This module supplies the missing quantitative
separation bridge: a positive coordinate gap between two rational boxes gives
a positive projective gap between all of their affine points.  Consequently a
sufficiently narrow nonzero boundary-event cylinder cannot meet both boxes.

Every bound is a displayed constructive rational.  No point at infinity,
completed root, compactness argument, or selected limiting parameter occurs.
-/

namespace CCL.PersistentCCLRegionSeparation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev CurveBoundary := CCL.PersistentCCLDispatch.CurveBoundary

open RFAP.ConstructiveGaussian.Gaussian

/-- Uniform upper bound for the homogeneous weight of affine points in one
rational box. -/
def affineWeightUpper (box : Box) : Coordinate := 1 + box.normSqBound

theorem affineWeightUpper_pos (box : Box) : 0 < affineWeightUpper box :=
  (show (0 : Coordinate) < 1 by decide).trans_le
    (le_add_of_nonneg_right box.normSqBound_nonneg)

theorem affine_weight_le
    {box : Box} {point : Gaussian} (inside : box.Contains point) :
    CCL.Chordal.Proj.weight (CCL.Proj.affine point) ≤
      affineWeightUpper box := by
  simp only [CCL.Chordal.Proj.weight, CCL.Proj.affine, normSq_one,
    affineWeightUpper]
  calc
    normSq point + 1 = 1 + normSq point := by ring1
    _ ≤ 1 + box.normSqBound :=
      add_le_add_right (box.normSq_le_normSqBound inside) 1

/-- Projective separation obtained from a displayed positive coordinate gap.
The two box-weight factors are finite coefficient data. -/
def chordalGap
    (left right : Box) (coordinateGap : Coordinate) : Coordinate :=
  coordinateGap ^ 2 /
    (affineWeightUpper left * affineWeightUpper right)

theorem chordalGap_pos
    (left right : Box) {coordinateGap : Coordinate}
    (positive : 0 < coordinateGap) :
    0 < chordalGap left right coordinateGap :=
  RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2)
    (RFAP.ConstructiveFraction.mul_pos_direct
      (affineWeightUpper_pos left) (affineWeightUpper_pos right))

/-- A uniform positive width that makes `coefficient * width^2` strictly
smaller than a displayed positive target. -/
def shrinkingWidth (coefficient target : Coordinate) : Coordinate :=
  min 1 (target / (2 * (coefficient + 1)))

theorem shrinkingWidth_pos
    {coefficient target : Coordinate} (coefficientNonnegative : 0 ≤ coefficient)
    (targetPositive : 0 < target) :
    0 < shrinkingWidth coefficient target := by
  have denominatorPositive : 0 < 2 * (coefficient + 1) :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (add_pos_of_nonneg_of_pos coefficientNonnegative (by decide))
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct targetPositive
      denominatorPositive)

theorem coefficient_mul_shrinkingWidth_sq_lt
    {coefficient target : Coordinate} (coefficientNonnegative : 0 ≤ coefficient)
    (targetPositive : 0 < target) :
    coefficient * shrinkingWidth coefficient target ^ 2 < target := by
  let width := shrinkingWidth coefficient target
  let denominator := 2 * (coefficient + 1)
  have widthPositive : 0 < width :=
    shrinkingWidth_pos coefficientNonnegative targetPositive
  have widthLeOne : width ≤ 1 := min_le_left _ _
  have widthLeRatio : width ≤ target / denominator := min_le_right _ _
  have denominatorPositive : 0 < denominator :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (add_pos_of_nonneg_of_pos coefficientNonnegative (by decide))
  have widthSquareLe : width ^ 2 ≤ width := by
    rw [pow_two]
    exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      widthLeOne widthPositive.le).trans_eq
        (RFAP.ConstructiveFraction.one_mul width)
  have coefficientStrict : coefficient < denominator := by
    have addStrict : coefficient < coefficient + 1 := by
      have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
        (show (0 : Coordinate) < 1 by decide) coefficient
      calc
        coefficient = coefficient + 0 := by ring1
        _ < coefficient + 1 := shifted
    have addNonnegative : 0 ≤ coefficient + 1 :=
      add_nonneg coefficientNonnegative (by decide)
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (show (1 : Coordinate) ≤ 2 by decide) addNonnegative
    exact addStrict.trans_le (by
      simpa only [denominator, RFAP.ConstructiveFraction.one_mul] using scaled)
  have denominatorWidthLe : denominator * width ≤ target := by
    have divided :=
      (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).mp
        widthLeRatio
    calc
      denominator * width = width * denominator :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ ≤ target := divided
  calc
    coefficient * width ^ 2 ≤ coefficient * width :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        widthSquareLe coefficientNonnegative
    _ < denominator * width :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        coefficientStrict widthPositive
    _ ≤ target := denominatorWidthLe

/-- The displayed projective gap is below the squared-chordal distance of
any two box points whenever the coordinate gap bounds their squared distance. -/
theorem chordalGap_le_affine
    {left right : Box} {coordinateGap : Coordinate}
    {leftPoint rightPoint : Gaussian}
    (leftInside : left.Contains leftPoint)
    (rightInside : right.Contains rightPoint)
    (distanceLower : coordinateGap ^ 2 ≤
      normSq (leftPoint - rightPoint)) :
    chordalGap left right coordinateGap ≤
      CCL.Chordal.chordalSq
        (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) := by
  let actualDenominator :=
    (1 + normSq leftPoint) * (1 + normSq rightPoint)
  let upperDenominator := affineWeightUpper left * affineWeightUpper right
  have actualPositive : 0 < actualDenominator :=
    RFAP.ConstructiveFraction.mul_pos_direct
      ((show (0 : Coordinate) < 1 by decide).trans_le
        (le_add_of_nonneg_right (normSq_nonneg leftPoint)))
      ((show (0 : Coordinate) < 1 by decide).trans_le
        (le_add_of_nonneg_right (normSq_nonneg rightPoint)))
  have upperPositive : 0 < upperDenominator :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (affineWeightUpper_pos left) (affineWeightUpper_pos right)
  have actualUpper : actualDenominator ≤ upperDenominator := by
    dsimp only [actualDenominator, upperDenominator]
    have leftWeight : 1 + normSq leftPoint ≤ affineWeightUpper left := by
      simpa only [CCL.Chordal.Proj.weight, CCL.Proj.affine,
        normSq_one, RFAP.ConstructiveFraction.add_comm] using
          affine_weight_le leftInside
    have rightWeight : 1 + normSq rightPoint ≤ affineWeightUpper right := by
      simpa only [CCL.Chordal.Proj.weight, CCL.Proj.affine,
        normSq_one, RFAP.ConstructiveFraction.add_comm] using
          affine_weight_le rightInside
    exact RFAP.ConstructiveFraction.mul_le_mul_direct leftWeight rightWeight
      (add_nonneg (by decide) (normSq_nonneg rightPoint))
      (affineWeightUpper_pos left).le
  have numeratorNonnegative : 0 ≤ normSq (leftPoint - rightPoint) :=
    normSq_nonneg _
  calc
    chordalGap left right coordinateGap =
        coordinateGap ^ 2 / upperDenominator := rfl
    _ ≤ normSq (leftPoint - rightPoint) / upperDenominator := by
      apply (RFAP.ConstructiveFraction.div_le_iff_pos upperPositive).2
      have cancel : normSq (leftPoint - rightPoint) / upperDenominator *
          upperDenominator = normSq (leftPoint - rightPoint) :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          (normSq (leftPoint - rightPoint)) upperDenominator upperPositive.ne'
      rw [cancel]
      exact distanceLower
    _ ≤ normSq (leftPoint - rightPoint) / actualDenominator :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        numeratorNonnegative actualPositive actualUpper
    _ = CCL.Chordal.chordalSq
        (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) := by
      rw [CCL.Chordal.chordalSq_affine]

/-- Executable positive squared-chordal gap obtained by scanning the four
coordinate separations of two rational boxes. -/
def separatedChordalGap
    {left right : Box} (separated : left.Separated right) : Coordinate :=
  chordalGap left right
    (RFAP.Boxes.Box.separationCertificate separated).gap

theorem separatedChordalGap_pos
    {left right : Box} (separated : left.Separated right) :
    0 < separatedChordalGap separated :=
  chordalGap_pos left right
    (RFAP.Boxes.Box.separationCertificate separated).positive

theorem separatedChordalGap_le_affine
    {left right : Box} (separated : left.Separated right)
    {leftPoint rightPoint : Gaussian}
    (leftInside : left.Contains leftPoint)
    (rightInside : right.Contains rightPoint) :
    separatedChordalGap separated ≤
      CCL.Chordal.chordalSq
        (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) :=
  chordalGap_le_affine leftInside rightInside
    ((RFAP.Boxes.Box.separationCertificate separated).lower
      leftInside rightInside)

/-- Compatibility wrapper exposing the executable gap together with its
positive and pointwise lower-bound certificates. -/
theorem separated_chordalGap
    {left right : Box} (separated : left.Separated right) :
    ∃ gap : Coordinate, 0 < gap ∧
      ∀ {leftPoint rightPoint : Gaussian},
        left.Contains leftPoint → right.Contains rightPoint →
          gap ≤ CCL.Chordal.chordalSq
            (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) :=
  ⟨separatedChordalGap separated, separatedChordalGap_pos separated,
    separatedChordalGap_le_affine separated⟩

/-- Coefficient-computed positive request width for keeping one boundary
event inside at most one of two separated winding regions. -/
def separatedEventRequestWidth
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      CCL.PersistentCCLBoundaryEvents.BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    Coordinate :=
  shrinkingWidth entry.chart.uniformChordalVariationCoefficient
    (separatedChordalGap separated)

theorem separatedEventRequestWidth_pos
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      CCL.PersistentCCLBoundaryEvents.BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    0 < separatedEventRequestWidth entry separated :=
  shrinkingWidth_pos
    entry.chart.uniformChordalVariationCoefficient_nonneg
    (separatedChordalGap_pos separated)

/-- After requesting an event cylinder whose certified diameter is below the
positive gap between two separated boxes, that one event cannot contain
non-pole parameters whose affine images lie in both boxes.  This is the
finite keep-apart statement needed before assigning a boundary event to one
winding region. -/
theorem requested_event_not_spanning_with_gap
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      CCL.PersistentCCLBoundaryEvents.BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (gap : Coordinate)
    (gapLower : ∀ {leftPoint rightPoint : Gaussian},
      leftBox.Contains leftPoint → rightBox.Contains rightPoint →
        gap ≤ CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint))
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (diameterSmall :
      entry.chart.uniformChordalVariationCoefficient * epsilon ^ 2 < gap)
    {leftParameter rightParameter : Coordinate}
    (leftParameterInside :
      (entry.request epsilon).cell.interval.Contains leftParameter)
    (rightParameterInside :
      (entry.request epsilon).cell.interval.Contains rightParameter)
    (leftDenominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt leftParameter ≠ 0)
    (rightDenominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt rightParameter ≠ 0)
    (leftPointInside : leftBox.Contains
      (entry.chart.parameterization.curve.point leftParameter))
    (rightPointInside : rightBox.Contains
      (entry.chart.parameterization.curve.point rightParameter)) : False := by
  let curve := entry.chart.parameterization.curve
  let leftPoint := curve.point leftParameter
  let rightPoint := curve.point rightParameter
  have eventUpper := entry.chordalSq_request_le epsilon epsilonPositive
    leftParameterInside rightParameterInside
  have leftTransport :
      CCL.Chordal.chordalSq
          (entry.chart.projective leftParameter)
          (entry.chart.projective rightParameter) =
        CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint)
          (entry.chart.projective rightParameter) := by
    simpa only [curve, leftPoint,
      CCL.CCLBoundaryCharts.BoundedChart.projective] using
      CCL.RationalCurveBounds.chordalSq_projective_eq_affine
        curve leftParameter leftDenominatorNonzero
          (entry.chart.projective rightParameter)
  have rightEquivalent :
      (entry.chart.projective rightParameter).Equivalent
        (CCL.Proj.affine rightPoint) := by
    simpa only [curve, rightPoint,
      CCL.CCLBoundaryCharts.BoundedChart.projective] using
      CCL.RationalCurveBounds.projective_equivalent_affine
        curve rightParameter rightDenominatorNonzero
  have rightTransport :
      CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint)
          (entry.chart.projective rightParameter) =
        CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) :=
    CCL.Chordal.chordalSq_eq_of_equivalent_right
      (entry.chart.projective_valid rightParameter)
      (CCL.Chordal.Proj.affine_hasNonzeroCoordinate rightPoint)
      rightEquivalent (CCL.Proj.affine leftPoint)
  have affineUpper :
      CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) ≤
        entry.chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
    rw [← rightTransport, ← leftTransport]
    exact eventUpper
  have affineLower : gap ≤
      CCL.Chordal.chordalSq
        (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) :=
    gapLower leftPointInside rightPointInside
  exact (not_lt_of_ge affineLower) (affineUpper.trans_lt diameterSmall)

/-- The computed request width keeps one event from meeting both separated
boxes.  All inputs are finite rational certificates. -/
theorem separatedEventRequest_not_spanning
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      CCL.PersistentCCLBoundaryEvents.BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    ∀ {leftParameter rightParameter : Coordinate},
      (entry.request (separatedEventRequestWidth entry separated)).cell.interval.Contains
        leftParameter →
      (entry.request (separatedEventRequestWidth entry separated)).cell.interval.Contains
        rightParameter →
      entry.chart.parameterization.curve.denominatorAt leftParameter ≠ 0 →
      entry.chart.parameterization.curve.denominatorAt rightParameter ≠ 0 →
      leftBox.Contains
        (entry.chart.parameterization.curve.point leftParameter) →
      rightBox.Contains
        (entry.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftParameterInside rightParameterInside
    leftDenominatorNonzero rightDenominatorNonzero leftPointInside
    rightPointInside
  apply requested_event_not_spanning_with_gap entry
    (separatedChordalGap separated)
    (separatedChordalGap_le_affine separated)
    (separatedEventRequestWidth entry separated)
    (separatedEventRequestWidth_pos entry separated)
    ?_ leftParameterInside rightParameterInside leftDenominatorNonzero
      rightDenominatorNonzero leftPointInside rightPointInside
  simpa only [separatedEventRequestWidth] using
    coefficient_mul_shrinkingWidth_sq_lt
      entry.chart.uniformChordalVariationCoefficient_nonneg
      (separatedChordalGap_pos separated)

/-- Explicit finite evidence that one displayed parameter of a requested
event maps into a rational box.  This is Type-valued data, not a root set or
an ambient existential search. -/
structure RequestMeeting
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      CCL.PersistentCCLBoundaryEvents.BoundaryEventEntry boundary)
    (epsilon : Coordinate) (box : Box) where
  parameter : Coordinate
  parameterInside :
    (entry.request epsilon).cell.interval.Contains parameter
  denominatorNonzero :
    entry.chart.parameterization.curve.denominatorAt parameter ≠ 0
  pointInside :
    box.Contains (entry.chart.parameterization.curve.point parameter)

/-- At the computed width, explicit meetings of one event with two separated
regions are incompatible. -/
theorem separatedEventRequest_meetings_incompatible
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      CCL.PersistentCCLBoundaryEvents.BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox)
    (leftMeeting : RequestMeeting entry
      (separatedEventRequestWidth entry separated) leftBox)
    (rightMeeting : RequestMeeting entry
      (separatedEventRequestWidth entry separated) rightBox) : False :=
  separatedEventRequest_not_spanning entry separated
    leftMeeting.parameterInside rightMeeting.parameterInside
    leftMeeting.denominatorNonzero rightMeeting.denominatorNonzero
    leftMeeting.pointInside rightMeeting.pointInside

/-- Fully executable-width form of the keep-apart theorem: the coefficient
and the finite box gap compute a positive request width at which one event
cannot span the two separated regions. -/
theorem finite_request_not_spanning_separated_boxes
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      CCL.PersistentCCLBoundaryEvents.BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    ∃ epsilon : Coordinate, 0 < epsilon ∧
      ∀ {leftParameter rightParameter : Coordinate},
        (entry.request epsilon).cell.interval.Contains leftParameter →
        (entry.request epsilon).cell.interval.Contains rightParameter →
        entry.chart.parameterization.curve.denominatorAt leftParameter ≠ 0 →
        entry.chart.parameterization.curve.denominatorAt rightParameter ≠ 0 →
        leftBox.Contains
          (entry.chart.parameterization.curve.point leftParameter) →
        rightBox.Contains
          (entry.chart.parameterization.curve.point rightParameter) →
        False := by
  exact ⟨separatedEventRequestWidth entry separated,
    separatedEventRequestWidth_pos entry separated,
    separatedEventRequest_not_spanning entry separated⟩

end CCL.PersistentCCLRegionSeparation
