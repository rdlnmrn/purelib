import mathlib.Data.ConstructiveList
import CCL.Persistent.RegionSeparation

/-!
# Finite ownership of persistent CCL events

One boundary-event request must be compared with a complete finite family of
pairwise-separated winding regions, not just one selected pair.  This module
computes a single positive rational request width below every pair-specific
width and proves uniqueness of any explicit region meeting at that request.

The construction folds finite lists of displayed rationals.  It introduces
no root set, completed point, infinite minimum, or choice operation.
-/

namespace CCL.PersistentCCLRegionOwnership

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev CurveBoundary := CCL.PersistentCCLDispatch.CurveBoundary
abbrev Separated (left right : Box) := left.Separated right
abbrev BoundaryEventEntry
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) :=
  CCL.PersistentCCLBoundaryEvents.BoundaryEventEntry boundary
abbrev RequestMeeting
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (epsilon : Coordinate) (box : Box) :=
  CCL.PersistentCCLRegionSeparation.RequestMeeting
    entry epsilon box

/-- Minimum of an explicit finite list, with `1` as the empty-family width. -/
def finitePositiveMinimum (values : List Coordinate) : Coordinate :=
  values.foldr min 1

theorem finitePositiveMinimum_pos
    (values : List Coordinate) (positive : ∀ value ∈ values, 0 < value) :
    0 < finitePositiveMinimum values := by
  induction values with
  | nil => exact (by decide)
  | cons head tail inductionHypothesis =>
      rw [finitePositiveMinimum, List.foldr_cons]
      exact lt_min (positive head (by simp))
        (inductionHypothesis fun value member =>
          positive value (by simp [member]))

theorem finitePositiveMinimum_le_of_mem
    {values : List Coordinate} {value : Coordinate}
    (member : value ∈ values) : finitePositiveMinimum values ≤ value := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [finitePositiveMinimum, List.foldr_cons]
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans
          (inductionHypothesis tailMember)

/-- Pairwise list separation, made symmetric for arbitrary distinct finite
indices. -/
theorem pairwise_get_separated
    {boxes : List Box} (pairwise : boxes.Pairwise Separated)
    (left right : Fin boxes.length) (different : left ≠ right) :
    (boxes.get left).Separated (boxes.get right) := by
  by_cases ordered : left.val < right.val
  · exact QuotientFreeList.pairwise_getElem pairwise left.val right.val
      left.isLt right.isLt ordered
  · have unequalValues : left.val ≠ right.val :=
      fun equal => different (Fin.ext equal)
    have reversed : right.val < left.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt ordered) unequalValues.symm
    exact RFAP.Boxes.Box.separated_symm
      (QuotientFreeList.pairwise_getElem pairwise right.val left.val
        right.isLt left.isLt reversed)

/-- Every ordered distinct pair contributes its executable event request
width to one finite list.  Duplicate orientations are harmless. -/
def pairRequestWidths
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated) : List Coordinate :=
  (List.finRange boxes.length).flatMap fun left =>
    (List.finRange boxes.length).filterMap fun right =>
      if different : left ≠ right then
        some
          (CCL.PersistentCCLRegionSeparation.separatedEventRequestWidth
            entry (pairwise_get_separated pairwise left right different))
      else
        none

theorem pairRequestWidth_mem
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated)
    (left right : Fin boxes.length) (different : left ≠ right) :
    CCL.PersistentCCLRegionSeparation.separatedEventRequestWidth
        entry (pairwise_get_separated pairwise left right different) ∈
      pairRequestWidths entry boxes pairwise := by
  rw [pairRequestWidths, QuotientFreeList.mem_flatMap]
  refine ⟨left, List.mem_finRange left, ?_⟩
  rw [QuotientFreeList.mem_filterMap]
  refine ⟨right, List.mem_finRange right, ?_⟩
  simp only [dif_pos different]

theorem pairRequestWidths_positive
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated) :
    ∀ width ∈ pairRequestWidths entry boxes pairwise, 0 < width := by
  intro width member
  rw [pairRequestWidths, QuotientFreeList.mem_flatMap] at member
  rcases member with ⟨left, _leftMember, member⟩
  rw [QuotientFreeList.mem_filterMap] at member
  rcases member with ⟨right, _rightMember, selected⟩
  split at selected
  next different =>
    have equal := Option.some.inj selected
    rw [← equal]
    exact
      CCL.PersistentCCLRegionSeparation.separatedEventRequestWidth_pos
        entry (pairwise_get_separated pairwise left right different)
  next same => simp at selected

/-- One positive width below every pair-specific keep-apart request. -/
def familyEventRequestWidth
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated) : Coordinate :=
  finitePositiveMinimum (pairRequestWidths entry boxes pairwise)

theorem familyEventRequestWidth_pos
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated) :
    0 < familyEventRequestWidth entry boxes pairwise :=
  finitePositiveMinimum_pos _
    (pairRequestWidths_positive entry boxes pairwise)

theorem familyEventRequestWidth_le_pair
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated)
    (left right : Fin boxes.length) (different : left ≠ right) :
    familyEventRequestWidth entry boxes pairwise ≤
      CCL.PersistentCCLRegionSeparation.separatedEventRequestWidth
        entry (pairwise_get_separated pairwise left right different) :=
  finitePositiveMinimum_le_of_mem
    (pairRequestWidth_mem entry boxes pairwise left right different)

/-- At the family-wide request width, one event cannot explicitly meet two
distinct members of the separated family. -/
theorem familyEventRequest_not_spanning
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Coordinate},
      (entry.request (familyEventRequestWidth entry boxes pairwise)).cell.interval.Contains
        leftParameter →
      (entry.request (familyEventRequestWidth entry boxes pairwise)).cell.interval.Contains
        rightParameter →
      entry.chart.parameterization.curve.denominatorAt leftParameter ≠ 0 →
      entry.chart.parameterization.curve.denominatorAt rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftParameterInside rightParameterInside
    leftDenominatorNonzero rightDenominatorNonzero leftPointInside
    rightPointInside
  let separated := pairwise_get_separated pairwise left right different
  let familyWidth := familyEventRequestWidth entry boxes pairwise
  let pairWidth :=
    CCL.PersistentCCLRegionSeparation.separatedEventRequestWidth
      entry separated
  have familyPositive : 0 < familyWidth :=
    familyEventRequestWidth_pos entry boxes pairwise
  have pairPositive : 0 < pairWidth :=
    CCL.PersistentCCLRegionSeparation.separatedEventRequestWidth_pos
      entry separated
  have widthOrder : familyWidth ≤ pairWidth := by
    simpa only [familyWidth, pairWidth, separated] using
      familyEventRequestWidth_le_pair entry boxes pairwise left right different
  have squareOrder : familyWidth ^ 2 ≤ pairWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct familyPositive.le widthOrder 2
  have coefficientNonnegative :=
    entry.chart.uniformChordalVariationCoefficient_nonneg
  have familyDiameterLe :
      entry.chart.uniformChordalVariationCoefficient * familyWidth ^ 2 ≤
        entry.chart.uniformChordalVariationCoefficient * pairWidth ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareOrder
      coefficientNonnegative
  have pairDiameterSmall :
      entry.chart.uniformChordalVariationCoefficient * pairWidth ^ 2 <
        CCL.PersistentCCLRegionSeparation.separatedChordalGap
          separated := by
    simpa only [pairWidth,
      CCL.PersistentCCLRegionSeparation.separatedEventRequestWidth]
      using
        CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
          coefficientNonnegative
          (CCL.PersistentCCLRegionSeparation.separatedChordalGap_pos
            separated)
  exact
    CCL.PersistentCCLRegionSeparation.requested_event_not_spanning_with_gap
      entry
      (CCL.PersistentCCLRegionSeparation.separatedChordalGap
        separated)
      (CCL.PersistentCCLRegionSeparation.separatedChordalGap_le_affine
        separated)
      familyWidth familyPositive (familyDiameterLe.trans_lt pairDiameterSmall)
      leftParameterInside rightParameterInside leftDenominatorNonzero
      rightDenominatorNonzero leftPointInside rightPointInside

/-- A finite region index together with its explicit meeting certificate. -/
structure FamilyRequestMeeting
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated) where
  index : Fin boxes.length
  meeting : RequestMeeting entry
    (familyEventRequestWidth entry boxes pairwise) (boxes.get index)

/-- The family-wide request admits at most one explicitly witnessed owner. -/
theorem FamilyRequestMeeting.index_unique
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {entry : BoundaryEventEntry boundary} {boxes : List Box}
    {pairwise : boxes.Pairwise Separated}
    (left right : FamilyRequestMeeting entry boxes pairwise) :
    left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (familyEventRequest_not_spanning entry boxes pairwise
      left.index right.index same
      left.meeting.parameterInside right.meeting.parameterInside
      left.meeting.denominatorNonzero right.meeting.denominatorNonzero
      left.meeting.pointInside right.meeting.pointInside).elim

/-! ## Executable classification of one displayed event sample -/

/-- A denominator-safe rational parameter computed inside one requested
event interval. -/
structure NonpoleRequestSample
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (epsilon : Coordinate) where
  parameter : Coordinate
  parameterInside : (entry.request epsilon).cell.interval.Contains parameter
  denominatorNonzero :
    entry.chart.parameterization.curve.denominatorAt parameter ≠ 0

/-- Execute a bounded interior search against the represented denominator
quadrance.  Chart nondegeneracy proves that polynomial is nonzero, and the
selected nonzero evaluation is exactly a non-pole affine parameter. -/
def nonpoleRequestSample
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (epsilon : Coordinate) :
    NonpoleRequestSample entry epsilon := by
  let curve := entry.chart.parameterization.curve
  let interval := (entry.request epsilon).cell.interval
  let denominatorPolynomial :=
    CCL.CurveBoxConditions.denominatorNormSq curve
  have chartMember :=
    CCL.PersistentCCLCurveClear.chart_mem_of_analysis_mem
      boundary entry.analysisMember
  have nondegenerate :=
    CCL.CCLChartNondegenerate.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive entry.chart
        chartMember
  have intervalProper : interval.lower < interval.upper := by
    simpa only [interval] using (entry.request epsilon).cell.proper
  let parameter := RFAP.SafeCandidates.interiorSearchValue
    denominatorPolynomial denominatorPolynomial.natDegree intervalProper
      nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  have specification :=
    RFAP.SafeCandidates.interiorSearchValue_spec
      denominatorPolynomial denominatorPolynomial.natDegree intervalProper
        nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  exact
    { parameter := parameter
      parameterInside := ⟨specification.2.1.le, specification.2.2.le⟩
      denominatorNonzero := by
        intro denominatorZero
        apply specification.1
        change denominatorPolynomial.eval parameter = 0
        rw [show denominatorPolynomial.eval parameter =
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (curve.denominatorAt parameter) by
              exact CCL.CurveBoxConditions.eval_denominatorNormSq
                curve parameter,
          denominatorZero,
          RFAP.ConstructiveGaussian.Gaussian.normSq_zero] }

/-- First finite box containing a displayed rational point. -/
def findContainingBoxIndex (boxes : List Box) (point :
    RFAP.ConstructiveGaussian.Gaussian) : Option (Fin boxes.length) :=
  match boxes with
  | [] => none
  | head :: tail =>
      if head.Contains point then
        some 0
      else
        match findContainingBoxIndex tail point with
        | none => none
        | some index => some index.succ

theorem findContainingBoxIndex_sound
    (boxes : List Box) (point : RFAP.ConstructiveGaussian.Gaussian)
    (index : Fin boxes.length)
    (found : findContainingBoxIndex boxes point = some index) :
    (boxes.get index).Contains point := by
  induction boxes with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      by_cases headContains : head.Contains point
      · rw [findContainingBoxIndex, if_pos headContains] at found
        have indexZero : index = 0 := Option.some.inj found.symm
        subst index
        exact headContains
      · rw [findContainingBoxIndex, if_neg headContains] at found
        cases recursive : findContainingBoxIndex tail point with
        | none => rw [recursive] at found; contradiction
        | some tailIndex =>
            rw [recursive] at found
            have indexSucc : index = tailIndex.succ :=
              Option.some.inj found.symm
            subst index
            exact inductionHypothesis tailIndex recursive

theorem findContainingBoxIndex_none
    (boxes : List Box) (point : RFAP.ConstructiveGaussian.Gaussian)
    (found : findContainingBoxIndex boxes point = none) :
    ∀ index : Fin boxes.length, ¬(boxes.get index).Contains point := by
  induction boxes with
  | nil => intro index; exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      by_cases headContains : head.Contains point
      · rw [findContainingBoxIndex, if_pos headContains] at found
        contradiction
      · rw [findContainingBoxIndex, if_neg headContains] at found
        cases recursive : findContainingBoxIndex tail point with
        | some index => rw [recursive] at found; contradiction
        | none =>
            intro index
            refine Fin.cases headContains ?_ index
            intro tailIndex
            exact inductionHypothesis recursive tailIndex

/-- Total finite result for one explicit non-pole parameter in the
family-wide event request: either its affine curve point has a uniquely
determined region owner, or it is certified outside every displayed box. -/
inductive SampleRegionClassification
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated)
    (parameter : Coordinate)
    (parameterInside :
      (entry.request (familyEventRequestWidth entry boxes pairwise)).cell.interval.Contains
        parameter)
    (denominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt parameter ≠ 0) where
  | meeting (owner : FamilyRequestMeeting entry boxes pairwise)
  | outside (proof : ∀ index : Fin boxes.length,
      ¬(boxes.get index).Contains
        (entry.chart.parameterization.curve.point parameter))

/-- Execute all finite box-membership comparisons for one displayed event
sample and retain either its owner certificate or all negative results. -/
def classifySample
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated)
    (parameter : Coordinate)
    (parameterInside :
      (entry.request (familyEventRequestWidth entry boxes pairwise)).cell.interval.Contains
        parameter)
    (denominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt parameter ≠ 0) :
    SampleRegionClassification entry boxes pairwise parameter
      parameterInside denominatorNonzero := by
  let point := entry.chart.parameterization.curve.point parameter
  match found : findContainingBoxIndex boxes point with
  | some index =>
      exact .meeting
        { index := index
          meeting :=
            { parameter := parameter
              parameterInside := parameterInside
              denominatorNonzero := denominatorNonzero
              pointInside := findContainingBoxIndex_sound boxes point index
                found } }
  | none =>
      exact .outside (findContainingBoxIndex_none boxes point found)

/-- Fully computed sample/classification pair for one family-wide event
request. -/
structure RequestedEventSampleClassification
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated) where
  sample : NonpoleRequestSample entry
    (familyEventRequestWidth entry boxes pairwise)
  classification : SampleRegionClassification entry boxes pairwise
    sample.parameter sample.parameterInside sample.denominatorNonzero

/-- Compute a non-pole parameter in the family-wide request and immediately
classify its affine point against every displayed region. -/
def classifyRequestedEventSample
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise Separated) :
    RequestedEventSampleClassification entry boxes pairwise :=
  let sample := nonpoleRequestSample entry
    (familyEventRequestWidth entry boxes pairwise)
  { sample := sample
    classification := classifySample entry boxes pairwise sample.parameter
      sample.parameterInside sample.denominatorNonzero }

end CCL.PersistentCCLRegionOwnership
