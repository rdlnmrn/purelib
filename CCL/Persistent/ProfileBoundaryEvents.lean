import mathlib.Data.ConstructiveList
import CCL.Persistent.ConditionProfiles
import CCL.Persistent.RegionOwnership

/-!
# Complete condition-profile event families for one CCL boundary

This module lifts the exact box-condition profiles through the already
complete finite boundary-event family.  It also transports the existing
pointwise locator in the safe direction: a supplied displayed rational
polynomial root is assigned to a computed profile event.  No nonzero Sturm
count is converted into a root-existence statement.
-/

namespace CCL.PersistentCCLProfileBoundaryEvents

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev BoundedChart := CCL.CCLBoundaryCharts.BoundedChart
abbrev SquarefreeFactorAnalysis :=
  CCL.CCLBoundaryCharts.SquarefreeFactorAnalysis
abbrev CurveBoundary := CCL.PersistentCCLDispatch.CurveBoundary
abbrev BoundaryEventEntry
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) :=
  CCL.PersistentCCLBoundaryEvents.BoundaryEventEntry boundary
abbrev ProfileEventEntry
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :=
  CCL.PersistentCCLConditionProfiles.ProfileEventEntry
    factorAnalysis

/-- One condition-profile event with its exact parent in the complete
unsplit boundary-event family. -/
structure BoundaryProfileEventEntry
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) where
  parent : BoundaryEventEntry boundary
  parentMember : parent ∈
    CCL.PersistentCCLBoundaryEvents.boundaryEventFamily boundary
  event : ProfileEventEntry parent.event.1
  eventMember : event ∈
    CCL.PersistentCCLConditionProfiles.profileEventFamily
      parent.event.1

namespace BoundaryProfileEventEntry

def requestAt
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (epsilon : Coordinate) :=
  entry.event.2.request epsilon

def request
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) :=
  entry.requestAt
    (CCL.PersistentCCLConditionProfiles.profileSignWidth
      entry.event.1)

theorem request_width_le
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) :
    entry.request.cell.interval.width ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
      entry.event.1 :=
  entry.event.2.request_width_le _
    (CCL.PersistentCCLConditionProfiles.profileSignWidth_pos
      entry.event.1)

theorem requestAt_width_le
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    (entry.requestAt epsilon).cell.interval.width ≤ epsilon :=
  entry.event.2.request_width_le epsilon positive

/-- The profile event has the same chart-wide homogeneous chordal diameter
bound as its parent event, independently of affine poles. -/
theorem chordalSq_requestAt_le
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    {left right : Coordinate}
    (leftInside : (entry.requestAt epsilon).cell.interval.Contains left)
    (rightInside : (entry.requestAt epsilon).cell.interval.Contains right) :
    CCL.Chordal.chordalSq
        (entry.parent.chart.projective left)
        (entry.parent.chart.projective right) ≤
      entry.parent.chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
  let requested := entry.requestAt epsilon
  have requestedRefines := entry.event.2.request_refines_chart epsilon
  have leftChart : entry.parent.chart.cell.interval.Contains left :=
    ⟨requestedRefines.1.trans leftInside.1,
      leftInside.2.trans requestedRefines.2⟩
  have rightChart : entry.parent.chart.cell.interval.Contains right :=
    ⟨requestedRefines.1.trans rightInside.1,
      rightInside.2.trans requestedRefines.2⟩
  have parameterBound :=
    CCL.RationalCurveBounds.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have widthSquare : requested.cell.interval.width ^ 2 ≤ epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      requested.cell.interval.width_nonneg
      (entry.requestAt_width_le epsilon positive) 2
  exact (entry.parent.chart.chordalSq_le_uniform leftChart rightChart).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      entry.parent.chart.uniformChordalVariationCoefficient_nonneg)

/-- Total affine classification against the boundary's analysis box. -/
def classification
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) :=
  CCL.PersistentCCLConditionProfiles.classifyRequestedProfileEventAffine
    entry.event.2

end BoundaryProfileEventEntry

/-! ## Unique ownership among separated winding regions -/

/-- Positive request width keeping one profile cylinder from spanning two
separated boxes. -/
def separatedProfileRequestWidth
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    Coordinate :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth
    entry.parent.chart.uniformChordalVariationCoefficient
    (CCL.PersistentCCLRegionSeparation.separatedChordalGap
      separated)

theorem separatedProfileRequestWidth_pos
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    0 < separatedProfileRequestWidth entry separated :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth_pos
    entry.parent.chart.uniformChordalVariationCoefficient_nonneg
    (CCL.PersistentCCLRegionSeparation.separatedChordalGap_pos
      separated)

/-- Quantitative profile-event keep-apart theorem at an arbitrary displayed
gap and width. -/
theorem requestedProfileEvent_not_spanning_with_gap
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    {leftBox rightBox : Box} (gap epsilon : Coordinate)
    (gapLower : ∀ {leftPoint rightPoint : Gaussian},
      leftBox.Contains leftPoint → rightBox.Contains rightPoint →
        gap ≤ CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint))
    (epsilonPositive : 0 < epsilon)
    (diameterSmall :
      entry.parent.chart.uniformChordalVariationCoefficient * epsilon ^ 2 <
        gap)
    {leftParameter rightParameter : Coordinate}
    (leftParameterInside :
      (entry.requestAt epsilon).cell.interval.Contains leftParameter)
    (rightParameterInside :
      (entry.requestAt epsilon).cell.interval.Contains rightParameter)
    (leftDenominatorNonzero :
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0)
    (rightDenominatorNonzero :
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0)
    (leftPointInside : leftBox.Contains
      (entry.parent.chart.parameterization.curve.point leftParameter))
    (rightPointInside : rightBox.Contains
      (entry.parent.chart.parameterization.curve.point rightParameter)) :
    False := by
  let curve := entry.parent.chart.parameterization.curve
  let leftPoint := curve.point leftParameter
  let rightPoint := curve.point rightParameter
  have eventUpper := entry.chordalSq_requestAt_le epsilon epsilonPositive
    leftParameterInside rightParameterInside
  have leftTransport :
      CCL.Chordal.chordalSq
          (entry.parent.chart.projective leftParameter)
          (entry.parent.chart.projective rightParameter) =
        CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint)
          (entry.parent.chart.projective rightParameter) := by
    simpa only [curve, leftPoint,
      CCL.CCLBoundaryCharts.BoundedChart.projective] using
      CCL.RationalCurveBounds.chordalSq_projective_eq_affine
        curve leftParameter leftDenominatorNonzero
          (entry.parent.chart.projective rightParameter)
  have rightEquivalent :
      (entry.parent.chart.projective rightParameter).Equivalent
        (CCL.Proj.affine rightPoint) := by
    simpa only [curve, rightPoint,
      CCL.CCLBoundaryCharts.BoundedChart.projective] using
      CCL.RationalCurveBounds.projective_equivalent_affine
        curve rightParameter rightDenominatorNonzero
  have rightTransport :
      CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint)
          (entry.parent.chart.projective rightParameter) =
        CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) :=
    CCL.Chordal.chordalSq_eq_of_equivalent_right
      (entry.parent.chart.projective_valid rightParameter)
      (CCL.Chordal.Proj.affine_hasNonzeroCoordinate rightPoint)
      rightEquivalent (CCL.Proj.affine leftPoint)
  have affineUpper :
      CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) ≤
        entry.parent.chart.uniformChordalVariationCoefficient * epsilon ^ 2 :=
    by
      rw [← rightTransport, ← leftTransport]
      exact eventUpper
  have affineLower : gap ≤
      CCL.Chordal.chordalSq
        (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) :=
    gapLower leftPointInside rightPointInside
  exact (not_lt_of_ge affineLower) (affineUpper.trans_lt diameterSmall)

/-- At the computed finite width, one profile event cannot meet both members
of a separated pair. -/
theorem separatedProfileRequest_not_spanning
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    ∀ {leftParameter rightParameter : Coordinate},
      (entry.requestAt
        (separatedProfileRequestWidth entry separated)).cell.interval.Contains
          leftParameter →
      (entry.requestAt
        (separatedProfileRequestWidth entry separated)).cell.interval.Contains
          rightParameter →
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      leftBox.Contains
        (entry.parent.chart.parameterization.curve.point leftParameter) →
      rightBox.Contains
        (entry.parent.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftInside rightInside leftDenominator
    rightDenominator leftPointInside rightPointInside
  apply requestedProfileEvent_not_spanning_with_gap entry
    (CCL.PersistentCCLRegionSeparation.separatedChordalGap
      separated)
    (separatedProfileRequestWidth entry separated)
    (CCL.PersistentCCLRegionSeparation.separatedChordalGap_le_affine
      separated)
    (separatedProfileRequestWidth_pos entry separated)
    ?_ leftInside rightInside leftDenominator rightDenominator
      leftPointInside rightPointInside
  simpa only [separatedProfileRequestWidth] using
    CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
      entry.parent.chart.uniformChordalVariationCoefficient_nonneg
      (CCL.PersistentCCLRegionSeparation.separatedChordalGap_pos
        separated)

/-- Every ordered distinct pair of a finite separated box family contributes
one profile-event keep-apart width. -/
def profilePairRequestWidths
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    List Coordinate :=
  (List.finRange boxes.length).flatMap fun left =>
    (List.finRange boxes.length).filterMap fun right =>
      if different : left ≠ right then
        some (separatedProfileRequestWidth entry
          (CCL.PersistentCCLRegionOwnership.pairwise_get_separated
            pairwise left right different))
      else none

theorem profilePairRequestWidth_mem
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (left right : Fin boxes.length) (different : left ≠ right) :
    separatedProfileRequestWidth entry
        (CCL.PersistentCCLRegionOwnership.pairwise_get_separated
          pairwise left right different) ∈
      profilePairRequestWidths entry boxes pairwise := by
  rw [profilePairRequestWidths, QuotientFreeList.mem_flatMap]
  refine ⟨left, List.mem_finRange left, ?_⟩
  rw [QuotientFreeList.mem_filterMap]
  refine ⟨right, List.mem_finRange right, ?_⟩
  simp only [dif_pos different]

theorem profilePairRequestWidths_positive
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    ∀ width ∈ profilePairRequestWidths entry boxes pairwise, 0 < width := by
  intro width member
  rw [profilePairRequestWidths, QuotientFreeList.mem_flatMap] at member
  rcases member with ⟨left, _leftMember, member⟩
  rw [QuotientFreeList.mem_filterMap] at member
  rcases member with ⟨right, _rightMember, selected⟩
  split at selected
  next different =>
    have equal := Option.some.inj selected
    rw [← equal]
    exact separatedProfileRequestWidth_pos entry
      (CCL.PersistentCCLRegionOwnership.pairwise_get_separated
        pairwise left right different)
  next same => simp at selected

/-- One positive width below every pairwise keep-apart request for this
profile event. -/
def profileFamilyRequestWidth
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    Coordinate :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum
    (profilePairRequestWidths entry boxes pairwise)

theorem profileFamilyRequestWidth_pos
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    0 < profileFamilyRequestWidth entry boxes pairwise :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_pos _
    (profilePairRequestWidths_positive entry boxes pairwise)

theorem profileFamilyRequestWidth_le_pair
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (left right : Fin boxes.length) (different : left ≠ right) :
    profileFamilyRequestWidth entry boxes pairwise ≤
      separatedProfileRequestWidth entry
        (CCL.PersistentCCLRegionOwnership.pairwise_get_separated
          pairwise left right different) :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
    (profilePairRequestWidth_mem entry boxes pairwise left right different)

/-- One positive rational request width that is simultaneously narrow enough
for every profile sign and every pairwise separated winding region. -/
def combinedProfileRequestWidth
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    Coordinate :=
  min
    (CCL.PersistentCCLConditionProfiles.profileSignWidth
      entry.event.1)
    (profileFamilyRequestWidth entry boxes pairwise)

theorem combinedProfileRequestWidth_pos
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    0 < combinedProfileRequestWidth entry boxes pairwise := by
  exact lt_min
    (CCL.PersistentCCLConditionProfiles.profileSignWidth_pos
      entry.event.1)
    (profileFamilyRequestWidth_pos entry boxes pairwise)

theorem combinedProfileRequestWidth_le_sign
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    combinedProfileRequestWidth entry boxes pairwise ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
        entry.event.1 :=
  min_le_left _ _

theorem combinedProfileRequestWidth_le_family
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    combinedProfileRequestWidth entry boxes pairwise ≤
      profileFamilyRequestWidth entry boxes pairwise :=
  min_le_right _ _

/-- Exact affine box classification at the same finite request width used to
keep all separated winding regions apart.  Root hypotheses remain displayed
rational evaluations; no root existence is inferred from an event count. -/
def classifyCombinedProfileEventAffine
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    CCL.PersistentCCLConditionProfiles.ProfileEventAffineClassification
      entry.event.2 (combinedProfileRequestWidth entry boxes pairwise) :=
  CCL.PersistentCCLConditionProfiles.classifyProfileEventAffine
    entry.event.2 (combinedProfileRequestWidth entry boxes pairwise)
      (combinedProfileRequestWidth_pos entry boxes pairwise)
      (combinedProfileRequestWidth_le_sign entry boxes pairwise)

/-- Any displayed positive width below the family bound keeps one profile
event from meeting two distinct separated winding boxes. -/
theorem profileRequest_not_spanning_of_le_family
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (epsilonLe : epsilon ≤ profileFamilyRequestWidth entry boxes pairwise)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Coordinate},
      (entry.requestAt epsilon).cell.interval.Contains leftParameter →
      (entry.requestAt epsilon).cell.interval.Contains rightParameter →
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.parent.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.parent.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftInside rightInside leftDenominator
    rightDenominator leftPointInside rightPointInside
  let separated :=
    CCL.PersistentCCLRegionOwnership.pairwise_get_separated
      pairwise left right different
  let pairWidth := separatedProfileRequestWidth entry separated
  have widthOrder : epsilon ≤ pairWidth :=
    epsilonLe.trans (by
      simpa only [pairWidth, separated] using
        profileFamilyRequestWidth_le_pair entry boxes pairwise left right
          different)
  have widthSquare : epsilon ^ 2 ≤ pairWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct epsilonPositive.le widthOrder 2
  have coefficientNonnegative :=
    entry.parent.chart.uniformChordalVariationCoefficient_nonneg
  have requestDiameterLe :
      entry.parent.chart.uniformChordalVariationCoefficient *
          epsilon ^ 2 ≤
        entry.parent.chart.uniformChordalVariationCoefficient *
          pairWidth ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct widthSquare
      coefficientNonnegative
  have pairDiameterSmall :
      entry.parent.chart.uniformChordalVariationCoefficient * pairWidth ^ 2 <
        CCL.PersistentCCLRegionSeparation.separatedChordalGap
          separated := by
    simpa only [pairWidth, separatedProfileRequestWidth] using
      CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
        coefficientNonnegative
        (CCL.PersistentCCLRegionSeparation.separatedChordalGap_pos
          separated)
  exact requestedProfileEvent_not_spanning_with_gap entry
    (CCL.PersistentCCLRegionSeparation.separatedChordalGap
      separated)
    epsilon
    (CCL.PersistentCCLRegionSeparation.separatedChordalGap_le_affine
      separated)
    epsilonPositive (requestDiameterLe.trans_lt pairDiameterSmall)
    leftInside rightInside leftDenominator rightDenominator leftPointInside
      rightPointInside

/-- At the single family-wide width, one profile event cannot meet two
distinct separated winding boxes. -/
theorem profileFamilyRequest_not_spanning
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Coordinate},
      (entry.requestAt
        (profileFamilyRequestWidth entry boxes pairwise)).cell.interval.Contains
          leftParameter →
      (entry.requestAt
        (profileFamilyRequestWidth entry boxes pairwise)).cell.interval.Contains
          rightParameter →
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.parent.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.parent.chart.parameterization.curve.point rightParameter) →
      False :=
  profileRequest_not_spanning_of_le_family entry boxes pairwise
    (profileFamilyRequestWidth entry boxes pairwise)
    (profileFamilyRequestWidth_pos entry boxes pairwise) le_rfl left right
      different

/-- At the combined sign-and-separation width, one classified profile event
cannot meet two distinct winding boxes. -/
theorem combinedProfileRequest_not_spanning
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Coordinate},
      (entry.requestAt
        (combinedProfileRequestWidth entry boxes pairwise)).cell.interval.Contains
          leftParameter →
      (entry.requestAt
        (combinedProfileRequestWidth entry boxes pairwise)).cell.interval.Contains
          rightParameter →
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.parent.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.parent.chart.parameterization.curve.point rightParameter) →
      False :=
  profileRequest_not_spanning_of_le_family entry boxes pairwise
    (combinedProfileRequestWidth entry boxes pairwise)
    (combinedProfileRequestWidth_pos entry boxes pairwise)
    (combinedProfileRequestWidth_le_family entry boxes pairwise) left right
      different

/-- Explicit meeting of the family-wide profile request with one finite
winding region. -/
structure ProfileFamilyRequestMeeting
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) where
  index : Fin boxes.length
  parameter : Coordinate
  parameterInside : (entry.requestAt
    (profileFamilyRequestWidth entry boxes pairwise)).cell.interval.Contains
      parameter
  denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0
  pointInside : (boxes.get index).Contains
    (entry.parent.chart.parameterization.curve.point parameter)

/-- Any two explicit owners of the same sufficiently narrow profile event
have the same finite region index. -/
theorem ProfileFamilyRequestMeeting.index_unique
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {entry : BoundaryProfileEventEntry boundary} {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    (left right : ProfileFamilyRequestMeeting entry boxes pairwise) :
    left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (profileFamilyRequest_not_spanning entry boxes pairwise
      left.index right.index same left.parameterInside right.parameterInside
      left.denominatorNonzero right.denominatorNonzero left.pointInside
      right.pointInside).elim

/-- Explicit meeting at the single request width that supports both exact
profile classification and separated-region ownership. -/
structure CombinedProfileRequestMeeting
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) where
  index : Fin boxes.length
  parameter : Coordinate
  parameterInside : (entry.requestAt
    (combinedProfileRequestWidth entry boxes pairwise)).cell.interval.Contains
      parameter
  denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0
  pointInside : (boxes.get index).Contains
    (entry.parent.chart.parameterization.curve.point parameter)

/-- Any two displayed rational meetings at the combined request have the
same finite winding-region index. -/
theorem CombinedProfileRequestMeeting.index_unique
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {entry : BoundaryProfileEventEntry boundary} {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    (left right : CombinedProfileRequestMeeting entry boxes pairwise) :
    left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (combinedProfileRequest_not_spanning entry boxes pairwise
      left.index right.index same left.parameterInside right.parameterInside
      left.denominatorNonzero right.denominatorNonzero left.pointInside
      right.pointInside).elim

/-- Expand every condition profile below one attached unsplit boundary
event. -/
def profileEntriesOfEvent
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (parent : BoundaryEventEntry boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLBoundaryEvents.boundaryEventFamily
        boundary) :
    List (BoundaryProfileEventEntry boundary) :=
  (CCL.PersistentCCLConditionProfiles.profileEventFamily
    parent.event.1).attach.map fun attached =>
      { parent := parent
        parentMember := parentMember
        event := attached.1
        eventMember := attached.2 }

/-- Complete finite family of every nonzero condition-profile event on one
dispatched Hermitian boundary. -/
def boundaryProfileEventFamily
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) : List (BoundaryProfileEventEntry boundary) :=
  (CCL.PersistentCCLBoundaryEvents.boundaryEventFamily
    boundary).attach.flatMap fun attached =>
      profileEntriesOfEvent boundary attached.1 attached.2

theorem mem_boundaryProfileEventFamily
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (parent : BoundaryEventEntry boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLBoundaryEvents.boundaryEventFamily
        boundary)
    (event : ProfileEventEntry parent.event.1)
    (eventMember : event ∈
      CCL.PersistentCCLConditionProfiles.profileEventFamily
        parent.event.1) :
    ({ parent := parent
       parentMember := parentMember
       event := event
       eventMember := eventMember } : BoundaryProfileEventEntry boundary) ∈
      boundaryProfileEventFamily boundary := by
  rw [boundaryProfileEventFamily, QuotientFreeList.mem_flatMap]
  refine ⟨⟨parent, parentMember⟩, QuotientFreeList.mem_attach _ _, ?_⟩
  rw [profileEntriesOfEvent, QuotientFreeList.mem_map]
  exact ⟨⟨event, eventMember⟩, QuotientFreeList.mem_attach _ _, rfl⟩

/-- A supplied displayed rational polynomial root, located in the complete
condition-profile boundary family. -/
structure LocatedBoundaryProfileEvent
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (value : Gaussian) where
  entry : BoundaryProfileEventEntry boundary
  member : entry ∈ boundaryProfileEventFamily boundary
  parameter : Coordinate
  parameterInside : entry.event.2.cell.interval.Contains parameter
  profileZero : entry.event.1.profile.factor.polynomial.eval parameter = 0
  denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0
  point_eq :
    entry.parent.chart.parameterization.curve.point parameter = value

/-- Safe pointwise completeness direction: locate a supplied rational root
in the computed boundary profile family. -/
def locateBoundaryProfileRoot
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (value : Gaussian) (inside : current.Contains value)
    (onBoundary : atom.form.eval value = 0)
    (root : p.eval value = 0)
    (denominatorLower : denominatorMargin ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.RawParser.denominator reference value)) :
    LocatedBoundaryProfileEvent boundary value := by
  let located :=
    CCL.PersistentCCLBoundaryEvents.locateBoundaryRoot
      degreePositive boundary value inside onBoundary root denominatorLower
  have parameterInsideChart :
      located.entry.chart.cell.interval.Contains located.parameter := by
    have refines := located.entry.event.2.cell_refines_chart
    exact ⟨refines.1.trans located.parameterInside.1,
      located.parameterInside.2.trans refines.2⟩
  let profileLocated :=
    CCL.PersistentCCLConditionProfiles.locateProfileEvent
      located.entry.event.1 located.parameter parameterInsideChart
        located.factorZero
  let entry : BoundaryProfileEventEntry boundary :=
    { parent := located.entry
      parentMember := located.member
      event := profileLocated.entry
      eventMember := profileLocated.member }
  exact
    { entry := entry
      member := mem_boundaryProfileEventFamily boundary located.entry
        located.member profileLocated.entry profileLocated.member
      parameter := located.parameter
      parameterInside := profileLocated.contains
      profileZero := profileLocated.profileZero
      denominatorNonzero := located.denominatorNonzero
      point_eq := located.point_eq }

end CCL.PersistentCCLProfileBoundaryEvents
