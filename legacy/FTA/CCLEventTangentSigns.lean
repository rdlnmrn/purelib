import FTA.CCLCountOneClassification
import FTA.CCLIncrementalOwnerShapes
import FTA.CCLPathTangent
import FTA.CCLPositiveEventApproximation
import FTA.CCLPositiveEventSemantics

/-!
# Classified tangent signs for a selected positive event

All cleared directional slopes of the selected incremental owner faces are
classified in one shared-factor tree.  The count-one follower retains the
same algebraic event while the common coprime refinement assigns every
nonzero slope a stable sign.  Thus a successful finite canonical table entry
is a genuine planar tangent direction at every rational parameter in the
final refined cell.
-/

namespace FTA
namespace CCLEventTangentSigns

open CCL CCL.GaussianRat
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLCountOneClassification
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLIntersectionSharedFactors
open FTA.CCLIncrementalOwnerShapes
open FTA.CCLMultiOwnerGrid
open FTA.CCLNextBitFormula
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPathTangent
open FTA.CCLPathIntersection
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventApproximation
open FTA.ComputablePolynomial
open FTA.ProjectivePath
open FTA.RationalPolynomialBounds
open FTA.RootCountDivisibility
open FTA.RootTrackSeparation
open FTA.SturmTransducer

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI
abbrev RatPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial ℚ

def selectedPath
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : Path :=
  selected.candidate.sourceEvent.partition.entry.chart.path

@[simp] theorem selectedPath_toIncrementalPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : SelectedEventPayload output) :
    selectedPath selected.toIncrementalPayload =
      selected.candidate.sourceEvent.partition.entry.chart.path := rfl

/-- All active-form slopes, grouped by the fixed eight-direction table. -/
def selectedSlopeConditions
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : List RatPolynomial :=
  coordinateDirections.flatMap fun direction =>
    (eventPayloadIncrementalActiveOwnerForms selected).map fun form =>
      clearedDirectionalSlope form (selectedPath selected) direction

theorem clearedDirectionalSlope_mem_selectedSlopeConditions
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {direction : QI}
    (directionMember : direction ∈ coordinateDirections)
    {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    clearedDirectionalSlope form (selectedPath selected) direction ∈
      selectedSlopeConditions selected := by
  rw [selectedSlopeConditions, List.mem_flatMap]
  refine ⟨direction, directionMember, ?_⟩
  exact List.mem_map.mpr ⟨form, formMember, rfl⟩

/-- The unique count-one slope-sign descendant of the selected parser event. -/
def selectedSlopeClassification
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :=
  followCountOneConditions selected.candidate.inputCell.branch.factor
    (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined
    (selectedSlopeConditions selected)

def selectedSlopeSigns
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :=
  (selectedSlopeClassification selected).branch.computeEventSigns
    (selectedSlopeClassification selected).parent

/-- A nondegenerate active boundary cannot have both cleared gradient
coordinates vanish on the final classified event factor.  Otherwise the
gradient-discriminant identity and the already certified projective-
denominator coprimality would make that nonconstant factor a unit. -/
theorem selectedActive_clearedGradient_not_both_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    ¬((selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedGradientX form (selectedPath selected)).toPolynomial ∧
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedGradientY form (selectedPath selected)).toPolynomial) := by
  intro bothDivides
  let classification := selectedSlopeClassification selected
  let path := selectedPath selected
  let factor := classification.branch.factor.polynomial.toPolynomial
  let denominator := (denominatorNorm path).toPolynomial
  have factorDividesSelected :
      factor ∣ selected.candidate.inputCell.branch.factor.polynomial.toPolynomial :=
    classification.divides
  have factorDividesEvent :
      factor ∣ selected.candidate.sourceEvent.event.branch.factor.polynomial.toPolynomial :=
    factorDividesSelected.trans selected.candidate.inputCell.divides
  let denominatorCondition := denominatorCoprimeCondition
    selected.candidate.sourceEvent.event.branch
    selected.candidate.sourceEvent.event.denominatorNonEquality
  have eventCoprimeDenominator : IsCoprime
      selected.candidate.sourceEvent.event.branch.factor.polynomial.toPolynomial
      denominator := by
    have certificate := denominatorCondition.coprime.isCoprime
    simpa [denominatorCondition, denominator, path, selectedPath,
      denominatorCoprimeCondition_polynomial] using certificate
  have factorCoprimeDenominator : IsCoprime factor denominator :=
    eventCoprimeDenominator.of_isCoprime_of_dvd_left factorDividesEvent
  have factorCoprimeDenominatorSq :
      IsCoprime factor (denominator * denominator) :=
    factorCoprimeDenominator.mul_right factorCoprimeDenominator
  have factorDividesForm :
      factor ∣ (clearedForm form path).toPolynomial :=
    factorDividesSelected.trans
      (selectedActivePolynomial_dvd selected formMember)
  have factorDividesLeft : factor ∣
      (DensePolynomial.scale (4 * form.radial)
        (clearedForm form path * denominatorNorm path)).toPolynomial := by
    simp only [DensePolynomial.toPolynomial_scale,
      DensePolynomial.toPolynomial_mul]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left factorDividesForm denominator) _
  rw [clearedGradient_discriminant_identity] at factorDividesLeft
  simp only [DensePolynomial.toPolynomial_add,
    DensePolynomial.toPolynomial_mul, DensePolynomial.toPolynomial_scale]
      at factorDividesLeft
  have factorDividesGradientSum : factor ∣
      (clearedGradientX form path).toPolynomial *
          (clearedGradientX form path).toPolynomial +
        (clearedGradientY form path).toPolynomial *
          (clearedGradientY form path).toPolynomial :=
    dvd_add (dvd_mul_of_dvd_left bothDivides.1 _)
      (dvd_mul_of_dvd_left bothDivides.2 _)
  have factorDividesDiscriminant : factor ∣
      Polynomial.C (boundaryDiscriminant form) *
        (denominator * denominator) := by
    have difference := dvd_sub factorDividesLeft factorDividesGradientSum
    simpa [denominator] using difference
  have discriminantUnit :
      IsUnit (Polynomial.C (boundaryDiscriminant form)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr discriminantNonzero)
  have factorCoprimeDiscriminant : IsCoprime factor
      (Polynomial.C (boundaryDiscriminant form) *
        (denominator * denominator)) :=
    (isCoprime_mul_unit_left_right discriminantUnit factor
      (denominator * denominator)).2 factorCoprimeDenominatorSq
  have factorUnit :=
    factorCoprimeDiscriminant.isUnit_of_dvd factorDividesDiscriminant
  have degree := Polynomial.natDegree_eq_zero_of_isUnit factorUnit
  rw [DensePolynomial.natDegree_toPolynomial
    classification.branch.factor.input.nonzero] at degree
  exact classification.branch.factor.input.nonconstant degree

/-- Canonical strict-sign representative of one cleared slope on the final
count-one descendant. -/
def selectedSlopeValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (form : HermitianForm) (direction : QI) : ℚ :=
  canonicalEventValue
    (selectedSlopeClassification selected).branch.factor.input
    (clearedDirectionalSlope form (selectedPath selected) direction)
    (selectedSlopeSigns selected).refined.interval.lower

/-- Canonical zero is exactly divisibility by the final classified event
factor for every slope included in the shared sign table. -/
theorem selectedSlopeValue_eq_zero_iff_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected)
    {direction : QI} (directionMember : direction ∈ coordinateDirections) :
    selectedSlopeValue selected form direction = 0 ↔
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedDirectionalSlope form (selectedPath selected)
          direction).toPolynomial := by
  let classification := selectedSlopeClassification selected
  let signs := selectedSlopeSigns selected
  have polynomialMember :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      directionMember formMember
  constructor
  · intro zero
    exact ConditionRelations.dvd_of_canonicalEventValue_eq_zero
      classification.branch.relations classification.parent signs
      polynomialMember (by
        simpa [selectedSlopeValue, classification, signs] using zero)
  · intro divides
    exact canonicalEventValue_eq_zero_of_dvd
      classification.branch.factor.input _ _ divides

/-- A nonzero classified slope can be cancelled from a product divisible by
the final event factor.  This is the zero-component propagation rule used by
the orthogonal-pair sign table. -/
theorem selectedSlopeValue_eq_zero_of_mul_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {leftForm rightForm : HermitianForm}
    (leftFormMember : leftForm ∈ eventPayloadIncrementalActiveOwnerForms selected)
    {leftDirection rightDirection : QI}
    (leftDirectionMember : leftDirection ∈ coordinateDirections)
    (leftNonzero :
      selectedSlopeValue selected leftForm leftDirection ≠ 0)
    (divides :
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedDirectionalSlope leftForm (selectedPath selected)
            leftDirection).toPolynomial *
          (clearedDirectionalSlope rightForm (selectedPath selected)
            rightDirection).toPolynomial) :
    selectedSlopeValue selected rightForm rightDirection = 0 := by
  let classification := selectedSlopeClassification selected
  let signs := selectedSlopeSigns selected
  let leftPolynomial :=
    clearedDirectionalSlope leftForm (selectedPath selected) leftDirection
  let rightPolynomial :=
    clearedDirectionalSlope rightForm (selectedPath selected) rightDirection
  have leftMember : leftPolynomial ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      leftDirectionMember leftFormMember
  have zero :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_eq_zero_of_dvd_mul_left
      classification.branch.relations signs.refined.interval.lower leftMember
      (by simpa [selectedSlopeValue, classification, signs, leftPolynomial]
        using leftNonzero)
      (by simpa [classification, leftPolynomial, rightPolynomial] using divides)
  simpa [selectedSlopeValue, classification, signs, rightPolynomial] using zero

/-- Right-factor version of the same cancellation rule. -/
theorem selectedSlopeValue_eq_zero_of_mul_dvd_right
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {leftForm rightForm : HermitianForm}
    (rightFormMember : rightForm ∈ eventPayloadIncrementalActiveOwnerForms selected)
    {leftDirection rightDirection : QI}
    (rightDirectionMember : rightDirection ∈ coordinateDirections)
    (rightNonzero :
      selectedSlopeValue selected rightForm rightDirection ≠ 0)
    (divides :
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedDirectionalSlope leftForm (selectedPath selected)
            leftDirection).toPolynomial *
          (clearedDirectionalSlope rightForm (selectedPath selected)
            rightDirection).toPolynomial) :
    selectedSlopeValue selected leftForm leftDirection = 0 := by
  let classification := selectedSlopeClassification selected
  let signs := selectedSlopeSigns selected
  let leftPolynomial :=
    clearedDirectionalSlope leftForm (selectedPath selected) leftDirection
  let rightPolynomial :=
    clearedDirectionalSlope rightForm (selectedPath selected) rightDirection
  have rightMember : rightPolynomial ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      rightDirectionMember rightFormMember
  have zero :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_eq_zero_of_dvd_mul_right
      classification.branch.relations signs.refined.interval.lower rightMember
      (by simpa [selectedSlopeValue, classification, signs, rightPolynomial]
        using rightNonzero)
      (by simpa [classification, leftPolynomial, rightPolynomial] using divides)
  simpa [selectedSlopeValue, classification, signs, leftPolynomial] using zero

/-- A nondegenerate active boundary has a nonzero classified horizontal or
vertical slope coordinate. -/
theorem selectedActive_axis_values_not_both_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    selectedSlopeValue selected form ⟨1, 0⟩ ≠ 0 ∨
      selectedSlopeValue selected form ⟨0, 1⟩ ≠ 0 := by
  by_contra neither
  push Not at neither
  apply selectedActive_clearedGradient_not_both_dvd selected formMember
    discriminantNonzero
  constructor
  · simpa using (selectedSlopeValue_eq_zero_iff_dvd selected formMember
      (direction := ⟨1, 0⟩) (by simp [coordinateDirections])).1 neither.1
  · simpa using (selectedSlopeValue_eq_zero_iff_dvd selected formMember
      (direction := ⟨0, 1⟩) (by simp [coordinateDirections])).1 neither.2

/-- Negating one classified slope polynomial negates its strict canonical
sign.  The proof uses the common-sign interval, so it is independent of the
implementation choices made by the two gcd classifications. -/
theorem selectedSlopeValue_opposite_pos_of_neg
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected)
    {direction opposite : QI}
    (directionMember : direction ∈ coordinateDirections)
    (oppositeMember : opposite ∈ coordinateDirections)
    (polynomialOpposite :
      (clearedDirectionalSlope form (selectedPath selected)
          opposite).toPolynomial =
        -(clearedDirectionalSlope form (selectedPath selected)
          direction).toPolynomial)
    (negative : selectedSlopeValue selected form direction < 0) :
    0 < selectedSlopeValue selected form opposite := by
  let classification := selectedSlopeClassification selected
  let signs := selectedSlopeSigns selected
  have directionPolynomialMember :
      clearedDirectionalSlope form (selectedPath selected) direction ∈
        selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      directionMember formMember
  have oppositePolynomialMember :
      clearedDirectionalSlope form (selectedPath selected) opposite ∈
        selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      oppositeMember formMember
  have positive :=
    ConditionRelations.canonicalEventValue_pos_of_polynomial_neg
      classification.branch.relations classification.parent signs
      directionPolynomialMember oppositePolynomialMember polynomialOpposite
      (by simpa [selectedSlopeValue, classification, signs] using negative)
  simpa [selectedSlopeValue, classification, signs] using positive

/-- A positive classified slope remains positive after a positive rescaling
and addition of a slope which vanishes on the selected event factor.  This is
the algebraic adapter used for the half-diagonal entries of the finite tangent
table. -/
theorem selectedSlopeValue_pos_of_direction_combination
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected)
    {source target zeroDirection : QI}
    (sourceMember : source ∈ coordinateDirections)
    (targetMember : target ∈ coordinateDirections)
    (zeroMember : zeroDirection ∈ coordinateDirections)
    (scale errorScale : ℚ) (scalePositive : 0 < scale)
    (realCombination :
      target.re = scale * source.re + errorScale * zeroDirection.re)
    (imagCombination :
      target.im = scale * source.im + errorScale * zeroDirection.im)
    (zeroValue : selectedSlopeValue selected form zeroDirection = 0)
    (sourcePositive : 0 < selectedSlopeValue selected form source) :
    0 < selectedSlopeValue selected form target := by
  let classification := selectedSlopeClassification selected
  let signs := selectedSlopeSigns selected
  let sourcePolynomial :=
    clearedDirectionalSlope form (selectedPath selected) source
  let targetPolynomial :=
    clearedDirectionalSlope form (selectedPath selected) target
  let zeroPolynomial :=
    clearedDirectionalSlope form (selectedPath selected) zeroDirection
  let errorPolynomial := DensePolynomial.scale errorScale zeroPolynomial
  have sourcePolynomialMember : sourcePolynomial ∈
      selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected sourceMember
      formMember
  have targetPolynomialMember : targetPolynomial ∈
      selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected targetMember
      formMember
  have zeroDivides : classification.branch.factor.polynomial.toPolynomial ∣
      zeroPolynomial.toPolynomial := by
    exact (selectedSlopeValue_eq_zero_iff_dvd selected formMember zeroMember).1
      zeroValue
  have errorDivides : classification.branch.factor.polynomial.toPolynomial ∣
      errorPolynomial.toPolynomial := by
    simp only [errorPolynomial, DensePolynomial.toPolynomial_scale]
    exact dvd_mul_of_dvd_right zeroDivides _
  have polynomialIdentity : targetPolynomial.toPolynomial =
      Polynomial.C scale * sourcePolynomial.toPolynomial +
        errorPolynomial.toPolynomial := by
    simp only [targetPolynomial, sourcePolynomial, zeroPolynomial,
      errorPolynomial, clearedDirectionalSlope,
      DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_scale]
    rw [realCombination, imagCombination]
    simp only [map_add, map_mul]
    ring
  have positive :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_pos_of_positive_scale_mod
      classification.branch.relations classification.parent signs
      sourcePolynomialMember targetPolynomialMember scale scalePositive
      polynomialIdentity errorDivides
      (by simpa [selectedSlopeValue, classification, signs,
        sourcePolynomial] using sourcePositive)
  simpa [selectedSlopeValue, classification, signs, targetPolynomial] using
    positive

/-- If one active gradient is vertically directed on the event and another
is horizontally directed, one of the four half-diagonals has positive
classified slope for both. -/
theorem exists_classified_diagonal_direction_of_axis_zeros
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {vertical horizontal : HermitianForm}
    (verticalMember :
      vertical ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (horizontalMember :
      horizontal ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (verticalEastZero :
      selectedSlopeValue selected vertical ⟨1, 0⟩ = 0)
    (horizontalNorthZero :
      selectedSlopeValue selected horizontal ⟨0, 1⟩ = 0)
    (verticalNorthNonzero :
      selectedSlopeValue selected vertical ⟨0, 1⟩ ≠ 0)
    (horizontalEastNonzero :
      selectedSlopeValue selected horizontal ⟨1, 0⟩ ≠ 0) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedSlopeValue selected vertical direction ∧
        0 < selectedSlopeValue selected horizontal direction := by
  have verticalSouthPositive
      (northNegative : selectedSlopeValue selected vertical ⟨0, 1⟩ < 0) :
      0 < selectedSlopeValue selected vertical ⟨0, -1⟩ :=
    selectedSlopeValue_opposite_pos_of_neg selected verticalMember
      (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
      (by simp [coordinateDirections]) (by simp [coordinateDirections])
      (by simp) northNegative
  have horizontalWestPositive
      (eastNegative : selectedSlopeValue selected horizontal ⟨1, 0⟩ < 0) :
      0 < selectedSlopeValue selected horizontal ⟨-1, 0⟩ :=
    selectedSlopeValue_opposite_pos_of_neg selected horizontalMember
      (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
      (by simp [coordinateDirections]) (by simp [coordinateDirections])
      (by simp) eastNegative
  rcases lt_or_gt_of_ne verticalNorthNonzero with
      verticalNorthNegative | verticalNorthPositive
  · have verticalSouth := verticalSouthPositive verticalNorthNegative
    rcases lt_or_gt_of_ne horizontalEastNonzero with
        horizontalEastNegative | horizontalEastPositive
    · have horizontalWest := horizontalWestPositive horizontalEastNegative
      refine ⟨⟨-1 / 2, -1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · exact selectedSlopeValue_pos_of_direction_combination selected
          verticalMember (source := ⟨0, -1⟩) (target := ⟨-1 / 2, -1 / 2⟩)
          (zeroDirection := ⟨1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (-1 / 2) (by norm_num)
          (by norm_num) (by norm_num) verticalEastZero verticalSouth
      · exact selectedSlopeValue_pos_of_direction_combination selected
          horizontalMember (source := ⟨-1, 0⟩)
          (target := ⟨-1 / 2, -1 / 2⟩) (zeroDirection := ⟨0, 1⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (-1 / 2) (by norm_num)
          (by norm_num) (by norm_num) horizontalNorthZero horizontalWest
    · refine ⟨⟨1 / 2, -1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · exact selectedSlopeValue_pos_of_direction_combination selected
          verticalMember (source := ⟨0, -1⟩) (target := ⟨1 / 2, -1 / 2⟩)
          (zeroDirection := ⟨1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (1 / 2) (by norm_num)
          (by norm_num) (by norm_num) verticalEastZero verticalSouth
      · exact selectedSlopeValue_pos_of_direction_combination selected
          horizontalMember (source := ⟨1, 0⟩)
          (target := ⟨1 / 2, -1 / 2⟩) (zeroDirection := ⟨0, 1⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (-1 / 2) (by norm_num)
          (by norm_num) (by norm_num) horizontalNorthZero
          horizontalEastPositive
  · rcases lt_or_gt_of_ne horizontalEastNonzero with
        horizontalEastNegative | horizontalEastPositive
    · have horizontalWest := horizontalWestPositive horizontalEastNegative
      refine ⟨⟨-1 / 2, 1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · exact selectedSlopeValue_pos_of_direction_combination selected
          verticalMember (source := ⟨0, 1⟩) (target := ⟨-1 / 2, 1 / 2⟩)
          (zeroDirection := ⟨1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (-1 / 2) (by norm_num)
          (by norm_num) (by norm_num) verticalEastZero verticalNorthPositive
      · exact selectedSlopeValue_pos_of_direction_combination selected
          horizontalMember (source := ⟨-1, 0⟩)
          (target := ⟨-1 / 2, 1 / 2⟩) (zeroDirection := ⟨0, 1⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (1 / 2) (by norm_num)
          (by norm_num) (by norm_num) horizontalNorthZero horizontalWest
    · refine ⟨⟨1 / 2, 1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · exact selectedSlopeValue_pos_of_direction_combination selected
          verticalMember (source := ⟨0, 1⟩) (target := ⟨1 / 2, 1 / 2⟩)
          (zeroDirection := ⟨1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (1 / 2) (by norm_num)
          (by norm_num) (by norm_num) verticalEastZero verticalNorthPositive
      · exact selectedSlopeValue_pos_of_direction_combination selected
          horizontalMember (source := ⟨1, 0⟩)
          (target := ⟨1 / 2, 1 / 2⟩) (zeroDirection := ⟨0, 1⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (1 / 2) (by norm_num)
          (by norm_num) (by norm_num) horizontalNorthZero
          horizontalEastPositive

/-- Every nondegenerate active face has one strictly positive classified
axis direction in the executable table. -/
theorem exists_classified_axis_direction_single
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedSlopeValue selected form direction := by
  rcases selectedActive_axis_values_not_both_zero selected formMember
      discriminantNonzero with eastNonzero | northNonzero
  · rcases lt_or_gt_of_ne eastNonzero with eastNegative | eastPositive
    · refine ⟨⟨-1, 0⟩, by simp [coordinateDirections], ?_⟩
      exact selectedSlopeValue_opposite_pos_of_neg selected formMember
        (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
        (by simp [coordinateDirections]) (by simp [coordinateDirections])
        (by simp) eastNegative
    · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], eastPositive⟩
  · rcases lt_or_gt_of_ne northNonzero with northNegative | northPositive
    · refine ⟨⟨0, -1⟩, by simp [coordinateDirections], ?_⟩
      exact selectedSlopeValue_opposite_pos_of_neg selected formMember
        (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
        (by simp [coordinateDirections]) (by simp [coordinateDirections])
        (by simp) northNegative
    · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], northPositive⟩

/-- The parser-state specialization discharges nondegeneracy from the finite
incremental formula shape. -/
theorem exists_classified_axis_direction_single_of_stateDeterminant
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (stateDeterminant : determinant state.matrix ≠ 0)
    {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedSlopeValue selected form direction := by
  exact exists_classified_axis_direction_single selected formMember
    (selectedIncrementalActiveOwner_boundaryDiscriminant_ne selected
      stateDeterminant formMember)

/-- Cleared gradient dot product, written in ordinary polynomial form so its
two coordinate products can be separated without expensive normalization. -/
def selectedGradientDotPolynomial
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (left right : HermitianForm) :
    RatPolynomial :=
  clearedDirectionalSlope left (selectedPath selected) ⟨1, 0⟩ *
      clearedDirectionalSlope right (selectedPath selected) ⟨1, 0⟩ +
    clearedDirectionalSlope left (selectedPath selected) ⟨0, 1⟩ *
      clearedDirectionalSlope right (selectedPath selected) ⟨0, 1⟩

/-- A compatible pair of active faces has event-divisible cleared gradient
dot product.  The final slope classifier follows a divisor of the original
selected event factor, so divisibility survives every subsequent sign split. -/
theorem selectedGradientDotPolynomial_dvd_of_pairingConstant_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (constantZero : gradientPairingConstant left right = 0) :
    (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (selectedGradientDotPolynomial selected left right).toPolynomial := by
  apply dvd_trans (selectedSlopeClassification selected).divides
  have originalDivides := dvd_clearedGradient_pairing_of_constant_zero
    left right (selectedPath selected)
    selected.candidate.inputCell.branch.factor.polynomial.toPolynomial
    constantZero (selectedActivePolynomial_dvd selected leftMember)
    (selectedActivePolynomial_dvd selected rightMember)
  simpa only [selectedGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    toPolynomial_clearedDirectionalSlope_east,
    toPolynomial_clearedDirectionalSlope_north] using originalDivides

theorem selectedGradientY_product_dvd_of_leftEast_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (dotDivides :
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedGradientDotPolynomial selected left right).toPolynomial)
    (leftEastZero : selectedSlopeValue selected left ⟨1, 0⟩ = 0) :
    (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedDirectionalSlope left (selectedPath selected) ⟨0, 1⟩).toPolynomial *
        (clearedDirectionalSlope right (selectedPath selected) ⟨0, 1⟩).toPolynomial := by
  have leftEastDivides :=
    (selectedSlopeValue_eq_zero_iff_dvd selected leftMember
      (direction := ⟨1, 0⟩) (by simp [coordinateDirections])).1 leftEastZero
  have xProductDivides := dvd_mul_of_dvd_left leftEastDivides
    (clearedDirectionalSlope right (selectedPath selected) ⟨1, 0⟩).toPolynomial
  have difference := dvd_sub dotDivides xProductDivides
  simpa only [selectedGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    add_sub_cancel_left] using difference

theorem selectedGradientY_product_dvd_of_rightEast_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (rightMember : right ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (dotDivides :
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedGradientDotPolynomial selected left right).toPolynomial)
    (rightEastZero : selectedSlopeValue selected right ⟨1, 0⟩ = 0) :
    (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedDirectionalSlope left (selectedPath selected) ⟨0, 1⟩).toPolynomial *
        (clearedDirectionalSlope right (selectedPath selected) ⟨0, 1⟩).toPolynomial := by
  have rightEastDivides :=
    (selectedSlopeValue_eq_zero_iff_dvd selected rightMember
      (direction := ⟨1, 0⟩) (by simp [coordinateDirections])).1 rightEastZero
  have xProductDivides := dvd_mul_of_dvd_right rightEastDivides
    (clearedDirectionalSlope left (selectedPath selected) ⟨1, 0⟩).toPolynomial
  have difference := dvd_sub dotDivides xProductDivides
  simpa only [selectedGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    add_sub_cancel_left] using difference

theorem selectedGradientX_product_dvd_of_leftNorth_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (dotDivides :
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedGradientDotPolynomial selected left right).toPolynomial)
    (leftNorthZero : selectedSlopeValue selected left ⟨0, 1⟩ = 0) :
    (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedDirectionalSlope left (selectedPath selected) ⟨1, 0⟩).toPolynomial *
        (clearedDirectionalSlope right (selectedPath selected) ⟨1, 0⟩).toPolynomial := by
  have leftNorthDivides :=
    (selectedSlopeValue_eq_zero_iff_dvd selected leftMember
      (direction := ⟨0, 1⟩) (by simp [coordinateDirections])).1 leftNorthZero
  have yProductDivides := dvd_mul_of_dvd_left leftNorthDivides
    (clearedDirectionalSlope right (selectedPath selected) ⟨0, 1⟩).toPolynomial
  have difference := dvd_sub dotDivides yProductDivides
  simpa only [selectedGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    add_sub_cancel_right] using difference

theorem selectedGradientX_product_dvd_of_rightNorth_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (rightMember : right ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (dotDivides :
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedGradientDotPolynomial selected left right).toPolynomial)
    (rightNorthZero : selectedSlopeValue selected right ⟨0, 1⟩ = 0) :
    (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedDirectionalSlope left (selectedPath selected) ⟨1, 0⟩).toPolynomial *
        (clearedDirectionalSlope right (selectedPath selected) ⟨1, 0⟩).toPolynomial := by
  have rightNorthDivides :=
    (selectedSlopeValue_eq_zero_iff_dvd selected rightMember
      (direction := ⟨0, 1⟩) (by simp [coordinateDirections])).1 rightNorthZero
  have yProductDivides := dvd_mul_of_dvd_right rightNorthDivides
    (clearedDirectionalSlope left (selectedPath selected) ⟨0, 1⟩).toPolynomial
  have difference := dvd_sub dotDivides yProductDivides
  simpa only [selectedGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    add_sub_cancel_right] using difference

/-- With all four axis components nonzero, one axis is common-positive.  If
both coordinate products were negative, their event-divisible sum would have
the forbidden uniform separation proved in `CCLBranchEventOwner`. -/
theorem exists_classified_axis_direction_pair_of_nonzero_axes
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (leftEastNonzero : selectedSlopeValue selected left ⟨1, 0⟩ ≠ 0)
    (rightEastNonzero : selectedSlopeValue selected right ⟨1, 0⟩ ≠ 0)
    (leftNorthNonzero : selectedSlopeValue selected left ⟨0, 1⟩ ≠ 0)
    (rightNorthNonzero : selectedSlopeValue selected right ⟨0, 1⟩ ≠ 0)
    (dotDivides :
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedGradientDotPolynomial selected left right).toPolynomial) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedSlopeValue selected left direction ∧
        0 < selectedSlopeValue selected right direction := by
  by_cases eastProductPositive : 0 <
      selectedSlopeValue selected left ⟨1, 0⟩ *
        selectedSlopeValue selected right ⟨1, 0⟩
  · rcases mul_pos_iff.mp eastProductPositive with
      ⟨leftPositive, rightPositive⟩ | ⟨leftNegative, rightNegative⟩
    · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], leftPositive,
        rightPositive⟩
    · have leftWestPositive := selectedSlopeValue_opposite_pos_of_neg selected
        leftMember (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
        (by simp [coordinateDirections]) (by simp [coordinateDirections])
        (by simp) leftNegative
      have rightWestPositive := selectedSlopeValue_opposite_pos_of_neg selected
        rightMember (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
        (by simp [coordinateDirections]) (by simp [coordinateDirections])
        (by simp) rightNegative
      exact ⟨⟨-1, 0⟩, by simp [coordinateDirections], leftWestPositive,
        rightWestPositive⟩
  · have eastProductNegative :
        selectedSlopeValue selected left ⟨1, 0⟩ *
            selectedSlopeValue selected right ⟨1, 0⟩ < 0 :=
      lt_of_le_of_ne (le_of_not_gt eastProductPositive)
        (mul_ne_zero leftEastNonzero rightEastNonzero)
    by_cases northProductPositive : 0 <
        selectedSlopeValue selected left ⟨0, 1⟩ *
          selectedSlopeValue selected right ⟨0, 1⟩
    · rcases mul_pos_iff.mp northProductPositive with
        ⟨leftPositive, rightPositive⟩ | ⟨leftNegative, rightNegative⟩
      · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], leftPositive,
          rightPositive⟩
      · have leftSouthPositive := selectedSlopeValue_opposite_pos_of_neg
          selected leftMember (direction := ⟨0, 1⟩)
          (opposite := ⟨0, -1⟩) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (by simp) leftNegative
        have rightSouthPositive := selectedSlopeValue_opposite_pos_of_neg
          selected rightMember (direction := ⟨0, 1⟩)
          (opposite := ⟨0, -1⟩) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (by simp) rightNegative
        exact ⟨⟨0, -1⟩, by simp [coordinateDirections], leftSouthPositive,
          rightSouthPositive⟩
    · have northProductNegative :
          selectedSlopeValue selected left ⟨0, 1⟩ *
              selectedSlopeValue selected right ⟨0, 1⟩ < 0 :=
        lt_of_le_of_ne (le_of_not_gt northProductPositive)
          (mul_ne_zero leftNorthNonzero rightNorthNonzero)
      let classification := selectedSlopeClassification selected
      let signs := selectedSlopeSigns selected
      exact (FTA.CCLBranchEventOwner.ConditionRelations.not_both_canonical_products_neg_of_dvd_sum
        classification.branch.relations classification.parent signs
        (clearedDirectionalSlope_mem_selectedSlopeConditions selected
          (direction := ⟨1, 0⟩) (by simp [coordinateDirections]) leftMember)
        (clearedDirectionalSlope_mem_selectedSlopeConditions selected
          (direction := ⟨1, 0⟩) (by simp [coordinateDirections]) rightMember)
        (clearedDirectionalSlope_mem_selectedSlopeConditions selected
          (direction := ⟨0, 1⟩) (by simp [coordinateDirections]) leftMember)
        (clearedDirectionalSlope_mem_selectedSlopeConditions selected
          (direction := ⟨0, 1⟩) (by simp [coordinateDirections]) rightMember)
        (by simpa only [selectedGradientDotPolynomial,
          DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
          classification] using dotDivides)
        (by simpa [selectedSlopeValue, classification, signs] using
          eastProductNegative)
        (by simpa [selectedSlopeValue, classification, signs] using
          northProductNegative)).elim

/-- Two nondegenerate active faces whose cleared gradient dot product
vanishes on the selected event factor admit one common entry of the exact
eight-direction table. -/
theorem exists_classified_direction_pair_of_gradientDot_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (leftNondegenerate : boundaryDiscriminant left ≠ 0)
    (rightNondegenerate : boundaryDiscriminant right ≠ 0)
    (dotDivides :
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedGradientDotPolynomial selected left right).toPolynomial) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedSlopeValue selected left direction ∧
        0 < selectedSlopeValue selected right direction := by
  have leftAxes := selectedActive_axis_values_not_both_zero selected
    leftMember leftNondegenerate
  have rightAxes := selectedActive_axis_values_not_both_zero selected
    rightMember rightNondegenerate
  by_cases leftEastZero : selectedSlopeValue selected left ⟨1, 0⟩ = 0
  · have leftNorthNonzero : selectedSlopeValue selected left ⟨0, 1⟩ ≠ 0 := by
      rcases leftAxes with leftEastNonzero | leftNorthNonzero
      · exact (leftEastNonzero leftEastZero).elim
      · exact leftNorthNonzero
    have yProductDivides := selectedGradientY_product_dvd_of_leftEast_zero
      selected leftMember dotDivides leftEastZero
    have rightNorthZero := selectedSlopeValue_eq_zero_of_mul_dvd selected
      leftMember (rightForm := right) (leftDirection := ⟨0, 1⟩)
      (rightDirection := ⟨0, 1⟩) (by simp [coordinateDirections])
      leftNorthNonzero yProductDivides
    have rightEastNonzero : selectedSlopeValue selected right ⟨1, 0⟩ ≠ 0 := by
      rcases rightAxes with rightEastNonzero | rightNorthNonzero
      · exact rightEastNonzero
      · exact (rightNorthNonzero rightNorthZero).elim
    exact exists_classified_diagonal_direction_of_axis_zeros selected
      leftMember rightMember leftEastZero rightNorthZero leftNorthNonzero
      rightEastNonzero
  · by_cases rightEastZero : selectedSlopeValue selected right ⟨1, 0⟩ = 0
    · have rightNorthNonzero : selectedSlopeValue selected right ⟨0, 1⟩ ≠ 0 := by
        rcases rightAxes with rightEastNonzero | rightNorthNonzero
        · exact (rightEastNonzero rightEastZero).elim
        · exact rightNorthNonzero
      have yProductDivides := selectedGradientY_product_dvd_of_rightEast_zero
        selected rightMember dotDivides rightEastZero
      have leftNorthZero := selectedSlopeValue_eq_zero_of_mul_dvd_right selected
        rightMember (leftForm := left) (leftDirection := ⟨0, 1⟩)
        (rightDirection := ⟨0, 1⟩) (by simp [coordinateDirections])
        rightNorthNonzero yProductDivides
      rcases exists_classified_diagonal_direction_of_axis_zeros selected
          rightMember leftMember rightEastZero leftNorthZero rightNorthNonzero
          leftEastZero with ⟨direction, directionMember, rightPositive,
            leftPositive⟩
      exact ⟨direction, directionMember, leftPositive, rightPositive⟩
    · have leftNorthNonzero : selectedSlopeValue selected left ⟨0, 1⟩ ≠ 0 := by
        intro leftNorthZero
        have xProductDivides := selectedGradientX_product_dvd_of_leftNorth_zero
          selected leftMember dotDivides leftNorthZero
        exact rightEastZero (selectedSlopeValue_eq_zero_of_mul_dvd selected
          leftMember (rightForm := right) (leftDirection := ⟨1, 0⟩)
          (rightDirection := ⟨1, 0⟩) (by simp [coordinateDirections])
          leftEastZero xProductDivides)
      have rightNorthNonzero : selectedSlopeValue selected right ⟨0, 1⟩ ≠ 0 := by
        intro rightNorthZero
        have xProductDivides := selectedGradientX_product_dvd_of_rightNorth_zero
          selected rightMember dotDivides rightNorthZero
        exact rightEastZero (selectedSlopeValue_eq_zero_of_mul_dvd selected
          leftMember (rightForm := right) (leftDirection := ⟨1, 0⟩)
          (rightDirection := ⟨1, 0⟩) (by simp [coordinateDirections])
          leftEastZero xProductDivides)
      exact exists_classified_axis_direction_pair_of_nonzero_axes selected
        leftMember rightMember leftEastZero rightEastZero leftNorthNonzero
        rightNorthNonzero dotDivides

def classifiedSlopesPositive?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (direction : QI) : Bool :=
  (eventPayloadIncrementalActiveOwnerForms selected).all fun form =>
    decide (0 < selectedSlopeValue selected form direction)

theorem classifiedSlopesPositive?_eq_true_iff
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (direction : QI) :
    classifiedSlopesPositive? selected direction = true ↔
      ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
        0 < selectedSlopeValue selected form direction := by
  simp [classifiedSlopesPositive?]

/-- Exact finite tangent table on the classified algebraic slope signs. -/
def classifiedTangentDirection?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : Option QI :=
  coordinateDirections.find? fun direction =>
    classifiedSlopesPositive? selected direction

/-- Any common-positive entry of the finite direction table is found by the
executable classified search. -/
theorem classifiedTangentDirection?_isSome_of_exists
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (existsDirection :
      ∃ direction ∈ coordinateDirections,
        ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
          0 < selectedSlopeValue selected form direction) :
    (classifiedTangentDirection? selected).isSome := by
  rw [classifiedTangentDirection?, List.find?_isSome]
  rcases existsDirection with ⟨direction, directionMember, slopes⟩
  exact ⟨direction, directionMember,
    (classifiedSlopesPositive?_eq_true_iff selected direction).2 slopes⟩

/-- The classified search succeeds vacuously when the selected transition has
no active owner face. -/
theorem classifiedTangentDirection?_isSome_of_nil
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (forms : eventPayloadIncrementalActiveOwnerForms selected = []) :
    (classifiedTangentDirection? selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_exists selected
  refine ⟨⟨1, 0⟩, by simp [coordinateDirections], ?_⟩
  simp [forms]

/-- Nondegeneracy closes the executable search for a singleton selected owner
face. -/
theorem classifiedTangentDirection?_isSome_of_singleton
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (stateDeterminant :
      determinant state.matrix ≠ 0) {form : HermitianForm}
    (forms : eventPayloadIncrementalActiveOwnerForms selected = [form]) :
    (classifiedTangentDirection? selected).isSome := by
  have formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  rcases exists_classified_axis_direction_single_of_stateDeterminant selected
      stateDeterminant formMember with
    ⟨direction, directionMember, slope⟩
  apply classifiedTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using slope

/-- Any selected transition with at most one active owner face is therefore
closed by the executable classified search. -/
theorem classifiedTangentDirection?_isSome_of_length_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (stateDeterminant :
      determinant state.matrix ≠ 0)
    (lengthLe : (eventPayloadIncrementalActiveOwnerForms selected).length ≤ 1) :
    (classifiedTangentDirection? selected).isSome := by
  cases forms : eventPayloadIncrementalActiveOwnerForms selected with
  | nil => exact classifiedTangentDirection?_isSome_of_nil selected forms
  | cons form tail =>
      cases tail with
      | nil =>
          exact classifiedTangentDirection?_isSome_of_singleton selected
            stateDeterminant forms
      | cons next rest => simp [forms] at lengthLe

/-- Formula-facing version used by all non-branching raw-parser phases. -/
theorem classifiedTangentDirection?_isSome_of_formulaAtoms_length_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (stateDeterminant :
      determinant state.matrix ≠ 0)
    (formulaLength :
      (formulaAtoms
        (inputIncrementalAdvanceFormula state selected.bit)).length ≤ 1) :
    (classifiedTangentDirection? selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_length_le_one selected
    stateDeterminant
  exact (activeOwnerForms_length_le_formulaAtoms
    (inputIncrementalAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected)).trans formulaLength

/-- The initial raw bit introduces exactly one atom, regardless of which
unary branch it selects. -/
theorem classifiedTangentDirection?_isSome_initial
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {matrix : Mat2 QI}
    {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.initial, matrix, history⟩) selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_formulaAtoms_length_le_one
    selected stateDeterminant
  cases selected.bit <;>
    simp [inputIncrementalAdvanceFormula, Formula.pullback,
      incrementalAdvanceFormula, RawParser.step, activeFormula, formulaAtoms]

/-- Continuing any unary run introduces one atom and is therefore a
singleton-or-empty owner transition. -/
theorem classifiedTangentDirection?_isSome_highUnary_true
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {count : ℕ} {matrix : Mat2 QI}
    {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output) (selectedTrue : selected.bit = true)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.highUnary count, matrix, history⟩) selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_formulaAtoms_length_le_one
    selected stateDeterminant
  simp [selectedTrue, inputIncrementalAdvanceFormula, Formula.pullback,
    incrementalAdvanceFormula, RawParser.step, activeFormula, formulaAtoms]

theorem classifiedTangentDirection?_isSome_lowUnary_true
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {count : ℕ} {matrix : Mat2 QI}
    {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output) (selectedTrue : selected.bit = true)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.lowUnary count, matrix, history⟩) selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_formulaAtoms_length_le_one
    selected stateDeterminant
  cases count <;>
    simp [selectedTrue, inputIncrementalAdvanceFormula, Formula.pullback,
      incrementalAdvanceFormula, RawParser.step, activeFormula, formulaAtoms]

theorem classifiedTangentDirection?_isSome_loopUnary_true
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {count : ℕ} {matrix : Mat2 QI}
    {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : IncrementalEventPayload output) (selectedTrue : selected.bit = true)
    (stateDeterminant : determinant matrix ≠ 0) :
    (classifiedTangentDirection? (state :=
      ⟨.loopUnary count, matrix, history⟩) selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_formulaAtoms_length_le_one
    selected stateDeterminant
  simp [selectedTrue, inputIncrementalAdvanceFormula, Formula.pullback,
    incrementalAdvanceFormula, RawParser.step, activeFormula, formulaAtoms]

/-- A compatible nondegenerate pair closes the executable search as soon as
its cleared gradient dot product vanishes on the selected event factor. -/
theorem classifiedTangentDirection?_isSome_of_pair
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (stateDeterminant :
      determinant state.matrix ≠ 0) {left right : HermitianForm}
    (forms : eventPayloadIncrementalActiveOwnerForms selected = [left, right])
    (dotDivides :
      (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedGradientDotPolynomial selected left right).toPolynomial) :
    (classifiedTangentDirection? selected).isSome := by
  have leftMember : left ∈
      eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  have rightMember : right ∈
      eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  rcases exists_classified_direction_pair_of_gradientDot_dvd selected
      leftMember rightMember
      (selectedIncrementalActiveOwner_boundaryDiscriminant_ne selected
        stateDeterminant leftMember)
      (selectedIncrementalActiveOwner_boundaryDiscriminant_ne selected
        stateDeterminant rightMember)
      dotDivides with ⟨direction, directionMember, leftSlope, rightSlope⟩
  apply classifiedTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using And.intro leftSlope rightSlope

/-- Pair-search specialization stated with the parser-shape invariant used by
real/imaginary sector corners. -/
theorem classifiedTangentDirection?_isSome_of_pairingConstant_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (stateDeterminant :
      determinant state.matrix ≠ 0) {left right : HermitianForm}
    (forms : eventPayloadIncrementalActiveOwnerForms selected = [left, right])
    (constantZero : gradientPairingConstant left right = 0) :
    (classifiedTangentDirection? selected).isSome := by
  apply classifiedTangentDirection?_isSome_of_pair selected stateDeterminant
    forms
  exact selectedGradientDotPolynomial_dvd_of_pairingConstant_zero selected
    (by simp [forms]) (by simp [forms]) constantZero

theorem classifiedTangentDirection?_some_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : QI}
    (search : classifiedTangentDirection? selected = some direction) :
    direction ∈ coordinateDirections :=
  List.mem_of_find?_eq_some search

theorem classifiedTangentDirection?_some_slopes
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : QI}
    (search : classifiedTangentDirection? selected = some direction) :
    ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
      0 < selectedSlopeValue selected form direction := by
  apply (classifiedSlopesPositive?_eq_true_iff selected direction).mp
  exact List.find?_some search

/-- The final slope-sign interval is nested in the original selected parser
event interval. -/
theorem selectedSlopeSigns_refines_inputCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    (selectedSlopeSigns selected).refined.interval.Refines
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval := by
  exact (selectedSlopeClassification selected).signRefines

/-- Repackage the slope-classified divisor as an ordinary parser input event
cell.  All original parser-condition relations transfer along divisibility,
while the parent interval is now the final slope-sign cell.  Consequently the
existing event extraction can be reused without selecting a point outside the
proved tangent interval. -/
def selectedSlopeInputCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    InputEventCell state selected.candidate.sourceEvent.event :=
  { branch :=
      { factor := (selectedSlopeClassification selected).branch.factor
        relations := selected.candidate.inputCell.branch.relations.ofDvd
          (selectedSlopeClassification selected).branch.factor.input
          (selectedSlopeClassification selected).divides }
    divides := (selectedSlopeClassification selected).divides.trans
      selected.candidate.inputCell.divides
    parent := (selectedSlopeSigns selected).refined
    refines := RationalInterval.refines_trans
      (selectedSlopeSigns_refines_inputCell selected)
      selected.candidate.inputCell.signRefines }

/-- The ordinary cell API performs one final common-sign refinement from the
slope-classified parent. -/
def selectedSlopeInputSigns
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :=
  (selectedSlopeInputCell selected).branch.computeEventSigns
    (selectedSlopeInputCell selected).parent

/-- A successful classified table direction has positive cleared slopes at
every rational point of the final common-sign interval. -/
theorem classifiedTangentDirection?_some_clearedSlopes
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : QI}
    (search : classifiedTangentDirection? selected = some direction)
    {t : ℚ} (lower : (selectedSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤ (selectedSlopeSigns selected).refined.interval.upper) :
    ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
      0 < (clearedDirectionalSlope form (selectedPath selected) direction).eval t := by
  intro form formMember
  let classification := selectedSlopeClassification selected
  let signs := selectedSlopeSigns selected
  let polynomial :=
    clearedDirectionalSlope form (selectedPath selected) direction
  have directionMember := classifiedTangentDirection?_some_mem search
  have polynomialMember : polynomial ∈ selectedSlopeConditions selected := by
    exact clearedDirectionalSlope_mem_selectedSlopeConditions selected
      directionMember formMember
  have canonicalPositive :=
    classifiedTangentDirection?_some_slopes search form formMember
  have productPositive :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
      classification.branch.relations classification.parent signs
      polynomialMember canonicalPositive.ne' lower upper
  change 0 < polynomial.eval t
  change 0 < selectedSlopeValue selected form direction at canonicalPositive
  change 0 < selectedSlopeValue selected form direction * polynomial.eval t at productPositive
  nlinarith

/-- One computed positive margin simultaneously lower-bounds every coprime
slope condition on the final classified interval. -/
def selectedSlopeStrictMargin
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
    (selectedSlopeClassification selected).branch.relations
    (selectedSlopeClassification selected).parent
    (selectedSlopeSigns selected)

theorem selectedSlopeStrictMargin_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedSlopeStrictMargin selected :=
  FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_pos
    (selectedSlopeClassification selected).branch.relations
    (selectedSlopeClassification selected).parent
    (selectedSlopeSigns selected)

theorem selectedSlopeStrictMargin_le_clearedSlope
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : QI}
    (search : classifiedTangentDirection? selected = some direction)
    {t : ℚ} (lower : (selectedSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤ (selectedSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    selectedSlopeStrictMargin selected ≤
      (clearedDirectionalSlope form (selectedPath selected) direction).eval t := by
  let polynomial :=
    clearedDirectionalSlope form (selectedPath selected) direction
  have polynomialMember : polynomial ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      (classifiedTangentDirection?_some_mem search) formMember
  have canonicalPositive :=
    classifiedTangentDirection?_some_slopes search form formMember
  have marginLeAbs :=
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
    (selectedSlopeClassification selected).branch.relations
    (selectedSlopeClassification selected).parent
    (selectedSlopeSigns selected) polynomialMember canonicalPositive.ne'
    lower upper
  have positive := classifiedTangentDirection?_some_clearedSlopes search
    lower upper form formMember
  simpa only [polynomial, selectedSlopeStrictMargin,
    abs_of_pos positive] using marginLeAbs

/-- A positive whole-cell upper bound for the projective denominator norm on
the classified slope interval. -/
def selectedSlopeDenominatorUpper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  denseEvalAbsBound (denominatorNorm (selectedPath selected))
      (intervalMagnitude
        (selectedSlopeSigns selected).refined.interval.lower
        (selectedSlopeSigns selected).refined.interval.upper) + 1

theorem selectedSlopeDenominatorUpper_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedSlopeDenominatorUpper selected := by
  unfold selectedSlopeDenominatorUpper
  have nonnegative := (denseHornerBounds_nonneg
    (denominatorNorm (selectedPath selected))
    (intervalMagnitude_pos
      (selectedSlopeSigns selected).refined.interval.lower
      (selectedSlopeSigns selected).refined.interval.upper).le).1
  linarith

theorem denominatorNorm_le_selectedSlopeDenominatorUpper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {t : ℚ}
    (lower : (selectedSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤ (selectedSlopeSigns selected).refined.interval.upper) :
    (denominatorNorm (selectedPath selected)).eval t ≤
      selectedSlopeDenominatorUpper selected := by
  let magnitude := intervalMagnitude
    (selectedSlopeSigns selected).refined.interval.lower
    (selectedSlopeSigns selected).refined.interval.upper
  have magnitudeNonnegative : 0 ≤ magnitude :=
    (intervalMagnitude_pos _ _).le
  have tMagnitude : |t| ≤ magnitude :=
    abs_le_intervalMagnitude lower upper
  have absoluteBound := abs_dense_eval_le_denseEvalAbsBound
    (denominatorNorm (selectedPath selected)) magnitudeNonnegative tMagnitude
  exact (le_abs_self _).trans absoluteBound |>.trans (by
    unfold selectedSlopeDenominatorUpper
    dsimp only [magnitude]
    linarith)

/-- Uniform positive lower bound for every selected directional derivative
using the fixed classified vector, valid at every rational point of the final
slope cell. -/
def selectedSlopeDirectionalLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  selectedSlopeStrictMargin selected / selectedSlopeDenominatorUpper selected

theorem selectedSlopeDirectionalLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedSlopeDirectionalLower selected :=
  div_pos (selectedSlopeStrictMargin_pos selected)
    (selectedSlopeDenominatorUpper_pos selected)

theorem selectedSlopeDirectionalLower_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : QI}
    (search : classifiedTangentDirection? selected = some direction)
    {t : ℚ} (lower : (selectedSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤ (selectedSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (formMember : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    selectedSlopeDirectionalLower selected ≤
      directionalSlope form ((selectedPath selected).value t) direction := by
  have rootLower := (selectedSlopeSigns_refines_inputCell selected).1.trans lower
  have rootUpper := upper.trans (selectedSlopeSigns_refines_inputCell selected).2
  have pathDenominator :=
    selected.candidate.inputCell.path_denominator_ne_on_cell rootLower rootUpper
  have denominatorPositive := eval_denominatorNorm_pos
    (selectedPath selected) t pathDenominator
  have denominatorLe := denominatorNorm_le_selectedSlopeDenominatorUpper
    selected lower upper
  have marginLe := selectedSlopeStrictMargin_le_clearedSlope search lower upper
    formMember
  have scaled : selectedSlopeDirectionalLower selected *
      (denominatorNorm (selectedPath selected)).eval t ≤
      selectedSlopeStrictMargin selected := by
    unfold selectedSlopeDirectionalLower
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (selectedSlopeDenominatorUpper_pos selected)).2
    exact mul_le_mul_of_nonneg_left denominatorLe
      (selectedSlopeStrictMargin_pos selected).le
  rw [eval_clearedDirectionalSlope form (selectedPath selected) direction t
    pathDenominator] at marginLe
  apply (mul_le_mul_iff_of_pos_right denominatorPositive).mp
  calc
    selectedSlopeDirectionalLower selected *
        (denominatorNorm (selectedPath selected)).eval t ≤
      selectedSlopeStrictMargin selected := scaled
    _ ≤ (denominatorNorm (selectedPath selected)).eval t *
        directionalSlope form ((selectedPath selected).value t) direction :=
      marginLe
    _ = directionalSlope form ((selectedPath selected).value t) direction *
        (denominatorNorm (selectedPath selected)).eval t := by ring

/-- Hence the ordinary planar tangent search succeeds at every rational path
point in the final classified interval. -/
theorem tangentDirectionCertificate?_isSome_of_classified_search
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : QI}
    (search : classifiedTangentDirection? selected = some direction)
    {t : ℚ} (lower : (selectedSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤ (selectedSlopeSigns selected).refined.interval.upper) :
    (tangentDirectionCertificate?
      (eventPayloadIncrementalActiveOwnerForms selected)
      ((selectedPath selected).value t)).isSome := by
  have rootLower :
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval.lower ≤ t :=
    (selectedSlopeSigns_refines_inputCell selected).1.trans lower
  have rootUpper : t ≤
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval.upper :=
    upper.trans (selectedSlopeSigns_refines_inputCell selected).2
  have denominator := selected.candidate.inputCell.path_denominator_ne_on_cell
    rootLower rootUpper
  apply tangentDirectionCertificate?_isSome_of_mem
    (classifiedTangentDirection?_some_mem search)
  intro form formMember
  apply (eval_clearedDirectionalSlope_pos_iff form (selectedPath selected)
    direction t denominator).1
  exact classifiedTangentDirection?_some_clearedSlopes search lower upper form
    formMember

/-! ## A rational approximation inside the classified slope cell -/

/-- Narrow the final classified event factor itself.  Unlike the earlier
source approximation, every returned parameter remains in the interval on
which all selected tangent slopes have fixed signs. -/
def selectedSlopeApproximation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :=
  FTA.RootCountDivisibility.narrowEventApproximation
    (selectedSlopeClassification selected).branch.factor.input
    (selectedSlopeSigns selected).refined epsilon epsilonPositive

def selectedSlopeApproximationParameter
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) : ℚ :=
  (selectedSlopeApproximation selected epsilon
    epsilonPositive).refined.interval.lower

def selectedSlopeApproximationPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) : QI :=
  (selectedPath selected).value
    (selectedSlopeApproximationParameter selected epsilon epsilonPositive)

theorem selectedSlopeApproximationParameter_lower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    (selectedSlopeSigns selected).refined.interval.lower ≤
      selectedSlopeApproximationParameter selected epsilon epsilonPositive := by
  exact (selectedSlopeApproximation selected epsilon epsilonPositive).refines.1

theorem selectedSlopeApproximationParameter_upper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    selectedSlopeApproximationParameter selected epsilon epsilonPositive ≤
      (selectedSlopeSigns selected).refined.interval.upper := by
  exact (selectedSlopeApproximation selected epsilon
    epsilonPositive).refined.proper.le.trans
      (selectedSlopeApproximation selected epsilon epsilonPositive).refines.2

/-- The classified approximation stays in the original selected parser cell,
so the projective path denominator remains constructively nonzero. -/
theorem selectedSlopeApproximation_denominator_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    (selectedPath selected).denominator.eval (PathPolynomial.ofRat
      (selectedSlopeApproximationParameter selected epsilon
        epsilonPositive)) ≠ 0 := by
  apply selected.candidate.inputCell.path_denominator_ne_on_cell
  · exact (selectedSlopeSigns_refines_inputCell selected).1.trans
      (selectedSlopeApproximationParameter_lower selected epsilon
        epsilonPositive)
  · exact (selectedSlopeApproximationParameter_upper selected epsilon
      epsilonPositive).trans (selectedSlopeSigns_refines_inputCell selected).2

/-- Every selected active boundary remains a multiple of the final classified
factor after the slope-condition splits. -/
theorem selectedSlopeActivePolynomial_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    (selectedSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedForm form (selectedPath selected)).toPolynomial :=
  dvd_trans (selectedSlopeClassification selected).divides
    (selectedActivePolynomial_dvd selected member)

/-- Every active face of the complete selected child formula remains a
multiple of the final slope-classified event factor. -/
theorem selectedSlopeCompleteActivePolynomial_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    (selectedSlopeClassification
        selected.toIncrementalPayload).branch.factor.polynomial.toPolynomial ∣
      (clearedForm form
        (selectedPath selected.toIncrementalPayload)).toPolynomial :=
  dvd_trans (selectedSlopeClassification selected.toIncrementalPayload).divides
    (selectedCompleteActivePolynomial_dvd selected member)

/-- Strict selected atoms retain their canonical signs at the classified
rational approximation. -/
theorem selectedStrictAtSlopeApproximation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form *
        form.eval (selectedSlopeApproximationPoint selected epsilon
          epsilonPositive) := by
  intro form member
  let path := selectedPath selected
  let signs := selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent
  let t := selectedSlopeApproximationParameter selected epsilon
    epsilonPositive
  have lower : signs.refined.interval.lower ≤ t :=
    (selectedSlopeSigns_refines_inputCell selected).1.trans
      (selectedSlopeApproximationParameter_lower selected epsilon
        epsilonPositive)
  have upper : t ≤ signs.refined.interval.upper :=
    (selectedSlopeApproximationParameter_upper selected epsilon
      epsilonPositive).trans (selectedSlopeSigns_refines_inputCell selected).2
  have polynomialSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent signs
      (selectedStrictPolynomial_mem selected member)
      (by
        simpa only [eventPayloadCanonicalValue] using
          strictPriorForms_value_ne
            (inputIncrementalAdvanceFormula state selected.bit)
            (eventPayloadCanonicalValue selected) member)
      lower upper
  have denominator := selectedSlopeApproximation_denominator_ne selected
    epsilon epsilonPositive
  have denominatorPositive := eval_denominatorNorm_pos path t denominator
  change 0 < eventPayloadCanonicalValue selected form *
    (clearedForm form path).eval t at polynomialSign
  rw [eval_clearedForm form path t denominator] at polynomialSign
  have rearranged : 0 < (denominatorNorm path).eval t *
      (eventPayloadCanonicalValue selected form *
        form.eval (selectedSlopeApproximationPoint selected epsilon
          epsilonPositive)) := by
    simpa only [path, signs, t, eventPayloadCanonicalValue,
      selectedSlopeApproximationPoint, mul_assoc, mul_left_comm, mul_comm]
      using polynomialSign
  rcases mul_pos_iff.mp rearranged with positive | negative
  · exact positive.2
  · exact (not_lt_of_ge denominatorPositive.le negative.1).elim

/-- Active selected boundaries are explicitly small at the classified
approximation, now with the final event factor as the computed divisor. -/
theorem selectedActiveAtSlopeApproximation_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    |form.eval (selectedSlopeApproximationPoint selected epsilon
        epsilonPositive)| ≤
      approximationBound (clearedForm form (selectedPath selected))
          (selectedSlopeClassification selected).branch.factor.polynomial
          (selectedSlopeSigns selected).refined epsilon /
        (RelevantCurveEvent.ownerDenominatorCertificate
          selected.candidate.sourceEvent.event).bound := by
  let path := selectedPath selected
  let approximation := selectedSlopeApproximation selected epsilon
    epsilonPositive
  let t := selectedSlopeApproximationParameter selected epsilon
    epsilonPositive
  let denominator := RelevantCurveEvent.ownerDenominatorCertificate
    selected.candidate.sourceEvent.event
  have small := approximation.multipleSmall
    (selectedSlopeActivePolynomial_dvd selected member) epsilonPositive.le
  have pathDenominator := selectedSlopeApproximation_denominator_ne selected
    epsilon epsilonPositive
  have denominatorLower : denominator.bound ≤
      (denominatorNorm path).eval t := by
    apply denominator.lower
    · exact selected.candidate.inputCell.signRefines.1.trans
        ((selectedSlopeSigns_refines_inputCell selected).1.trans
          (selectedSlopeApproximationParameter_lower selected epsilon
            epsilonPositive))
    · exact ((selectedSlopeApproximationParameter_upper selected epsilon
        epsilonPositive).trans
          (selectedSlopeSigns_refines_inputCell selected).2).trans
            selected.candidate.inputCell.signRefines.2
  apply (le_div_iff₀ denominator.positive).2
  calc
    |form.eval (selectedSlopeApproximationPoint selected epsilon
          epsilonPositive)| * denominator.bound =
        denominator.bound *
          |form.eval (selectedSlopeApproximationPoint selected epsilon
            epsilonPositive)| := by ring
    _ ≤ (denominatorNorm path).eval t *
          |form.eval (selectedSlopeApproximationPoint selected epsilon
            epsilonPositive)| :=
      mul_le_mul_of_nonneg_right denominatorLower (abs_nonneg _)
    _ = |(clearedForm form path).eval t| := by
      rw [eval_clearedForm form path t pathDenominator, abs_mul,
        abs_of_pos (eval_denominatorNorm_pos path t pathDenominator)]
      rfl
    _ ≤ approximationBound (clearedForm form path)
          (selectedSlopeClassification selected).branch.factor.polynomial
          (selectedSlopeSigns selected).refined epsilon := by
      simpa only [approximation, path, t, selectedSlopeApproximation,
        selectedSlopeApproximationParameter] using small

/-- The final ordinary narrowing of the slope-classified input cell also
preserves every strict incremental atom.  This is the form used by direct
localization, whose approximation width is chosen from the later owner box. -/
theorem selectedStrictAtSlopeInputCellApproximation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form *
        form.eval ((selectedPath selected).value
          ((selectedSlopeInputCell selected).clearedApproximation epsilon
            epsilonPositive).refined.interval.lower) := by
  intro form member
  let path := selectedPath selected
  let originalSigns := selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent
  let cell := selectedSlopeInputCell selected
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let t := approximation.refined.interval.lower
  have slopeLower : (selectedSlopeSigns selected).refined.interval.lower ≤ t :=
    (selectedSlopeInputSigns selected).refines.1.trans approximation.refines.1
  have slopeUpper : t ≤
      (selectedSlopeSigns selected).refined.interval.upper :=
    (approximation.refined.proper.le.trans approximation.refines.2).trans
      (selectedSlopeInputSigns selected).refines.2
  have lower : originalSigns.refined.interval.lower ≤ t :=
    (selectedSlopeSigns_refines_inputCell selected).1.trans slopeLower
  have upper : t ≤ originalSigns.refined.interval.upper :=
    slopeUpper.trans (selectedSlopeSigns_refines_inputCell selected).2
  have polynomialSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent originalSigns
      (selectedStrictPolynomial_mem selected member)
      (by
        simpa only [eventPayloadCanonicalValue] using
          strictPriorForms_value_ne
            (inputIncrementalAdvanceFormula state selected.bit)
            (eventPayloadCanonicalValue selected) member)
      lower upper
  have pathDenominator := cell.path_denominator_ne_on_cell
    approximation.refines.1
    (approximation.refined.proper.le.trans approximation.refines.2)
  have denominatorPositive := eval_denominatorNorm_pos path t pathDenominator
  change 0 < eventPayloadCanonicalValue selected form *
    (clearedForm form path).eval t at polynomialSign
  rw [eval_clearedForm form path t pathDenominator] at polynomialSign
  have rearranged : 0 < (denominatorNorm path).eval t *
      (eventPayloadCanonicalValue selected form *
        form.eval ((selectedPath selected).value t)) := by
    simpa only [path, originalSigns, cell, approximation, t,
      eventPayloadCanonicalValue, mul_assoc, mul_left_comm, mul_comm]
      using polynomialSign
  rcases mul_pos_iff.mp rearranged with positive | negative
  · exact positive.2
  · exact (not_lt_of_ge denominatorPositive.le negative.1).elim

/-- The same final ordinary narrowing preserves every strict atom of the
complete selected child formula, including its retained parser history. -/
theorem selectedCompleteStrictAtSlopeInputCellApproximation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    ∀ form ∈ eventPayloadStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected.toIncrementalPayload form *
        form.eval ((selectedPath selected.toIncrementalPayload).value
          ((selectedSlopeInputCell
              selected.toIncrementalPayload).clearedApproximation epsilon
            epsilonPositive).refined.interval.lower) := by
  intro form member
  let direct := selected.toIncrementalPayload
  let path := selectedPath direct
  let originalSigns := selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent
  let cell := selectedSlopeInputCell direct
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let t := approximation.refined.interval.lower
  have slopeLower : (selectedSlopeSigns direct).refined.interval.lower ≤ t :=
    (selectedSlopeInputSigns direct).refines.1.trans approximation.refines.1
  have slopeUpper : t ≤
      (selectedSlopeSigns direct).refined.interval.upper :=
    (approximation.refined.proper.le.trans approximation.refines.2).trans
      (selectedSlopeInputSigns direct).refines.2
  have lower : originalSigns.refined.interval.lower ≤ t :=
    (selectedSlopeSigns_refines_inputCell direct).1.trans slopeLower
  have upper : t ≤ originalSigns.refined.interval.upper :=
    slopeUpper.trans (selectedSlopeSigns_refines_inputCell direct).2
  have canonicalNonzero := strictPriorForms_value_ne
    (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue direct) member
  change canonicalEventValue
    selected.candidate.inputCell.branch.factor.input
    (clearedForm form selected.candidate.sourceEvent.partition.entry.chart.path)
    originalSigns.refined.interval.lower ≠ 0 at canonicalNonzero
  have polynomialSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent originalSigns
      (selectedCompleteStrictPolynomial_mem selected member)
      (by simpa only [eventPayloadCanonicalValue] using canonicalNonzero)
      lower upper
  have pathDenominator := cell.path_denominator_ne_on_cell
    approximation.refines.1
    (approximation.refined.proper.le.trans approximation.refines.2)
  have denominatorPositive := eval_denominatorNorm_pos path t pathDenominator
  change 0 < eventPayloadCanonicalValue direct form *
    (clearedForm form path).eval t at polynomialSign
  rw [eval_clearedForm form path t pathDenominator] at polynomialSign
  have rearranged : 0 < (denominatorNorm path).eval t *
      (eventPayloadCanonicalValue direct form *
        form.eval ((selectedPath direct).value t)) := by
    dsimp only [path, cell, approximation, t] at polynomialSign ⊢
    convert polynomialSign using 1
    all_goals ring
  rcases mul_pos_iff.mp rearranged with positive | negative
  · exact positive.2
  · exact (not_lt_of_ge denominatorPositive.le negative.1).elim

/-- The ordinary `InputEventCell` narrowing API for the final slope divisor
has the same active-form residual estimate.  This version is consumed by the
localized sampler, whose width also enforces the Newton and box budgets. -/
theorem selectedActiveAtSlopeInputCellApproximation_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    |form.eval ((selectedPath selected).value
      ((selectedSlopeInputCell selected).clearedApproximation epsilon
        epsilonPositive).refined.interval.lower)| ≤
      approximationBound (clearedForm form (selectedPath selected))
          (selectedSlopeClassification selected).branch.factor.polynomial
          (selectedSlopeInputSigns selected).refined epsilon /
        (RelevantCurveEvent.ownerDenominatorCertificate
          selected.candidate.sourceEvent.event).bound := by
  let cell := selectedSlopeInputCell selected
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let t := approximation.refined.interval.lower
  let denominator := RelevantCurveEvent.ownerDenominatorCertificate
    selected.candidate.sourceEvent.event
  have small := approximation.multipleSmall
    (selectedSlopeActivePolynomial_dvd selected member) epsilonPositive.le
  have pathDenominator := cell.path_denominator_ne_on_cell
    approximation.refines.1
    (approximation.refined.proper.le.trans approximation.refines.2)
  have denominatorLower : denominator.bound ≤
      (denominatorNorm (selectedPath selected)).eval t := by
    apply denominator.lower
    · exact cell.signRefines.1.trans approximation.refines.1
    · exact (approximation.refined.proper.le.trans
        approximation.refines.2).trans cell.signRefines.2
  apply (le_div_iff₀ denominator.positive).2
  calc
    |form.eval ((selectedPath selected).value t)| * denominator.bound =
        denominator.bound * |form.eval ((selectedPath selected).value t)| := by
      ring
    _ ≤ (denominatorNorm (selectedPath selected)).eval t *
          |form.eval ((selectedPath selected).value t)| :=
      mul_le_mul_of_nonneg_right denominatorLower (abs_nonneg _)
    _ = |(clearedForm form (selectedPath selected)).eval t| := by
      rw [eval_clearedForm form (selectedPath selected) t pathDenominator,
        abs_mul, abs_of_pos (eval_denominatorNorm_pos
          (selectedPath selected) t pathDenominator)]
    _ ≤ approximationBound (clearedForm form (selectedPath selected))
          (selectedSlopeClassification selected).branch.factor.polynomial
          (selectedSlopeInputSigns selected).refined epsilon := by
      exact small

/-- Complete-child active faces satisfy the same residual estimate at the
ordinary narrowing of the final slope cell. -/
theorem selectedCompleteActiveAtSlopeInputCellApproximation_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    |form.eval ((selectedPath selected.toIncrementalPayload).value
      ((selectedSlopeInputCell
          selected.toIncrementalPayload).clearedApproximation epsilon
        epsilonPositive).refined.interval.lower)| ≤
      approximationBound
          (clearedForm form (selectedPath selected.toIncrementalPayload))
          (selectedSlopeClassification
            selected.toIncrementalPayload).branch.factor.polynomial
          (selectedSlopeInputSigns selected.toIncrementalPayload).refined
            epsilon /
        (RelevantCurveEvent.ownerDenominatorCertificate
          selected.candidate.sourceEvent.event).bound := by
  let direct := selected.toIncrementalPayload
  let cell := selectedSlopeInputCell direct
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let t := approximation.refined.interval.lower
  let denominator := RelevantCurveEvent.ownerDenominatorCertificate
    selected.candidate.sourceEvent.event
  have small := approximation.multipleSmall
    (selectedSlopeCompleteActivePolynomial_dvd selected member)
    epsilonPositive.le
  have pathDenominator := cell.path_denominator_ne_on_cell
    approximation.refines.1
    (approximation.refined.proper.le.trans approximation.refines.2)
  have denominatorLower : denominator.bound ≤
      (denominatorNorm (selectedPath direct)).eval t := by
    apply denominator.lower
    · exact cell.signRefines.1.trans approximation.refines.1
    · exact (approximation.refined.proper.le.trans
        approximation.refines.2).trans cell.signRefines.2
  apply (le_div_iff₀ denominator.positive).2
  calc
    |form.eval ((selectedPath direct).value t)| * denominator.bound =
        denominator.bound * |form.eval ((selectedPath direct).value t)| := by
      ring
    _ ≤ (denominatorNorm (selectedPath direct)).eval t *
          |form.eval ((selectedPath direct).value t)| :=
      mul_le_mul_of_nonneg_right denominatorLower (abs_nonneg _)
    _ = |(clearedForm form (selectedPath direct)).eval t| := by
      rw [eval_clearedForm form (selectedPath direct) t pathDenominator,
        abs_mul, abs_of_pos (eval_denominatorNorm_pos
          (selectedPath direct) t pathDenominator)]
    _ ≤ approximationBound (clearedForm form (selectedPath direct))
          (selectedSlopeClassification direct).branch.factor.polynomial
          (selectedSlopeInputSigns direct).refined epsilon := by
      exact small

/-- A successful algebraic table search therefore produces a successful
ordinary tangent search at an explicitly narrowed rational curve point. -/
theorem tangentDirectionCertificate?_isSome_at_selectedSlopeApproximation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : QI}
    (search : classifiedTangentDirection? selected = some direction)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    (tangentDirectionCertificate?
      (eventPayloadIncrementalActiveOwnerForms selected)
      (selectedSlopeApproximationPoint selected epsilon
        epsilonPositive)).isSome := by
  apply tangentDirectionCertificate?_isSome_of_classified_search search
  · exact selectedSlopeApproximationParameter_lower selected epsilon
      epsilonPositive
  · exact selectedSlopeApproximationParameter_upper selected epsilon
      epsilonPositive

end CCLEventTangentSigns
end FTA
