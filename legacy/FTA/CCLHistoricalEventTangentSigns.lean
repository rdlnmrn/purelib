import FTA.CCLHistoricalEventOwner
import FTA.CCLCompleteEventTangentSigns

/-!
# Tangent signs for a selected event with complete parser history

This module runs the finite eight-direction slope classifier on every active
face of the conjunction formed by the current parser predicate and the
selected child.  It starts from the history-classified count-one descendant,
so both newly selected and previously retained equality faces use one common
algebraic event factor and one common rational sign interval.
-/

namespace FTA
namespace CCLHistoricalEventTangentSigns

open CCL CCL.GaussianRat
open FTA.CCLBranchEvent
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLCanonicalEvent
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLCountOneClassification
open FTA.CCLEventTangentSigns
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLHistoricalEventOwner
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLPathIntersection
open FTA.CCLParserGeometry
open FTA.CCLPathTangent
open FTA.CCLPositiveEventSemantics
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.ProjectivePath
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI
abbrev RatPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial ℚ

private theorem clearedOrientedWeakForm_dvd
    (factor : Polynomial ℚ) (path : ProjectivePath.Path) (atom : Atom)
    (divides : factor ∣ (clearedForm atom.form path).toPolynomial) :
    factor ∣ (clearedForm (orientedWeakForm atom) path).toPolynomial := by
  rcases atom with ⟨form, sign⟩
  cases sign with
  | nonpositive =>
      have negIdentity :
          (clearedForm form.neg path).toPolynomial =
            -(clearedForm form path).toPolynomial := by
        simp only [clearedForm, HermitianForm.neg, toPolynomial_add,
          toPolynomial_scale]
        simp
        abel
      change factor ∣ (clearedForm form.neg path).toPolynomial
      rw [negIdentity]
      exact dvd_neg.mpr divides
  | negative | zero | nonzero | nonnegative | positive =>
      simpa [orientedWeakForm] using divides

/-- A current-state face active in the common oracle is already an exact
multiple of the history-classified event factor. -/
theorem historicalCurrentActivePolynomial_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ activeOwnerForms (inputStateFormula state)
      (historicalCanonicalValue selected)) :
    (historicalInputCell selected).branch.factor.polynomial.toPolynomial ∣
      (clearedForm form (selectedCompletePath selected)).toPolynomial := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  let classification :=
    currentFormulaClassification selected.candidate.inputCell
  let currentSigns := classification.branch.computeEventSigns
    classification.parent
  let cell := historicalInputCell selected
  let finalSigns := cell.branch.computeEventSigns cell.parent
  let t := finalSigns.refined.interval.lower
  have polynomialMember : clearedForm atom.form (selectedCompletePath selected) ∈
      eventFormulaPolynomials (inputStateFormula state)
        (selectedCompletePath selected) :=
    List.mem_map.mpr
      ⟨atom, satisfyingAtoms_mem_formulaAtoms _ _
        (activeSatisfyingAtoms_source atomMember), rfl⟩
  have lower : currentSigns.refined.interval.lower ≤ t := by
    exact finalSigns.refines.1
  have upper : t ≤ currentSigns.refined.interval.upper := by
    exact finalSigns.refined.proper.le.trans finalSigns.refines.2
  have canonicalZero := activeSatisfyingAtoms_zero atomMember
  have canonicalZero' : canonicalEventValue classification.branch.factor.input
      (clearedForm atom.form (selectedCompletePath selected)) t = 0 := by
    simpa only [historicalCanonicalValue, inputEventCanonicalValue,
      selectedPath, historicalInputCell,
      currentFormulaInputCell, classification, currentSigns, cell, finalSigns,
      t] using canonicalZero
  have divides :=
    ConditionRelations.dvd_of_canonicalEventValue_eq_zero_between
      classification.branch.relations classification.parent currentSigns
      polynomialMember lower upper canonicalZero'
  exact clearedOrientedWeakForm_dvd _ _ atom (by
    simpa only [historicalInputCell, currentFormulaInputCell,
      classification] using divides)

/-- The selected-child part of the common active list is likewise a multiple
of the history-classified event factor. -/
theorem historicalChildActivePolynomial_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ activeOwnerForms
      (inputAdvanceFormula state selected.bit)
      (historicalCanonicalValue selected)) :
    (historicalInputCell selected).branch.factor.polynomial.toPolynomial ∣
      (clearedForm form (selectedCompletePath selected)).toPolynomial := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  let cell := historicalInputCell selected
  let signs := cell.branch.computeEventSigns cell.parent
  have polynomialMember : clearedForm atom.form (selectedCompletePath selected) ∈
      inputEventPolynomials state (selectedCompletePath selected) :=
    clearedForm_mem_inputEventPolynomials_of_advance_atom state
      (selectedCompletePath selected) selected.bit atom
      (satisfyingAtoms_mem_formulaAtoms _ _
        (activeSatisfyingAtoms_source atomMember))
  have canonicalZero := activeSatisfyingAtoms_zero atomMember
  have divides :=
    ConditionRelations.dvd_of_canonicalEventValue_eq_zero
      cell.branch.relations cell.parent signs polynomialMember (by
        simpa only [historicalCanonicalValue, inputEventCanonicalValue,
          selectedPath, cell, signs] using canonicalZero)
  exact clearedOrientedWeakForm_dvd _ _ atom (by
    simpa only [cell] using divides)

/-- Cleared directional slopes for every active historical/child face and
every member of the fixed compass table. -/
def historicalSlopeConditions
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : List RatPolynomial :=
  coordinateDirections.flatMap fun direction =>
    (historicalActiveOwnerForms selected).map fun form =>
      clearedDirectionalSlope form (selectedCompletePath selected) direction

theorem clearedDirectionalSlope_mem_historicalSlopeConditions
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {direction : QI}
    (directionMember : direction ∈ coordinateDirections)
    {form : HermitianForm}
    (formMember : form ∈ historicalActiveOwnerForms selected) :
    clearedDirectionalSlope form (selectedCompletePath selected) direction ∈
      historicalSlopeConditions selected := by
  rw [historicalSlopeConditions, List.mem_flatMap]
  exact ⟨direction, directionMember,
    List.mem_map.mpr ⟨form, formMember, rfl⟩⟩

/-- Unique count-one descendant after all historical tangent slopes have been
classified simultaneously. -/
def historicalSlopeClassification
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :=
  followCountOneConditions (historicalInputCell selected).branch.factor
    ((historicalInputCell selected).branch.computeEventSigns
      (historicalInputCell selected).parent).refined
    (historicalSlopeConditions selected)

def historicalSlopeSigns
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :=
  (historicalSlopeClassification selected).branch.computeEventSigns
    (historicalSlopeClassification selected).parent

theorem historicalSlopeSigns_refines_inputCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    (historicalSlopeSigns selected).refined.interval.Refines
      ((historicalInputCell selected).branch.computeEventSigns
        (historicalInputCell selected).parent).refined.interval :=
  (historicalSlopeClassification selected).signRefines

/-- The selected source event's denominator bound remains valid on the final
historical slope interval. -/
def historicalDenominatorPositiveLowerBound
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    FTA.PositiveLowerBound.Certificate
      (denominatorNorm (selectedCompletePath selected))
      (historicalSlopeSigns selected).refined.interval := by
  let denominator := RelevantCurveEvent.ownerDenominatorCertificate
    selected.candidate.sourceEvent.event
  exact
    { bound := denominator.bound ^ 2
      positive := sq_pos_of_pos denominator.positive
      lower := by
        intro t lower upper
        have rootLower := (historicalInputCell selected).signRefines.1.trans
          ((historicalSlopeSigns_refines_inputCell selected).1.trans lower)
        have rootUpper :=
          (upper.trans
              (historicalSlopeSigns_refines_inputCell selected).2).trans
            (historicalInputCell selected).signRefines.2
        have denominatorLower : denominator.bound ≤
            (denominatorNorm (selectedCompletePath selected)).eval t :=
          denominator.lower rootLower rootUpper
        simpa only [pow_two] using
          mul_self_le_mul_self denominator.positive.le denominatorLower }

/-- Four denominator factors rescale a positive invariant angle gap into the
positive polynomial obstruction used by the compass table. -/
def historicalAngleGapPositiveLowerBound
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (left right : HermitianForm)
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    FTA.PositiveLowerBound.Certificate
      (DensePolynomial.scale
        (boundaryDiscriminant left * boundaryDiscriminant right -
          2 * gradientPairingConstant left right ^ 2)
        ((denominatorNorm (selectedCompletePath selected) *
            denominatorNorm (selectedCompletePath selected)) *
          (denominatorNorm (selectedCompletePath selected) *
            denominatorNorm (selectedCompletePath selected))))
      (historicalSlopeSigns selected).refined.interval := by
  let denominatorCertificate :=
    historicalDenominatorPositiveLowerBound selected
  let denominatorSquared := FTA.PositiveLowerBound.Certificate.mul
    denominatorCertificate denominatorCertificate
  let denominatorFourth := FTA.PositiveLowerBound.Certificate.mul
    denominatorSquared denominatorSquared
  exact FTA.PositiveLowerBound.Certificate.ofScalarProduct
    (boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2)
    angleGapPositive.ne' denominatorFourth (by
      intro t
      simp only [DensePolynomial.eval_scale, DensePolynomial.eval_mul])

/-- Every face in the simultaneous active list remains a multiple after the
final slope classification. -/
theorem historicalSlopeActivePolynomial_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    (historicalSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedForm form (selectedCompletePath selected)).toPolynomial := by
  apply (historicalSlopeClassification selected).divides.trans
  rw [historicalActiveOwnerForms_eq_append] at member
  rcases List.mem_append.mp member with currentMember | childMember
  · exact historicalCurrentActivePolynomial_dvd selected currentMember
  · exact historicalChildActivePolynomial_dvd selected childMember

/-- Canonical value of one classified historical slope. -/
def historicalSlopeValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (form : HermitianForm) (direction : QI) : ℚ :=
  canonicalEventValue
    (historicalSlopeClassification selected).branch.factor.input
    (clearedDirectionalSlope form (selectedCompletePath selected) direction)
    (historicalSlopeSigns selected).refined.interval.lower

/-- A nondegenerate active historical boundary cannot have both cleared
gradient coordinates vanish on the final slope factor. -/
theorem historicalActive_clearedGradient_not_both_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ historicalActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    ¬((historicalSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedGradientX form (selectedCompletePath selected)).toPolynomial ∧
      (historicalSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedGradientY form (selectedCompletePath selected)).toPolynomial) := by
  intro bothDivides
  let classification := historicalSlopeClassification selected
  let path := selectedCompletePath selected
  let factor := classification.branch.factor.polynomial.toPolynomial
  let denominator := (denominatorNorm path).toPolynomial
  have factorDividesSelected :
      factor ∣ (historicalInputCell selected).branch.factor.polynomial.toPolynomial :=
    classification.divides
  have factorDividesEvent :
      factor ∣ selected.candidate.sourceEvent.event.branch.factor.polynomial.toPolynomial :=
    factorDividesSelected.trans (historicalInputCell selected).divides
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
      factor ∣ (clearedForm form path).toPolynomial := by
    simpa [factor, path, classification] using
      historicalSlopeActivePolynomial_dvd selected formMember
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

/-- A nondegenerate historical active face has negative discriminant.  A
positive discriminant would make the cleared gradient identity uniformly
positive on the count-one cell while the common event factor divides it. -/
theorem historicalActive_boundaryDiscriminant_neg
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ historicalActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    boundaryDiscriminant form < 0 := by
  apply lt_of_le_of_ne (le_of_not_gt (fun discriminantPositive => ?_))
    discriminantNonzero
  let classification := historicalSlopeClassification selected
  let signs := historicalSlopeSigns selected
  let path := selectedCompletePath selected
  let factor := classification.branch.factor.polynomial.toPolynomial
  let denominator := denominatorNorm path
  let gradientSquare :=
    clearedGradientX form path * clearedGradientX form path +
      clearedGradientY form path * clearedGradientY form path
  let discriminantTerm := DensePolynomial.scale (boundaryDiscriminant form)
    (denominator * denominator)
  let obstruction := gradientSquare + discriminantTerm
  have factorDividesForm :
      factor ∣ (clearedForm form path).toPolynomial := by
    simpa [factor, path, classification] using
      historicalSlopeActivePolynomial_dvd selected formMember
  have factorDividesLeft : factor ∣
      (DensePolynomial.scale (4 * form.radial)
        (clearedForm form path * denominator)).toPolynomial := by
    simp only [DensePolynomial.toPolynomial_scale,
      DensePolynomial.toPolynomial_mul]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left factorDividesForm denominator.toPolynomial) _
  rw [clearedGradient_discriminant_identity] at factorDividesLeft
  have obstructionDivides : factor ∣ obstruction.toPolynomial := by
    simpa only [obstruction, gradientSquare, discriminantTerm, denominator,
      DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
      DensePolynomial.toPolynomial_scale] using factorDividesLeft
  let denominatorCertificate :=
    historicalDenominatorPositiveLowerBound selected
  let lowerBound := boundaryDiscriminant form * denominatorCertificate.bound
  have lowerBoundPositive : 0 < lowerBound :=
    mul_pos discriminantPositive denominatorCertificate.positive
  have obstructionPositive : ∀ t : ℚ,
      signs.refined.interval.lower ≤ t →
      t ≤ signs.refined.interval.upper → 0 < obstruction.eval t := by
    intro t lower upper
    have denominatorLower := denominatorCertificate.lower t lower upper
    have gradientXSquare := sq_nonneg ((clearedGradientX form path).eval t)
    have gradientYSquare := sq_nonneg ((clearedGradientY form path).eval t)
    simp only [obstruction, gradientSquare, discriminantTerm,
      DensePolynomial.eval_add, DensePolynomial.eval_mul,
      DensePolynomial.eval_scale, denominator]
    nlinarith
  have obstructionLower : FTA.PositiveLowerBound.Certificate obstruction
      signs.refined.interval :=
    { bound := lowerBound ^ 2
      positive := sq_pos_of_pos lowerBoundPositive
      lower := by
        intro t lower upper
        have denominatorLower := denominatorCertificate.lower t lower upper
        have gradientXSquare :=
          sq_nonneg ((clearedGradientX form path).eval t)
        have gradientYSquare :=
          sq_nonneg ((clearedGradientY form path).eval t)
        have valueLower : lowerBound ≤ obstruction.eval t := by
          simp only [obstruction, gradientSquare, discriminantTerm,
            DensePolynomial.eval_add, DensePolynomial.eval_mul,
            DensePolynomial.eval_scale, denominator, lowerBound]
          nlinarith
        have valueNonnegative : 0 ≤ obstruction.eval t :=
          (obstructionPositive t lower upper).le
        simpa only [pow_two] using
          mul_self_le_mul_self lowerBoundPositive.le valueLower }
  exact FTA.RootCountDivisibility.CountOneInterval.no_positiveLowerBound_of_dvd
    classification.branch.factor.input signs.refined obstructionDivides
    obstructionLower

/-- Canonical zero is exactly divisibility by the final slope factor for a
classified historical slope. -/
theorem historicalSlopeValue_eq_zero_iff_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ historicalActiveOwnerForms selected)
    {direction : QI} (directionMember : direction ∈ coordinateDirections) :
    historicalSlopeValue selected form direction = 0 ↔
      (historicalSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedDirectionalSlope form (selectedCompletePath selected)
          direction).toPolynomial := by
  let classification := historicalSlopeClassification selected
  let signs := historicalSlopeSigns selected
  have polynomialMember :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      directionMember formMember
  constructor
  · intro zero
    exact ConditionRelations.dvd_of_canonicalEventValue_eq_zero
      classification.branch.relations classification.parent signs
      polynomialMember (by
        simpa [historicalSlopeValue, classification, signs] using zero)
  · intro divides
    exact canonicalEventValue_eq_zero_of_dvd
      classification.branch.factor.input _ _ divides

/-- A nondegenerate historical active face has a nonzero classified
horizontal or vertical slope. -/
theorem historicalActive_axis_values_not_both_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ historicalActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    historicalSlopeValue selected form ⟨1, 0⟩ ≠ 0 ∨
      historicalSlopeValue selected form ⟨0, 1⟩ ≠ 0 := by
  by_contra neither
  push Not at neither
  apply historicalActive_clearedGradient_not_both_dvd selected formMember
    discriminantNonzero
  constructor
  · simpa using (historicalSlopeValue_eq_zero_iff_dvd selected formMember
      (direction := ⟨1, 0⟩) (by simp [coordinateDirections])).1 neither.1
  · simpa using (historicalSlopeValue_eq_zero_iff_dvd selected formMember
      (direction := ⟨0, 1⟩) (by simp [coordinateDirections])).1 neither.2

/-- Opposite compass directions have opposite classified signs. -/
theorem historicalSlopeValue_opposite_pos_of_neg
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ historicalActiveOwnerForms selected)
    {direction opposite : QI}
    (directionMember : direction ∈ coordinateDirections)
    (oppositeMember : opposite ∈ coordinateDirections)
    (polynomialOpposite :
      (clearedDirectionalSlope form (selectedCompletePath selected)
          opposite).toPolynomial =
        -(clearedDirectionalSlope form (selectedCompletePath selected)
          direction).toPolynomial)
    (negative : historicalSlopeValue selected form direction < 0) :
    0 < historicalSlopeValue selected form opposite := by
  let classification := historicalSlopeClassification selected
  let signs := historicalSlopeSigns selected
  have directionPolynomialMember :
      clearedDirectionalSlope form (selectedCompletePath selected) direction ∈
        historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      directionMember formMember
  have oppositePolynomialMember :
      clearedDirectionalSlope form (selectedCompletePath selected) opposite ∈
        historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      oppositeMember formMember
  have positive :=
    ConditionRelations.canonicalEventValue_pos_of_polynomial_neg
      classification.branch.relations classification.parent signs
      directionPolynomialMember oppositePolynomialMember polynomialOpposite
      (by simpa [historicalSlopeValue, classification, signs] using negative)
  simpa [historicalSlopeValue, classification, signs] using positive

/-- Every nondegenerate historical active face has a strictly positive axis
direction in the executable table. -/
theorem exists_historical_axis_direction_single
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ historicalActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    ∃ direction ∈ coordinateDirections,
      0 < historicalSlopeValue selected form direction := by
  rcases historicalActive_axis_values_not_both_zero selected formMember
      discriminantNonzero with eastNonzero | northNonzero
  · rcases lt_or_gt_of_ne eastNonzero with eastNegative | eastPositive
    · refine ⟨⟨-1, 0⟩, by simp [coordinateDirections], ?_⟩
      exact historicalSlopeValue_opposite_pos_of_neg selected formMember
        (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
        (by simp [coordinateDirections]) (by simp [coordinateDirections])
        (by simp) eastNegative
    · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], eastPositive⟩
  · rcases lt_or_gt_of_ne northNonzero with northNegative | northPositive
    · refine ⟨⟨0, -1⟩, by simp [coordinateDirections], ?_⟩
      exact historicalSlopeValue_opposite_pos_of_neg selected formMember
        (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
        (by simp [coordinateDirections]) (by simp [coordinateDirections])
        (by simp) northNegative
    · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], northPositive⟩

def historicalClassifiedSlopesPositive?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (direction : QI) : Bool :=
  (historicalActiveOwnerForms selected).all fun form =>
    decide (0 < historicalSlopeValue selected form direction)

theorem historicalClassifiedSlopesPositive?_eq_true_iff
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (direction : QI) :
    historicalClassifiedSlopesPositive? selected direction = true ↔
      ∀ form ∈ historicalActiveOwnerForms selected,
        0 < historicalSlopeValue selected form direction := by
  simp [historicalClassifiedSlopesPositive?]

/-- Executable common-cone search over the fixed eight rational directions. -/
def historicalClassifiedTangentDirection?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : Option QI :=
  coordinateDirections.find? fun direction =>
    historicalClassifiedSlopesPositive? selected direction

theorem historicalClassifiedTangentDirection?_isSome_of_exists
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (existsDirection :
      ∃ direction ∈ coordinateDirections,
        ∀ form ∈ historicalActiveOwnerForms selected,
          0 < historicalSlopeValue selected form direction) :
    (historicalClassifiedTangentDirection? selected).isSome := by
  rw [historicalClassifiedTangentDirection?, List.find?_isSome]
  rcases existsDirection with ⟨direction, directionMember, slopes⟩
  exact ⟨direction, directionMember,
    (historicalClassifiedSlopesPositive?_eq_true_iff
      selected direction).2 slopes⟩

/-- A positive invariant angle gap rules out simultaneous failure of all four
antipodal compass pairs for two historical active faces. -/
theorem not_four_historical_direction_products_nonpositive_of_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ historicalActiveOwnerForms selected)
    (rightMember : right ∈ historicalActiveOwnerForms selected)
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2)
    (eastNonpositive :
      historicalSlopeValue selected left ⟨1, 0⟩ *
        historicalSlopeValue selected right ⟨1, 0⟩ ≤ 0)
    (northNonpositive :
      historicalSlopeValue selected left ⟨0, 1⟩ *
        historicalSlopeValue selected right ⟨0, 1⟩ ≤ 0)
    (northEastNonpositive :
      historicalSlopeValue selected left ⟨1 / 2, 1 / 2⟩ *
        historicalSlopeValue selected right ⟨1 / 2, 1 / 2⟩ ≤ 0)
    (southEastNonpositive :
      historicalSlopeValue selected left ⟨1 / 2, -1 / 2⟩ *
        historicalSlopeValue selected right ⟨1 / 2, -1 / 2⟩ ≤ 0) :
    False := by
  let classification := historicalSlopeClassification selected
  let signs := historicalSlopeSigns selected
  let path := selectedCompletePath selected
  let gap := boundaryDiscriminant left * boundaryDiscriminant right -
    2 * gradientPairingConstant left right ^ 2
  let base := DensePolynomial.scale gap
    ((denominatorNorm path * denominatorNorm path) *
      (denominatorNorm path * denominatorNorm path))
  let leftEast := clearedDirectionalSlope left path ⟨1, 0⟩
  let rightEast := clearedDirectionalSlope right path ⟨1, 0⟩
  let leftNorth := clearedDirectionalSlope left path ⟨0, 1⟩
  let rightNorth := clearedDirectionalSlope right path ⟨0, 1⟩
  let leftNorthEast := clearedDirectionalSlope left path ⟨1 / 2, 1 / 2⟩
  let rightNorthEast := clearedDirectionalSlope right path ⟨1 / 2, 1 / 2⟩
  let leftSouthEast := clearedDirectionalSlope left path ⟨1 / 2, -1 / 2⟩
  let rightSouthEast := clearedDirectionalSlope right path ⟨1 / 2, -1 / 2⟩
  have leftEastMember : leftEast ∈ historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightEastMember : rightEast ∈ historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have leftNorthMember : leftNorth ∈ historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightNorthMember : rightNorth ∈ historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have leftNorthEastMember : leftNorthEast ∈
      historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightNorthEastMember : rightNorthEast ∈
      historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have leftSouthEastMember : leftSouthEast ∈
      historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightSouthEastMember : rightSouthEast ∈
      historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have basePositive : ∀ t : ℚ,
      signs.refined.interval.lower ≤ t →
      t ≤ signs.refined.interval.upper → 0 < base.eval t := by
    intro t lower upper
    let denominator := RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event
    have rootLower := (historicalInputCell selected).signRefines.1.trans
      ((historicalSlopeSigns_refines_inputCell selected).1.trans lower)
    have rootUpper :=
      (upper.trans
          (historicalSlopeSigns_refines_inputCell selected).2).trans
        (historicalInputCell selected).signRefines.2
    have denominatorLower : denominator.bound ≤
        (denominatorNorm path).eval t := by
      simpa only [path, selectedPath] using
        denominator.lower rootLower rootUpper
    have denominatorPositive : 0 < (denominatorNorm path).eval t :=
      denominator.positive.trans_le denominatorLower
    simp only [base, DensePolynomial.eval_scale, DensePolynomial.eval_mul]
    exact mul_pos angleGapPositive
      (mul_pos (mul_pos denominatorPositive denominatorPositive)
        (mul_pos denominatorPositive denominatorPositive))
  have baseLower : FTA.PositiveLowerBound.Certificate base
      signs.refined.interval := by
    simpa only [base, gap, path, signs] using
      historicalAngleGapPositiveLowerBound selected left right
        angleGapPositive
  have obstructionDivides :
      classification.branch.factor.polynomial.toPolynomial ∣
        (base +
          (DensePolynomial.scale 4
              ((leftEast * rightEast) * (leftNorth * rightNorth)) +
            DensePolynomial.scale 16
              ((leftNorthEast * rightNorthEast) *
                (leftSouthEast * rightSouthEast)))).toPolynomial := by
    have identity := dvd_compass_angleGap_identity left right path
      classification.branch.factor.polynomial.toPolynomial
      (by
        simpa only [classification, path] using
          historicalSlopeActivePolynomial_dvd selected leftMember)
      (by
        simpa only [classification, path] using
          historicalSlopeActivePolynomial_dvd selected rightMember)
    simpa only [base, gap, leftEast, rightEast, leftNorth, rightNorth,
      leftNorthEast, rightNorthEast, leftSouthEast, rightSouthEast] using
        identity
  exact ConditionRelations.not_four_direction_products_nonpositive
    classification.branch.relations classification.parent signs
    leftEastMember rightEastMember leftNorthMember rightNorthMember
    leftNorthEastMember rightNorthEastMember leftSouthEastMember
    rightSouthEastMember 4 16 (by norm_num) (by norm_num) basePositive
    baseLower obstructionDivides
    (by simpa [historicalSlopeValue, classification, signs, path,
      leftEast, rightEast] using eastNonpositive)
    (by simpa [historicalSlopeValue, classification, signs, path,
      leftNorth, rightNorth] using northNonpositive)
    (by simpa [historicalSlopeValue, classification, signs, path,
      leftNorthEast, rightNorthEast] using northEastNonpositive)
    (by simpa [historicalSlopeValue, classification, signs, path,
      leftSouthEast, rightSouthEast] using southEastNonpositive)

/-- A positive invariant angle gap forces one compass direction to enter both
historical owner faces. -/
theorem exists_historical_direction_pair_of_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ historicalActiveOwnerForms selected)
    (rightMember : right ∈ historicalActiveOwnerForms selected)
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    ∃ direction ∈ coordinateDirections,
      0 < historicalSlopeValue selected left direction ∧
        0 < historicalSlopeValue selected right direction := by
  have negNorthEast : (-⟨1 / 2, 1 / 2⟩ : QI) =
      ⟨-1 / 2, -1 / 2⟩ := by
    ext <;> norm_num
  have negSouthEast : (-⟨1 / 2, -1 / 2⟩ : QI) =
      ⟨-1 / 2, 1 / 2⟩ := by
    ext <;> norm_num
  by_cases eastProduct : 0 <
      historicalSlopeValue selected left ⟨1, 0⟩ *
        historicalSlopeValue selected right ⟨1, 0⟩
  · rcases mul_pos_iff.mp eastProduct with positive | negative
    · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], positive⟩
    · have leftWestPositive :=
        historicalSlopeValue_opposite_pos_of_neg selected leftMember
          (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp) negative.1
      have rightWestPositive :=
        historicalSlopeValue_opposite_pos_of_neg selected rightMember
          (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp) negative.2
      exact ⟨⟨-1, 0⟩, by simp [coordinateDirections], leftWestPositive,
        rightWestPositive⟩
  · by_cases northProduct : 0 <
        historicalSlopeValue selected left ⟨0, 1⟩ *
          historicalSlopeValue selected right ⟨0, 1⟩
    · rcases mul_pos_iff.mp northProduct with positive | negative
      · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], positive⟩
      · have leftSouthPositive :=
          historicalSlopeValue_opposite_pos_of_neg selected leftMember
            (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
            (by simp [coordinateDirections]) (by simp [coordinateDirections])
            (by simp) negative.1
        have rightSouthPositive :=
          historicalSlopeValue_opposite_pos_of_neg selected rightMember
            (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
            (by simp [coordinateDirections]) (by simp [coordinateDirections])
            (by simp) negative.2
        exact ⟨⟨0, -1⟩, by simp [coordinateDirections], leftSouthPositive,
          rightSouthPositive⟩
    · by_cases northEastProduct : 0 <
          historicalSlopeValue selected left ⟨1 / 2, 1 / 2⟩ *
            historicalSlopeValue selected right ⟨1 / 2, 1 / 2⟩
      · rcases mul_pos_iff.mp northEastProduct with positive | negative
        · exact ⟨⟨1 / 2, 1 / 2⟩, by simp [coordinateDirections], positive⟩
        · have leftSouthWestPositive :=
            historicalSlopeValue_opposite_pos_of_neg selected leftMember
              (direction := ⟨1 / 2, 1 / 2⟩)
              (opposite := (-⟨1 / 2, 1 / 2⟩ : QI))
              (by simp [coordinateDirections])
              (by rw [negNorthEast]; simp [coordinateDirections])
              (toPolynomial_clearedDirectionalSlope_neg left
                (selectedCompletePath selected) ⟨1 / 2, 1 / 2⟩) negative.1
          have rightSouthWestPositive :=
            historicalSlopeValue_opposite_pos_of_neg selected rightMember
              (direction := ⟨1 / 2, 1 / 2⟩)
              (opposite := (-⟨1 / 2, 1 / 2⟩ : QI))
              (by simp [coordinateDirections])
              (by rw [negNorthEast]; simp [coordinateDirections])
              (toPolynomial_clearedDirectionalSlope_neg right
                (selectedCompletePath selected) ⟨1 / 2, 1 / 2⟩) negative.2
          rw [negNorthEast] at leftSouthWestPositive rightSouthWestPositive
          exact ⟨⟨-1 / 2, -1 / 2⟩, by simp [coordinateDirections],
            leftSouthWestPositive, rightSouthWestPositive⟩
      · by_cases southEastProduct : 0 <
            historicalSlopeValue selected left ⟨1 / 2, -1 / 2⟩ *
              historicalSlopeValue selected right ⟨1 / 2, -1 / 2⟩
        · rcases mul_pos_iff.mp southEastProduct with positive | negative
          · exact ⟨⟨1 / 2, -1 / 2⟩, by simp [coordinateDirections],
              positive⟩
          · have leftNorthWestPositive :=
              historicalSlopeValue_opposite_pos_of_neg selected leftMember
                (direction := ⟨1 / 2, -1 / 2⟩)
                (opposite := (-⟨1 / 2, -1 / 2⟩ : QI))
                (by simp [coordinateDirections])
                (by rw [negSouthEast]; simp [coordinateDirections])
                (toPolynomial_clearedDirectionalSlope_neg left
                  (selectedCompletePath selected) ⟨1 / 2, -1 / 2⟩) negative.1
            have rightNorthWestPositive :=
              historicalSlopeValue_opposite_pos_of_neg selected rightMember
                (direction := ⟨1 / 2, -1 / 2⟩)
                (opposite := (-⟨1 / 2, -1 / 2⟩ : QI))
                (by simp [coordinateDirections])
                (by rw [negSouthEast]; simp [coordinateDirections])
                (toPolynomial_clearedDirectionalSlope_neg right
                  (selectedCompletePath selected) ⟨1 / 2, -1 / 2⟩) negative.2
            rw [negSouthEast] at leftNorthWestPositive rightNorthWestPositive
            exact ⟨⟨-1 / 2, 1 / 2⟩, by simp [coordinateDirections],
              leftNorthWestPositive, rightNorthWestPositive⟩
        · exact
            (not_four_historical_direction_products_nonpositive_of_angleGap
              selected leftMember rightMember angleGapPositive
              (le_of_not_gt eastProduct) (le_of_not_gt northProduct)
              (le_of_not_gt northEastProduct)
              (le_of_not_gt southEastProduct)).elim

/-- A displayed two-face historical cone with positive invariant angle gap
closes the executable tangent search. -/
theorem historicalClassifiedTangentDirection?_isSome_of_pair_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (forms : historicalActiveOwnerForms selected = [left, right])
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    (historicalClassifiedTangentDirection? selected).isSome := by
  have leftMember : left ∈ historicalActiveOwnerForms selected := by
    simp [forms]
  have rightMember : right ∈ historicalActiveOwnerForms selected := by
    simp [forms]
  rcases exists_historical_direction_pair_of_angleGap selected leftMember
      rightMember angleGapPositive with
    ⟨direction, directionMember, leftPositive, rightPositive⟩
  apply historicalClassifiedTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using And.intro leftPositive rightPositive

/-- Exact orthogonality is the principal compatible pair case: negative
discriminants make its invariant angle gap strictly positive. -/
theorem historicalClassifiedTangentDirection?_isSome_of_pairingConstant_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (forms : historicalActiveOwnerForms selected = [left, right])
    (leftNondegenerate : boundaryDiscriminant left ≠ 0)
    (rightNondegenerate : boundaryDiscriminant right ≠ 0)
    (constantZero : gradientPairingConstant left right = 0) :
    (historicalClassifiedTangentDirection? selected).isSome := by
  have leftMember : left ∈ historicalActiveOwnerForms selected := by
    simp [forms]
  have rightMember : right ∈ historicalActiveOwnerForms selected := by
    simp [forms]
  have leftNegative := historicalActive_boundaryDiscriminant_neg selected
    leftMember leftNondegenerate
  have rightNegative := historicalActive_boundaryDiscriminant_neg selected
    rightMember rightNondegenerate
  apply historicalClassifiedTangentDirection?_isSome_of_pair_angleGap
    selected forms
  rw [constantZero]
  norm_num
  exact mul_pos_of_neg_of_neg leftNegative rightNegative

theorem historicalClassifiedTangentDirection?_isSome_of_parsed_pairingConstant_zero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : LocalExtraction.GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisSafeCuts.AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    {left right : HermitianForm}
    (forms : historicalActiveOwnerForms selected = [left, right])
    (constantZero : gradientPairingConstant left right = 0) :
    (historicalClassifiedTangentDirection? selected).isSome := by
  apply historicalClassifiedTangentDirection?_isSome_of_pairingConstant_zero
    selected forms
  · exact historicalActiveOwner_boundaryDiscriminant_ne current separation
      selected squarefree degreeNonzero elimination valid (by simp [forms])
  · exact historicalActiveOwner_boundaryDiscriminant_ne current separation
      selected squarefree degreeNonzero elimination valid (by simp [forms])
  · exact constantZero

theorem historicalClassifiedTangentDirection?_isSome_of_nil
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (forms : historicalActiveOwnerForms selected = []) :
    (historicalClassifiedTangentDirection? selected).isSome := by
  apply historicalClassifiedTangentDirection?_isSome_of_exists selected
  refine ⟨⟨1, 0⟩, by simp [coordinateDirections], ?_⟩
  simp [forms]

theorem historicalClassifiedTangentDirection?_isSome_of_singleton
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (forms : historicalActiveOwnerForms selected = [form])
    (nondegenerate : boundaryDiscriminant form ≠ 0) :
    (historicalClassifiedTangentDirection? selected).isSome := by
  have formMember : form ∈ historicalActiveOwnerForms selected := by
    simp [forms]
  rcases exists_historical_axis_direction_single selected formMember
      nondegenerate with ⟨direction, directionMember, slope⟩
  apply historicalClassifiedTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using slope

/-- Every empty or singleton historical cone is closed by the executable
search once nondegeneracy is known. -/
theorem historicalClassifiedTangentDirection?_isSome_of_length_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (nondegenerate : ∀ form ∈ historicalActiveOwnerForms selected,
      boundaryDiscriminant form ≠ 0)
    (lengthLe : (historicalActiveOwnerForms selected).length ≤ 1) :
    (historicalClassifiedTangentDirection? selected).isSome := by
  cases forms : historicalActiveOwnerForms selected with
  | nil =>
      exact historicalClassifiedTangentDirection?_isSome_of_nil selected forms
  | cons form tail =>
      cases tail with
      | nil =>
          apply historicalClassifiedTangentDirection?_isSome_of_singleton
            selected forms
          exact nondegenerate form (by simp [forms])
      | cons next rest => simp [forms] at lengthLe

theorem historicalClassifiedTangentDirection?_isSome_of_parsed_length_le_one
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : LocalExtraction.GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisSafeCuts.AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    (lengthLe : (historicalActiveOwnerForms selected).length ≤ 1) :
    (historicalClassifiedTangentDirection? selected).isSome := by
  apply historicalClassifiedTangentDirection?_isSome_of_length_le_one selected
  · intro form member
    exact historicalActiveOwner_boundaryDiscriminant_ne current separation
      selected squarefree degreeNonzero elimination valid member
  · exact lengthLe

theorem historicalClassifiedTangentDirection?_some_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some direction) :
    direction ∈ coordinateDirections :=
  List.mem_of_find?_eq_some search

theorem historicalClassifiedTangentDirection?_some_slopes
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some direction) :
    ∀ form ∈ historicalActiveOwnerForms selected,
      0 < historicalSlopeValue selected form direction := by
  apply (historicalClassifiedSlopesPositive?_eq_true_iff
    selected direction).mp
  exact List.find?_some search

/-- A successful canonical table entry has positive cleared slope throughout
the final common-sign interval. -/
theorem historicalClassifiedTangentDirection?_some_clearedSlopes
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    {t : ℚ}
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper) :
    ∀ form ∈ historicalActiveOwnerForms selected,
      0 < (clearedDirectionalSlope form (selectedCompletePath selected)
        direction).eval t := by
  intro form formMember
  let classification := historicalSlopeClassification selected
  let signs := historicalSlopeSigns selected
  let polynomial :=
    clearedDirectionalSlope form (selectedCompletePath selected) direction
  have polynomialMember : polynomial ∈ historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (historicalClassifiedTangentDirection?_some_mem search) formMember
  have canonicalPositive :=
    historicalClassifiedTangentDirection?_some_slopes search form formMember
  have productPositive :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      classification.branch.relations classification.parent signs
      polynomialMember canonicalPositive.ne' lower upper
  change 0 < polynomial.eval t
  change 0 < historicalSlopeValue selected form direction at canonicalPositive
  change 0 < historicalSlopeValue selected form direction *
    polynomial.eval t at productPositive
  nlinarith

/-- A successful historical classifier is a genuine simultaneous tangent
vector at every rational path point retained by its final sign interval. -/
def historicalClassifiedTangentDirectionAt
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (t : ℚ)
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper) :
    TangentDirection (historicalActiveOwnerForms selected)
      ((selectedCompletePath selected).value t) :=
  { vector := direction
    normSqLeOne := coordinateDirection_normSq_le_one
      (historicalClassifiedTangentDirection?_some_mem search)
    slopes := by
      intro form member
      have rootLower :=
        (historicalSlopeSigns_refines_inputCell selected).1.trans lower
      have rootUpper := upper.trans
        (historicalSlopeSigns_refines_inputCell selected).2
      have denominator :=
        (historicalInputCell selected).path_denominator_ne_on_cell
          rootLower rootUpper
      apply (eval_clearedDirectionalSlope_pos_iff form
        (selectedCompletePath selected) direction t denominator).1
      exact historicalClassifiedTangentDirection?_some_clearedSlopes search
        lower upper form member }

end CCLHistoricalEventTangentSigns
end FTA
