import FTA.CCLPositiveEventGrid

/-!
# Quantitative approximation of selected positive CCL events

The event classifier already separates every selected formula atom into an
exact multiple of the isolated event factor or a strict coprime sign.  This
module exposes those two alternatives at the rational endpoint returned by
the bounded event refinement, before comparing that point with the coupled
track's represented sample.
-/

namespace FTA
namespace CCLPositiveEventApproximation

open CCL CCL.GaussianRat
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLPositiveEventSemantics
open FTA.ComputablePolynomial.DensePolynomial
open FTA.RootCountDivisibility
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Owner-independent form of the active-face approximation estimate.  If
the isolated event factor divides the cleared Hermitian form, narrowing the
event cell makes the genuine affine form value small.  This applies in the
all-`neither` branch, where there is no selected owner payload from which to
recover the same divisibility fact. -/
theorem inputEventFormAtApproximation_le_of_dvd
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : CCLBranchEvent.RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) (form : HermitianForm)
    (divides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form path).toPolynomial) :
    |form.eval (path.value
        (cell.clearedApproximation epsilon epsilonPositive).refined.interval.lower)| ≤
      approximationBound (clearedForm form path)
          cell.branch.factor.polynomial
          (cell.branch.computeEventSigns cell.parent).refined epsilon /
        (CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
          event).bound := by
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let t := approximation.refined.interval.lower
  let denominator :=
    CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate event
  have small := approximation.multipleSmall divides epsilonPositive.le
  have pathDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
    apply cell.path_denominator_ne_on_cell
    · exact approximation.refines.1
    · exact approximation.refined.proper.le.trans approximation.refines.2
  have denominatorLower : denominator.bound ≤
      (CCLPathIntersection.denominatorNorm path).eval t := by
    apply denominator.lower
    · exact cell.signRefines.1.trans approximation.refines.1
    · exact (approximation.refined.proper.le.trans approximation.refines.2).trans
        cell.signRefines.2
  apply (le_div_iff₀ denominator.positive).2
  calc
    |form.eval (path.value t)| * denominator.bound =
        denominator.bound * |form.eval (path.value t)| := by ring
    _ ≤ (CCLPathIntersection.denominatorNorm path).eval t *
          |form.eval (path.value t)| :=
      mul_le_mul_of_nonneg_right denominatorLower (abs_nonneg _)
    _ = |(clearedForm form path).eval t| := by
      rw [eval_clearedForm form path t pathDenominator, abs_mul,
        abs_of_pos (CCLPathIntersection.eval_denominatorNorm_pos path t
          pathDenominator)]
    _ ≤ approximationBound (clearedForm form path)
          cell.branch.factor.polynomial
          (cell.branch.computeEventSigns cell.parent).refined epsilon := by
      simpa only [approximation, t] using small

private theorem selectedAtomPolynomial_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {atom : CCLParserGeometry.Atom}
    (member : atom ∈ satisfyingAtoms
      (inputIncrementalAdvanceFormula state selected.bit)
      (eventPayloadCanonicalValue selected)) :
    clearedForm atom.form
        selected.candidate.sourceEvent.partition.entry.chart.path ∈
      inputEventPolynomials state
        selected.candidate.sourceEvent.partition.entry.chart.path := by
  have atomMember := satisfyingAtoms_mem_formulaAtoms
    (inputIncrementalAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected) member
  have completeAtomMember :=
    inputIncrementalAdvanceFormula_atoms_subset state selected.bit atom
      atomMember
  cases bitEq : selected.bit with
  | false =>
      simp only [bitEq] at completeAtomMember
      simp only [inputEventPolynomials, eventFormulaPolynomials, formulaAtoms,
        List.map_append, List.mem_append, List.mem_map]
      exact Or.inl ⟨atom, completeAtomMember, rfl⟩
  | true =>
      simp only [bitEq] at completeAtomMember
      simp only [inputEventPolynomials, eventFormulaPolynomials, formulaAtoms,
        List.map_append, List.mem_append, List.mem_map]
      exact Or.inr ⟨atom, completeAtomMember, rfl⟩

/-- Every atom selected from the complete next-bit formula occurs in the
shared event-condition classifier.  Unlike the incremental specialization
above, this includes the historical parser constraints retained by the
ordinary next state. -/
private theorem selectedCompleteAtomPolynomial_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {atom : CCLParserGeometry.Atom}
    (member : atom ∈ satisfyingAtoms
      (inputAdvanceFormula state selected.bit)
      (eventPayloadCanonicalValue selected.toIncrementalPayload)) :
    clearedForm atom.form
        selected.candidate.sourceEvent.partition.entry.chart.path ∈
      inputEventPolynomials state
        selected.candidate.sourceEvent.partition.entry.chart.path := by
  have atomMember := satisfyingAtoms_mem_formulaAtoms
    (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected.toIncrementalPayload) member
  cases bitEq : selected.bit with
  | false =>
      simp only [bitEq] at atomMember
      simp only [inputEventPolynomials, eventFormulaPolynomials, formulaAtoms,
        List.map_append, List.mem_append, List.mem_map]
      exact Or.inl ⟨atom, atomMember, rfl⟩
  | true =>
      simp only [bitEq] at atomMember
      simp only [inputEventPolynomials, eventFormulaPolynomials, formulaAtoms,
        List.map_append, List.mem_append, List.mem_map]
      exact Or.inr ⟨atom, atomMember, rfl⟩

theorem selectedStrictPolynomial_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalStrictPriorForms selected) :
    clearedForm form
        selected.candidate.sourceEvent.partition.entry.chart.path ∈
      inputEventPolynomials state
        selected.candidate.sourceEvent.partition.entry.chart.path := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  exact selectedAtomPolynomial_mem selected
    (strictSatisfyingAtoms_source atomMember)

/-- Complete-form counterpart of `selectedStrictPolynomial_mem`. -/
theorem selectedCompleteStrictPolynomial_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadStrictPriorForms selected) :
    clearedForm form
        selected.candidate.sourceEvent.partition.entry.chart.path ∈
      inputEventPolynomials state
        selected.candidate.sourceEvent.partition.entry.chart.path := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  exact selectedCompleteAtomPolynomial_mem selected
    (strictSatisfyingAtoms_source atomMember)

theorem selectedActivePolynomial_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    selected.candidate.inputCell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form
        selected.candidate.sourceEvent.partition.entry.chart.path).toPolynomial := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  have polynomialMember := selectedAtomPolynomial_mem selected
    (activeSatisfyingAtoms_source atomMember)
  have canonicalZero := activeSatisfyingAtoms_zero atomMember
  have divides :=
    ConditionRelations.dvd_of_canonicalEventValue_eq_zero
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent)
      polynomialMember (by
        simpa only [eventPayloadCanonicalValue,
          toIncrementalPayload_candidate] using canonicalZero)
  rcases atom with ⟨atomForm, sign⟩
  cases sign with
  | negative => simpa [orientedWeakForm] using divides
  | nonpositive =>
      have negIdentity :
          (clearedForm atomForm.neg
            selected.candidate.sourceEvent.partition.entry.chart.path).toPolynomial =
          -(clearedForm atomForm
            selected.candidate.sourceEvent.partition.entry.chart.path).toPolynomial := by
        simp only [clearedForm, HermitianForm.neg, toPolynomial_add,
          toPolynomial_scale]
        simp
        abel
      change selected.candidate.inputCell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm atomForm.neg
          selected.candidate.sourceEvent.partition.entry.chart.path).toPolynomial
      rw [negIdentity]
      exact dvd_neg.mpr (by simpa using divides)
  | zero => simpa [orientedWeakForm] using divides
  | nonzero => simpa [orientedWeakForm] using divides
  | nonnegative => simpa [orientedWeakForm] using divides
  | positive => simpa [orientedWeakForm] using divides

/-- Every canonically active face of the complete selected child formula is
an exact multiple of the isolated event factor.  This is the algebraic fact
needed to sample the complete parser cell without importing a separately
chosen represented point and its radius-dependent prior list. -/
theorem selectedCompleteActivePolynomial_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    selected.candidate.inputCell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form
        selected.candidate.sourceEvent.partition.entry.chart.path).toPolynomial := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  have polynomialMember := selectedCompleteAtomPolynomial_mem selected
    (activeSatisfyingAtoms_source atomMember)
  have canonicalZero := activeSatisfyingAtoms_zero atomMember
  change (canonicalEventValue
    selected.candidate.inputCell.branch.factor.input
    (clearedForm atom.form
      selected.candidate.sourceEvent.partition.entry.chart.path)
    (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined.interval.lower = 0) at canonicalZero
  have divides :=
    ConditionRelations.dvd_of_canonicalEventValue_eq_zero
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent)
      polynomialMember (by
        simpa only [eventPayloadCanonicalValue] using canonicalZero)
  rcases atom with ⟨atomForm, sign⟩
  cases sign with
  | negative => simpa [orientedWeakForm] using divides
  | nonpositive =>
      have negIdentity :
          (clearedForm atomForm.neg
            selected.candidate.sourceEvent.partition.entry.chart.path).toPolynomial =
          -(clearedForm atomForm
            selected.candidate.sourceEvent.partition.entry.chart.path).toPolynomial := by
        simp only [clearedForm, HermitianForm.neg, toPolynomial_add,
          toPolynomial_scale]
        simp
        abel
      change selected.candidate.inputCell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm atomForm.neg
          selected.candidate.sourceEvent.partition.entry.chart.path).toPolynomial
      rw [negIdentity]
      exact dvd_neg.mpr (by simpa using divides)
  | zero => simpa [orientedWeakForm] using divides
  | nonzero => simpa [orientedWeakForm] using divides
  | nonnegative => simpa [orientedWeakForm] using divides
  | positive => simpa [orientedWeakForm] using divides

/-- The already bounded event refinement, reused for every selected owner
form at one requested parameter width. -/
def selectedApproximation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :=
  selected.candidate.inputCell.clearedApproximation epsilon epsilonPositive

def selectedApproximationParameter
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) : ℚ :=
  (selectedApproximation selected epsilon epsilonPositive).refined.interval.lower

def selectedApproximationPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) : QI :=
  selected.candidate.sourceEvent.partition.entry.chart.path.value
    (selectedApproximationParameter selected epsilon epsilonPositive)

theorem selectedApproximationParameter_lower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined.interval.lower ≤
      selectedApproximationParameter selected epsilon epsilonPositive := by
  exact (selectedApproximation selected epsilon epsilonPositive).refines.1

theorem selectedApproximationParameter_upper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    selectedApproximationParameter selected epsilon epsilonPositive ≤
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval.upper := by
  exact (selectedApproximation selected epsilon epsilonPositive).refined.proper.le.trans
    (selectedApproximation selected epsilon epsilonPositive).refines.2

theorem selectedApproximation_denominator_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    selected.candidate.sourceEvent.partition.entry.chart.path.denominator.eval
      (PathPolynomial.ofRat
        (selectedApproximationParameter selected epsilon epsilonPositive)) ≠ 0 := by
  apply CCLBranchEventOwner.RelevantCurveEvent.ownerDenominator_ne
    selected.candidate.sourceEvent.event
  · exact selected.candidate.inputCell.signRefines.1.trans
      (selectedApproximationParameter_lower selected epsilon epsilonPositive)
  · exact (selectedApproximationParameter_upper selected epsilon
      epsilonPositive).trans selected.candidate.inputCell.signRefines.2

/-- Every selected strict atom already has its canonical sign at the common
rational event approximation; no limiting argument is needed for this half. -/
theorem selectedStrictAtApproximation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form *
        form.eval (selectedApproximationPoint selected epsilon epsilonPositive) := by
  intro form member
  let path := selected.candidate.sourceEvent.partition.entry.chart.path
  let signs := selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent
  let t := selectedApproximationParameter selected epsilon epsilonPositive
  have polynomialSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent signs
      (selectedStrictPolynomial_mem selected member)
      (by
        simpa only [eventPayloadCanonicalValue,
          toIncrementalPayload_candidate] using
          strictPriorForms_value_ne
            (inputIncrementalAdvanceFormula state selected.bit)
            (eventPayloadCanonicalValue selected) member)
      (selectedApproximationParameter_lower selected epsilon epsilonPositive)
      (selectedApproximationParameter_upper selected epsilon epsilonPositive)
  have denominator := selectedApproximation_denominator_ne selected epsilon
    epsilonPositive
  have denominatorPositive := CCLPathIntersection.eval_denominatorNorm_pos
    path t denominator
  rw [eval_clearedForm form path t denominator] at polynomialSign
  have rearranged : 0 <
      (CCLPathIntersection.denominatorNorm path).eval t *
        (eventPayloadCanonicalValue selected form *
          form.eval (selectedApproximationPoint selected epsilon
            epsilonPositive)) := by
    simpa only [path, signs, t, eventPayloadCanonicalValue,
      toIncrementalPayload_candidate,
      selectedApproximationPoint, mul_assoc, mul_left_comm, mul_comm] using
        polynomialSign
  rcases mul_pos_iff.mp rearranged with positive | negative
  · exact positive.2
  · exact (not_lt_of_ge denominatorPositive.le negative.1).elim

/-- Every canonically strict atom of the complete selected child formula has
its fixed algebraic-event sign at the common rational approximation. -/
theorem selectedCompleteStrictAtApproximation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    ∀ form ∈ eventPayloadStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected.toIncrementalPayload form *
        form.eval (selectedApproximationPoint selected.toIncrementalPayload
          epsilon epsilonPositive) := by
  intro form member
  let path := selected.candidate.sourceEvent.partition.entry.chart.path
  let signs := selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent
  let t := selectedApproximationParameter selected.toIncrementalPayload epsilon
    epsilonPositive
  have canonicalNonzero := strictPriorForms_value_ne
    (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected.toIncrementalPayload) member
  change canonicalEventValue
    selected.candidate.inputCell.branch.factor.input
    (clearedForm form selected.candidate.sourceEvent.partition.entry.chart.path)
    signs.refined.interval.lower ≠ 0 at canonicalNonzero
  have polynomialSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent signs
      (selectedCompleteStrictPolynomial_mem selected member)
      (by simpa only [eventPayloadCanonicalValue] using canonicalNonzero)
      (selectedApproximationParameter_lower selected.toIncrementalPayload
        epsilon epsilonPositive)
      (selectedApproximationParameter_upper selected.toIncrementalPayload
        epsilon epsilonPositive)
  have denominator := selectedApproximation_denominator_ne
    selected.toIncrementalPayload epsilon epsilonPositive
  have denominatorPositive := CCLPathIntersection.eval_denominatorNorm_pos
    path t denominator
  rw [eval_clearedForm form path t denominator] at polynomialSign
  have rearranged : 0 <
      (CCLPathIntersection.denominatorNorm path).eval t *
        (eventPayloadCanonicalValue selected.toIncrementalPayload form *
          form.eval (selectedApproximationPoint selected.toIncrementalPayload
            epsilon epsilonPositive)) := by
    unfold eventPayloadCanonicalValue selectedApproximationPoint
    rw [toIncrementalPayload_candidate selected]
    simpa only [path, signs, t, eventPayloadCanonicalValue,
      mul_assoc, mul_left_comm, mul_comm] using
        polynomialSign
  rcases mul_pos_iff.mp rearranged with positive | negative
  · exact positive.2
  · exact (not_lt_of_ge denominatorPositive.le negative.1).elim

/-- Canonically active selected forms are linearly small in the requested
event-parameter width, with the already computed projective denominator
margin made explicit. -/
theorem selectedActiveAtApproximation_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    |form.eval (selectedApproximationPoint selected epsilon epsilonPositive)| ≤
      approximationBound
          (clearedForm form
            selected.candidate.sourceEvent.partition.entry.chart.path)
          selected.candidate.inputCell.branch.factor.polynomial
          (selected.candidate.inputCell.branch.computeEventSigns
            selected.candidate.inputCell.parent).refined epsilon /
        (CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
          selected.candidate.sourceEvent.event).bound := by
  let path := selected.candidate.sourceEvent.partition.entry.chart.path
  let approximation := selectedApproximation selected epsilon epsilonPositive
  let t := selectedApproximationParameter selected epsilon epsilonPositive
  let denominator :=
    CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event
  have small := approximation.multipleSmall
    (selectedActivePolynomial_dvd selected member) epsilonPositive.le
  have pathDenominator := selectedApproximation_denominator_ne selected epsilon
    epsilonPositive
  have denominatorLower : denominator.bound ≤
      (CCLPathIntersection.denominatorNorm path).eval t := by
    apply denominator.lower
    · exact selected.candidate.inputCell.signRefines.1.trans
        (selectedApproximationParameter_lower selected epsilon epsilonPositive)
    · exact (selectedApproximationParameter_upper selected epsilon
        epsilonPositive).trans selected.candidate.inputCell.signRefines.2
  apply (le_div_iff₀ denominator.positive).2
  calc
    |form.eval (selectedApproximationPoint selected epsilon epsilonPositive)| *
          denominator.bound =
        denominator.bound *
          |form.eval (selectedApproximationPoint selected epsilon
            epsilonPositive)| := by ring
    _ ≤ (CCLPathIntersection.denominatorNorm path).eval t *
          |form.eval (selectedApproximationPoint selected epsilon
            epsilonPositive)| :=
      mul_le_mul_of_nonneg_right denominatorLower (abs_nonneg _)
    _ = |(clearedForm form path).eval t| := by
      rw [eval_clearedForm form path t pathDenominator, abs_mul,
        abs_of_pos (CCLPathIntersection.eval_denominatorNorm_pos path t
          pathDenominator)]
      rfl
    _ ≤ approximationBound (clearedForm form path)
          selected.candidate.inputCell.branch.factor.polynomial
          (selected.candidate.inputCell.branch.computeEventSigns
            selected.candidate.inputCell.parent).refined epsilon := by
      simpa only [approximation, path, t, selectedApproximation,
        toIncrementalPayload_candidate,
        selectedApproximationParameter] using small

/-- Complete-form active faces obey the same explicit approximation bound.
The bound depends only on classified polynomial data and the requested
parameter width, not on an opaque represented sample. -/
theorem selectedCompleteActiveAtApproximation_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    |form.eval (selectedApproximationPoint selected.toIncrementalPayload epsilon
      epsilonPositive)| ≤
      approximationBound
          (clearedForm form
            selected.candidate.sourceEvent.partition.entry.chart.path)
          selected.candidate.inputCell.branch.factor.polynomial
          (selected.candidate.inputCell.branch.computeEventSigns
            selected.candidate.inputCell.parent).refined epsilon /
        (CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
          selected.candidate.sourceEvent.event).bound := by
  let path := selected.candidate.sourceEvent.partition.entry.chart.path
  let approximation := selectedApproximation selected.toIncrementalPayload
    epsilon epsilonPositive
  let t := selectedApproximationParameter selected.toIncrementalPayload epsilon
    epsilonPositive
  let denominator :=
    CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event
  have small := approximation.multipleSmall
    (selectedCompleteActivePolynomial_dvd selected member) epsilonPositive.le
  change |(clearedForm form path).eval
      approximation.refined.interval.lower| ≤
    approximationBound (clearedForm form path)
      selected.candidate.inputCell.branch.factor.polynomial
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined epsilon at small
  have pathDenominator := selectedApproximation_denominator_ne
    selected.toIncrementalPayload epsilon epsilonPositive
  have denominatorLower : denominator.bound ≤
      (CCLPathIntersection.denominatorNorm path).eval t := by
    apply denominator.lower
    · exact selected.candidate.inputCell.signRefines.1.trans
        (selectedApproximationParameter_lower selected.toIncrementalPayload
          epsilon epsilonPositive)
    · exact (selectedApproximationParameter_upper
        selected.toIncrementalPayload epsilon epsilonPositive).trans
          selected.candidate.inputCell.signRefines.2
  apply (le_div_iff₀ denominator.positive).2
  calc
    |form.eval (selectedApproximationPoint selected.toIncrementalPayload epsilon
          epsilonPositive)| *
          denominator.bound =
        denominator.bound *
          |form.eval (selectedApproximationPoint selected.toIncrementalPayload
            epsilon epsilonPositive)| := by ring
    _ ≤ (CCLPathIntersection.denominatorNorm path).eval t *
          |form.eval (selectedApproximationPoint selected.toIncrementalPayload
            epsilon epsilonPositive)| :=
      mul_le_mul_of_nonneg_right denominatorLower (abs_nonneg _)
    _ = |(clearedForm form path).eval t| := by
      rw [eval_clearedForm form path t pathDenominator, abs_mul,
        abs_of_pos (CCLPathIntersection.eval_denominatorNorm_pos path t
          pathDenominator)]
      rfl
    _ ≤ approximationBound (clearedForm form path)
          selected.candidate.inputCell.branch.factor.polynomial
          (selected.candidate.inputCell.branch.computeEventSigns
            selected.candidate.inputCell.parent).refined epsilon := by
      simpa only [approximation, path, t, selectedApproximation,
        selectedApproximationParameter] using small

end CCLPositiveEventApproximation
end FTA
