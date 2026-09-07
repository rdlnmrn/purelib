import FTA.CCLPositiveEventGrid

/-!
# Common positive-event grid for guarded CCL owners

This module instantiates the finite multi-owner grid over the common selected-
event payload.  It is deliberately separate from the established global-event
adapter: keeping both records concrete avoids expensive dependent-abbreviation
reduction while guarded and global provenance share the same executable grid
construction and semantic proof.
-/

namespace FTA
namespace CCLGuardedEventGrid

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBranchEvidence
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLBranchSampling
open FTA.CCLCompatibleCandidates
open FTA.CCLCoupledController
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventGrid
open FTA.CCLPositiveEventSemantics
open FTA.CentralBandGrid
open FTA.ConstructiveTrack
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- One executable common-payload grid attempt. -/
def eventGridData?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next) :
    Option (EventGridData current separation selected next nextRefines) :=
  match tangentDirectionCertificate?
      (eventPayloadActiveForms current selected base.point) base.point with
  | none => none
  | some direction =>
      if strictCheck :
          ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
          0 < eventPayloadCanonicalValue selected form * form.eval base.point
      then
        if residualCheck :
            ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
            |form.eval base.point| < approximateBoundaryBudget direction
              (eventPayloadPriorForms current selected base.priors base.point
                next.box)
        then some
          { base := base.point
            baseStrict := base.strict
            baseNonzero := base.nonzero
            baseRepresented := base.represented
            basePriors := base.priors
            basePriorsNonzero := base.priorsNonzero
            baseStable := base.stable
            direction := direction
            selectedStrictAtBase := strictCheck
            selectedActiveResidual := residualCheck }
        else none
      else none

def eventGridDataOfIsSome
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next)
    (success : (eventGridData? current separation selected next nextRefines
      base).isSome) :
    EventGridData current separation selected next nextRefines :=
  (eventGridData? current separation selected next nextRefines base).get success

def guardedGridData?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next) :
    Option (GuardedGridData current separation selected next nextRefines) :=
  eventGridData? current separation selected.toPayload.toIncrementalPayload next nextRefines base

def guardedGridDataOfIsSome
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next)
    (success : (guardedGridData? current separation selected next nextRefines
      base).isSome) :
    GuardedGridData current separation selected next nextRefines :=
  (guardedGridData? current separation selected next nextRefines base).get
    success

theorem eventGridData?_isSome_of_direction
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next) (direction : TangentDirection
      (eventPayloadActiveForms current selected base.point) base.point)
    (directionSearch : tangentDirectionCertificate?
      (eventPayloadActiveForms current selected base.point) base.point =
        some direction)
    (strict : ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form * form.eval base.point)
    (residual : ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
      |form.eval base.point| < approximateBoundaryBudget direction
        (eventPayloadPriorForms current selected base.priors base.point
          next.box)) :
    (eventGridData? current separation selected next nextRefines base).isSome :=
  by
    unfold eventGridData?
    rw [directionSearch]
    simp only
    rw [dif_pos strict, dif_pos residual]
    rfl

theorem guardedGridData?_isSome_of_direction
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next) (direction : TangentDirection
      (guardedPositiveEventActiveForms current selected base.point) base.point)
    (directionSearch : tangentDirectionCertificate?
      (guardedPositiveEventActiveForms current selected base.point) base.point =
        some direction)
    (strict : ∀ form ∈
        eventPayloadIncrementalStrictPriorForms selected.toPayload.toIncrementalPayload,
      0 < eventPayloadCanonicalValue selected.toPayload.toIncrementalPayload form *
        form.eval base.point)
    (residual : ∀ form ∈
        eventPayloadIncrementalActiveOwnerForms selected.toPayload.toIncrementalPayload,
      |form.eval base.point| < approximateBoundaryBudget direction
        (guardedPositiveEventPriorForms current selected base.priors base.point
          next.box)) :
    (guardedGridData? current separation selected next nextRefines base).isSome :=
  by
    exact eventGridData?_isSome_of_direction current separation
      selected.toPayload.toIncrementalPayload next nextRefines base direction directionSearch strict
      residual

theorem eventGridData?_fields_of_eq_some
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next)
    {data : EventGridData current separation selected next nextRefines}
    (equality : eventGridData? current separation selected next nextRefines
      base = some data) :
    data.base = base.point ∧ data.basePriors = base.priors := by
  unfold eventGridData? at equality
  generalize directionEquality : tangentDirectionCertificate?
    (eventPayloadActiveForms current selected base.point) base.point =
      directionOption at equality
  cases directionOption with
  | none => simp at equality
  | some direction =>
      simp only at equality
      by_cases strictCheck :
          ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
            0 < eventPayloadCanonicalValue selected form *
              form.eval base.point
      · rw [dif_pos strictCheck] at equality
        by_cases residualCheck :
            ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
              |form.eval base.point| < approximateBoundaryBudget direction
                (eventPayloadPriorForms current selected base.priors
                  base.point next.box)
        · rw [dif_pos residualCheck] at equality
          simp only [Option.some.injEq] at equality
          subst data
          exact ⟨rfl, rfl⟩
        · rw [dif_neg residualCheck] at equality
          contradiction
      · rw [dif_neg strictCheck] at equality
        contradiction

theorem eventGridDataOfIsSome_base
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next)
    (success : (eventGridData? current separation selected next nextRefines
      base).isSome) :
    (eventGridDataOfIsSome current separation selected next nextRefines base
      success).base = base.point := by
  apply (eventGridData?_fields_of_eq_some current separation selected next
    nextRefines base ?_).1
  exact (Option.some_get success).symm

theorem eventGridDataOfIsSome_basePriors
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next)
    (success : (eventGridData? current separation selected next nextRefines
      base).isSome) :
    (eventGridDataOfIsSome current separation selected next nextRefines base
      success).basePriors = base.priors := by
  apply (eventGridData?_fields_of_eq_some current separation selected next
    nextRefines base ?_).2
  exact (Option.some_get success).symm

namespace EventGridData

theorem base_inverseDenominator
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    (adjugate (RawParser.parse current.word).matrix).c * data.base +
        (adjugate (RawParser.parse current.word).matrix).d ≠ 0 :=
  separation_denominator_ne separation
    (nextRefines.contains data.baseStrict.contains)

theorem currentFormula_holds_base
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    (inputStateFormula (RawParser.parse current.word)).Holds data.base := by
  rcases data.baseRepresented with ⟨tail, represents⟩
  apply inputStateFormula_holds_of_represents
    (RawParser.parse current.word) data.base tail
    (by simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word)
    (base_inverseDenominator data) represents

theorem currentEvaluation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    formulaEvalWith (inputStateFormula (RawParser.parse current.word))
      (fun form => form.eval data.base) = true :=
  (formulaEvalWith_eval_eq_true_iff
    (inputStateFormula (RawParser.parse current.word)) data.base).2
      (currentFormula_holds_base data)

theorem priors_nonzero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    ∀ form ∈ eventPayloadPriorForms current selected data.basePriors
      data.base next.box,
      form.eval data.base ≠ 0 := by
  intro form member
  simp only [eventPayloadPriorForms, List.mem_append,
    List.mem_singleton] at member
  rcases member with ((currentPrior | selectedStrict) | boxForm) | normForm
  · exact data.basePriorsNonzero form currentPrior
  · intro zero
    have positive := data.selectedStrictAtBase form selectedStrict
    rw [zero] at positive
    norm_num at positive
  · exact (boxForms_pos_of_strictContains data.baseStrict form boxForm).ne'
  · subst form
    simpa [eval_affineNormForm] using
      (normSq_pos data.baseNonzero).ne'

theorem active_residual
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    ∀ form ∈ eventPayloadActiveForms current selected data.base,
      |form.eval data.base| < approximateBoundaryBudget data.direction
        (eventPayloadPriorForms current selected data.basePriors data.base
          next.box) := by
  intro form member
  exact data.selectedActiveResidual form member

def point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) : QI :=
  step data.base
    (multiOwnerEpsilon data.direction
      (eventPayloadPriorForms current selected data.basePriors data.base
        next.box))
    data.direction.vector

theorem entered
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    ∀ form ∈ eventPayloadActiveForms current selected data.base,
      0 < form.eval (point data) := by
  simpa only [point] using
    (enters_all_boundaries_of_residual data.direction
      (eventPayloadPriorForms current selected data.basePriors data.base
        next.box)
      (priors_nonzero data) (active_residual data))

theorem preserved
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    ∀ form ∈ eventPayloadPriorForms current selected data.basePriors
      data.base next.box,
      0 < form.eval data.base * form.eval (point data) := by
  simpa only [point] using
    (preserves_all_priors data.direction
      (eventPayloadPriorForms current selected data.basePriors data.base
        next.box)
      (priors_nonzero data))

theorem point_inside
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    next.box.Contains (point data) := by
  change next.box.Contains (step data.base
    (multiOwnerEpsilon data.direction
      (eventPayloadPriorForms current selected data.basePriors data.base
        next.box))
    data.direction.vector)
  apply multiOwner_step_mem_box_of_strict_priors data.direction
    (priors_nonzero data) next.box
    (boxForms_pos_of_strictContains data.baseStrict)
  intro form member
  simp [eventPayloadPriorForms, member]

theorem point_nonzero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    point data ≠ 0 := by
  let normForm := affineNormForm 1 0
  have normMember : normForm ∈
      eventPayloadPriorForms current selected data.basePriors data.base
        next.box := by
    simp [eventPayloadPriorForms, normForm]
  have product := preserved data normForm normMember
  have basePositive : 0 < normForm.eval data.base := by
    simpa [normForm, eval_affineNormForm] using normSq_pos data.baseNonzero
  have pointPositive : 0 < normForm.eval (point data) := by
    rcases mul_pos_iff.mp product with signs | signs
    · exact signs.2
    · exact (not_lt_of_ge basePositive.le signs.1).elim
  intro zero
  rw [zero] at pointPositive
  simp [normForm, eval_affineNormForm, normSq_zero] at pointPositive

theorem currentFormula_holds_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    (inputStateFormula (RawParser.parse current.word)).Holds
      (point data) := by
  have represented :
      RawParserSemantics.Represented current.word (point data) := by
    apply data.baseStable
      ((nextRefines.trans separation.refines).contains (point_inside data))
    intro form member
    apply preserved data form
    simp [eventPayloadPriorForms, member]
  rcases represented with ⟨tail, represents⟩
  apply inputStateFormula_holds_of_represents
    (RawParser.parse current.word) (point data) tail
    (by simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word)
    (separation_denominator_ne separation
      (nextRefines.contains (point_inside data))) represents

theorem point_represented
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    RawParserSemantics.Represented current.word (point data) := by
  apply data.baseStable
    ((nextRefines.trans separation.refines).contains (point_inside data))
  intro form member
  apply preserved data form
  simp [eventPayloadPriorForms, member]

theorem selectedIncrementalFormula_holds_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    (inputIncrementalAdvanceFormula (RawParser.parse current.word)
      selected.bit).Holds (point data) := by
  apply eventPayloadIncremental_holds_of_owner_form_lists selected (point data)
  · intro form member
    exact entered data form member
  · intro form member
    apply mul_pos_trans (data.selectedStrictAtBase form member)
    apply preserved data form
    simp [eventPayloadPriorForms, member]

theorem selectedStrictAtPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form *
        form.eval (point data) := by
  intro form member
  apply mul_pos_trans (data.selectedStrictAtBase form member)
  apply preserved data form
  simp [eventPayloadPriorForms, member]

def sample
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : EventGridData current separation selected next nextRefines) :
    OwnerInputSample current selected.bit next separation.state.box where
  outcome :=
    { point := point data
      inside := point_inside data
      nonzero := point_nonzero data
      semantics :=
        CCLBranchSampling.represented_append_of_inputIncrementalFormula
        current.word (point data) selected.bit
        (separation_denominator_ne separation
          (nextRefines.contains (point_inside data)))
        (point_represented data) (selectedIncrementalFormula_holds_point data)
      priors := data.basePriors ++
        eventPayloadIncrementalActiveOwnerForms selected ++
        eventPayloadIncrementalStrictPriorForms selected
      priorsNonzero := by
        intro form member
        simp only [List.mem_append] at member
        rcases member with (currentPrior | selectedActive) | selectedStrict
        · have product := preserved data form (by
            simp [eventPayloadPriorForms, currentPrior])
          intro zero
          have impossible : ¬(0 <
              form.eval data.base * form.eval (point data)) := by
            simp [zero]
          exact impossible product
        · exact (entered data form selectedActive).ne'
        · have positive := mul_pos_trans
            (data.selectedStrictAtBase form selectedStrict)
            (preserved data form (by
              simp [eventPayloadPriorForms, selectedStrict]))
          intro zero
          have impossible : ¬(0 < eventPayloadCanonicalValue selected form *
              form.eval (point data)) := by
            simp [zero]
          exact impossible positive
      stable := by
        intro candidate inside preservedSigns
        have oldRepresented :
            RawParserSemantics.Represented current.word candidate := by
          apply data.baseStable (separation.refines.contains inside)
          intro form member
          apply mul_pos_trans
            (preserved data form (by
              simp [eventPayloadPriorForms, member]))
          exact preservedSigns form (by simp [member])
        have selectedHolds :
            (inputIncrementalAdvanceFormula (RawParser.parse current.word)
              selected.bit).Holds candidate := by
          apply eventPayloadIncremental_holds_of_owner_form_lists selected
            candidate
          · intro form member
            have atGrid := entered data form member
            have sameSign := preservedSigns form (by simp [member])
            rcases mul_pos_iff.mp sameSign with signs | signs
            · exact signs.2
            · exact (not_lt_of_ge atGrid.le signs.1).elim
          · intro form member
            apply mul_pos_trans
              (mul_pos_trans (data.selectedStrictAtBase form member)
                (preserved data form (by
                  simp [eventPayloadPriorForms, member])))
            exact preservedSigns form (by simp [member])
        exact CCLBranchSampling.represented_append_of_inputIncrementalFormula
          current.word candidate selected.bit
          (separation_denominator_ne separation inside)
          oldRepresented selectedHolds }

end EventGridData

/-- Successful common-payload grid data in every later winding box, coherent
with the coupled state's fixed historical sign neighbourhood. -/
structure PersistentEventGridDataFamily
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation) where
  data : (next : WindingOneState p ambient) →
    (nextRefines : next.box.Refines separation.state.box) →
      EventGridData current separation selected next nextRefines
  basePriors : ∀ next nextRefines,
    (data next nextRefines).basePriors = current.priors
  baseSameSigns : ∀ next nextRefines form, form ∈ current.priors →
    0 < form.eval current.sample * form.eval (data next nextRefines).base

def PersistentEventGridDataFamily.ownerSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    (family : PersistentEventGridDataFamily current separation selected) :
    PersistentEventOwnerSamples current separation selected where
  sample next nextRefines := EventGridData.sample (family.data next nextRefines)
  sample_priors := by
    intro next nextRefines
    have anchorPriors := family.basePriors separation.state
      (RatBox.refines_refl separation.state.box)
    have nextPriors := family.basePriors next nextRefines
    change (family.data next nextRefines).basePriors ++
        eventPayloadIncrementalActiveOwnerForms selected ++
          eventPayloadIncrementalStrictPriorForms selected =
      (family.data separation.state
        (RatBox.refines_refl separation.state.box)).basePriors ++
          eventPayloadIncrementalActiveOwnerForms selected ++
            eventPayloadIncrementalStrictPriorForms selected
    rw [nextPriors, anchorPriors]
  sample_sameSigns := by
    intro next nextRefines form member
    let anchor := family.data separation.state
      (RatBox.refines_refl separation.state.box)
    let later := family.data next nextRefines
    change form ∈ anchor.basePriors ++
      eventPayloadIncrementalActiveOwnerForms selected ++
        eventPayloadIncrementalStrictPriorForms selected at member
    change 0 < form.eval (EventGridData.point anchor) *
      form.eval (EventGridData.point later)
    simp only [List.mem_append] at member
    rcases member with (old | active) | strict
    · have oldCurrent : form ∈ current.priors := by
        rw [← family.basePriors separation.state
          (RatBox.refines_refl separation.state.box)]
        exact old
      have anchorPreserved := EventGridData.preserved anchor form (by
        simp [eventPayloadPriorForms, old])
      have baseToBase := CCLCoupledTrack.sameSign_of_common_anchor
        (family.baseSameSigns separation.state
          (RatBox.refines_refl separation.state.box) form oldCurrent)
        (family.baseSameSigns next nextRefines form oldCurrent)
      have laterOld : form ∈ later.basePriors := by
        rw [family.basePriors next nextRefines]
        exact oldCurrent
      have laterPreserved := EventGridData.preserved later form (by
        simp [eventPayloadPriorForms, laterOld])
      have anchorPointToBase :
          0 < form.eval (EventGridData.point anchor) * form.eval anchor.base := by
        rw [_root_.mul_comm]
        exact anchorPreserved
      apply mul_pos_trans
      · apply mul_pos_trans
        · exact anchorPointToBase
        · exact baseToBase
      · exact laterPreserved
    · exact mul_pos (EventGridData.entered anchor form active)
        (EventGridData.entered later form active)
    · exact CCLCoupledTrack.sameSign_of_common_anchor
        (EventGridData.selectedStrictAtPoint anchor form strict)
        (EventGridData.selectedStrictAtPoint later form strict)

abbrev PersistentGuardedGridDataFamily
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation) :=
  PersistentEventGridDataFamily current separation selected.toPayload.toIncrementalPayload

def PersistentGuardedGridDataFamily.ownerSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedGuardEventCount separation}
    (family : PersistentGuardedGridDataFamily current separation selected) :
    PersistentGuardOwnerSamples current separation selected :=
  PersistentEventGridDataFamily.ownerSamples family

def eventGridSample?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next) :
    Option (OwnerInputSample current selected.bit next separation.state.box) :=
  (eventGridData? current separation selected next nextRefines base).map
    fun data => EventGridData.sample data

def guardedGridSample?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next) :
    Option (OwnerInputSample current selected.bit next separation.state.box) :=
  eventGridSample? current separation selected.toPayload.toIncrementalPayload next nextRefines base

def eventGridSampleAtWidth?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    Option (OwnerInputSample current selected.bit next separation.state.box) :=
  let inner := refineState squarefree elimination next epsilon epsilonPositive
  let strict := refineState_strictInterior squarefree elimination next epsilon
    epsilonPositive
  let base := gridBaseOfCurrentRefinement current next inner
    (nextRefines.trans separation.refines) strict
  eventGridSample? current separation selected next nextRefines base

def guardedGridSampleAtWidth?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    Option (OwnerInputSample current selected.bit next separation.state.box) :=
  eventGridSampleAtWidth? current separation selected.toPayload.toIncrementalPayload squarefree
    elimination next nextRefines epsilon epsilonPositive

end CCLGuardedEventGrid
end FTA
