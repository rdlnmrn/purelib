import FTA.CCLCoupledController
import FTA.CCLMultiOwnerGrid
import FTA.CCLPositiveEventSemantics

/-!
# Approximate multi-owner grid for a positive CCL event

This module packages the finite reciprocal perturbation after geometric
localization has supplied a represented base point near the selected algebraic
event.  Current-prefix active equalities are exact at that base point; selected
event equalities need only meet the explicit approximate-boundary budget.

The construction is deliberately factored into small declarations.  No one
proof elaborates localization, the classified-event oracle, the parser syntax,
and the multi-owner estimates simultaneously.
-/

namespace FTA
namespace CCLPositiveEventGrid

open CCL CCL.GaussianRat
open FTA.CCLBranchEvidence
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLCompatibleCandidates
open FTA.CCLCoupledController
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventSemantics
open FTA.CentralBandGrid
open FTA.ConstructiveTrack
open FTA.AxisSafeCuts
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Active old-prefix equalities at one represented rational base point. -/
def currentActiveOwnerForms
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient) (base : QI) :
    List HermitianForm :=
  activeOwnerForms (inputStateFormula (RawParser.parse current.word))
    (fun form => form.eval base)

/-- Strict old-prefix signs at the same base point. -/
def currentStrictPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient) (base : QI) :
    List HermitianForm :=
  strictPriorForms (inputStateFormula (RawParser.parse current.word))
    (fun form => form.eval base)

def positiveEventActiveForms
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventCount separation) (_base : QI) :
    List HermitianForm :=
  selectedIncrementalActiveOwnerForms selected

/-- Protected forms: the stable old-prefix branch, selected strict signs, four
inward box forms, and the norm form that preserves nonzeroness. -/
def positiveEventPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventCount separation)
    (currentPriors : List HermitianForm) (_base : QI) (box : RatBox) :
    List HermitianForm :=
  currentPriors ++ selectedIncrementalStrictPriorForms selected ++
    boxForms box ++
      [affineNormForm 1 0]

def eventPayloadActiveForms
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : IncrementalEventPayload separation) (_base : QI) :
    List HermitianForm :=
  eventPayloadIncrementalActiveOwnerForms selected

def eventPayloadPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : IncrementalEventPayload separation)
    (currentPriors : List HermitianForm) (_base : QI) (box : RatBox) :
    List HermitianForm :=
  currentPriors ++ eventPayloadIncrementalStrictPriorForms selected ++
    boxForms box ++ [affineNormForm 1 0]

def guardedPositiveEventActiveForms
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedGuardEventCount separation) (base : QI) :
    List HermitianForm :=
  eventPayloadActiveForms current selected.toPayload.toIncrementalPayload base

def guardedPositiveEventPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedGuardEventCount separation)
    (currentPriors : List HermitianForm) (base : QI) (box : RatBox) :
    List HermitianForm :=
  eventPayloadPriorForms current selected.toPayload.toIncrementalPayload
    currentPriors base box

theorem positiveEventActiveForms_eq_payload
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventCount separation) (base : QI) :
    positiveEventActiveForms current selected base =
      eventPayloadActiveForms current selected.toPayload.toIncrementalPayload
        base := rfl

theorem positiveEventPriorForms_eq_payload
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventCount separation)
    (currentPriors : List HermitianForm) (base : QI) (box : RatBox) :
    positiveEventPriorForms current selected currentPriors base box =
      eventPayloadPriorForms current selected.toPayload.toIncrementalPayload
        currentPriors base box :=
  rfl

theorem boxForms_pos_of_strictContains
    {box : RatBox} {base : QI} (strict : box.StrictContains base) :
    ∀ form ∈ boxForms box, 0 < form.eval base := by
  intro form member
  simp [boxForms] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [eval_boxXLowerForm]
    linarith [strict.1]
  · rw [eval_boxXUpperForm]
    linarith [strict.2.1]
  · rw [eval_boxYLowerForm]
    linarith [strict.2.2.1]
  · rw [eval_boxYUpperForm]
    linarith [strict.2.2.2]

theorem mul_pos_trans {a b c : ℚ} (first : 0 < a * b)
    (second : 0 < b * c) : 0 < a * c := by
  rcases mul_pos_iff.mp first with ⟨aPositive, bPositive⟩ |
      ⟨aNegative, bNegative⟩
  · rcases mul_pos_iff.mp second with ⟨_bPositive, cPositive⟩ |
        ⟨bNegative, _cNegative⟩
    · exact mul_pos aPositive cPositive
    · exact (not_lt_of_ge bPositive.le bNegative).elim
  · rcases mul_pos_iff.mp second with ⟨bPositive, _cPositive⟩ |
        ⟨_bNegative, cNegative⟩
    · exact (not_lt_of_ge bPositive.le bNegative).elim
    · exact mul_pos_of_neg_of_neg aNegative cNegative

/-- Represented old-prefix point already strictly inside the requested owner
box. -/
structure GridBase
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (next : WindingOneState p ambient) where
  point : QI
  strict : next.box.StrictContains point
  nonzero : point ≠ 0
  represented : RawParserSemantics.Represented current.word point
  priors : List HermitianForm
  priorsNonzero : ∀ form ∈ priors, form.eval point ≠ 0
  stable : ∀ {nextPoint : QI}, current.numerical.box.Contains nextPoint →
    (∀ form ∈ priors, 0 < form.eval point * form.eval nextPoint) →
      RawParserSemantics.Represented current.word nextPoint

/-- Any represented outcome in a strict inner refinement supplies a grid
base strictly inside the outer owner box. -/
def GridBase.ofStrictRefinement
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (next inner : WindingOneState p ambient)
    (strict : StrictInterior inner.box next.box)
    (outcome : CCLCoupledTrack.StableRepresentedOutcome
      current.word inner.box current.numerical.box) :
    GridBase current next where
  point := outcome.point
  strict :=
    ⟨strict.left.trans_le outcome.inside.1,
      outcome.inside.2.1.trans_lt strict.right,
      strict.bottom.trans_le outcome.inside.2.2.1,
      outcome.inside.2.2.2.trans_lt strict.top⟩
  nonzero := outcome.nonzero
  represented := outcome.semantics
  priors := outcome.priors
  priorsNonzero := outcome.priorsNonzero
  stable := by
    intro nextPoint inside preserved
    exact outcome.stable inside preserved

/-- Obtain the base directly from the coupled state's persistent sample in a
displayed strict refinement. -/
def gridBaseOfCurrentRefinement
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (next inner : WindingOneState p ambient)
    (nextRefinesCurrent : next.box.Refines current.numerical.box)
    (strict : StrictInterior inner.box next.box) : GridBase current next :=
  GridBase.ofStrictRefinement current next inner strict
    (current.sampleInRefinement inner
      (strict.refines.trans nextRefinesCurrent))

/-- All finite data needed after localization has made the selected active
residuals small enough. -/
structure EventGridData
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box) where
  base : QI
  baseStrict : next.box.StrictContains base
  baseNonzero : base ≠ 0
  baseRepresented : RawParserSemantics.Represented current.word base
  basePriors : List HermitianForm
  basePriorsNonzero : ∀ form ∈ basePriors, form.eval base ≠ 0
  baseStable : ∀ {nextPoint : QI},
    current.numerical.box.Contains nextPoint →
    (∀ form ∈ basePriors, 0 < form.eval base * form.eval nextPoint) →
      RawParserSemantics.Represented current.word nextPoint
  direction : TangentDirection
    (eventPayloadActiveForms current selected base) base
  selectedStrictAtBase :
    ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
    0 < eventPayloadCanonicalValue selected form * form.eval base
  selectedActiveResidual :
    ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
    |form.eval base| < approximateBoundaryBudget direction
      (eventPayloadPriorForms current selected basePriors base next.box)

structure GridData
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box) where
  base : QI
  baseStrict : next.box.StrictContains base
  baseNonzero : base ≠ 0
  baseRepresented : RawParserSemantics.Represented current.word base
  basePriors : List HermitianForm
  basePriorsNonzero : ∀ form ∈ basePriors, form.eval base ≠ 0
  baseStable : ∀ {nextPoint : QI},
    current.numerical.box.Contains nextPoint →
    (∀ form ∈ basePriors, 0 < form.eval base * form.eval nextPoint) →
      RawParserSemantics.Represented current.word nextPoint
  direction : TangentDirection
    (positiveEventActiveForms current selected base) base
  selectedStrictAtBase :
    ∀ form ∈ selectedIncrementalStrictPriorForms selected,
    0 < selectedEventCanonicalValue selected form * form.eval base
  selectedActiveResidual :
    ∀ form ∈ selectedIncrementalActiveOwnerForms selected,
    |form.eval base| < approximateBoundaryBudget direction
      (positiveEventPriorForms current selected basePriors base next.box)

abbrev GuardedGridData
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box) :=
  EventGridData current separation selected.toPayload.toIncrementalPayload next
    nextRefines

/-- One completely executable grid attempt at a fixed represented base.  The
direction table and both remaining event inequalities are finite rational
decisions; success carries all proofs needed by `GridData.sample`. -/
def gridData?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next) :
    Option (GridData current separation selected next nextRefines) :=
  match tangentDirectionCertificate?
      (positiveEventActiveForms current selected base.point) base.point with
  | none => none
  | some direction =>
      if strictCheck :
          ∀ form ∈ selectedIncrementalStrictPriorForms selected,
          0 < selectedEventCanonicalValue selected form * form.eval base.point
      then
        if residualCheck :
            ∀ form ∈ selectedIncrementalActiveOwnerForms selected,
            |form.eval base.point| < approximateBoundaryBudget direction
              (positiveEventPriorForms current selected base.priors base.point
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

/-- Extract the proof-bearing grid record from a successful executable
attempt.  The success proof is finite Boolean evidence, so no choice
principle is involved. -/
def gridDataOfIsSome
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next)
    (success : (gridData? current separation selected next nextRefines
      base).isSome) :
    GridData current separation selected next nextRefines :=
  (gridData? current separation selected next nextRefines base).get success

theorem gridData?_fields_of_eq_some
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next)
    {data : GridData current separation selected next nextRefines}
    (equality : gridData? current separation selected next nextRefines base =
      some data) :
    data.base = base.point ∧ data.basePriors = base.priors := by
  unfold gridData? at equality
  generalize directionEquality : tangentDirectionCertificate?
    (positiveEventActiveForms current selected base.point) base.point =
      directionOption at equality
  cases directionOption with
  | none => simp at equality
  | some direction =>
      simp only at equality
      by_cases strictCheck :
          ∀ form ∈ selectedIncrementalStrictPriorForms selected,
            0 < selectedEventCanonicalValue selected form *
              form.eval base.point
      · rw [dif_pos strictCheck] at equality
        by_cases residualCheck :
            ∀ form ∈ selectedIncrementalActiveOwnerForms selected,
              |form.eval base.point| < approximateBoundaryBudget direction
                (positiveEventPriorForms current selected base.priors
                  base.point next.box)
        · rw [dif_pos residualCheck] at equality
          simp only [Option.some.injEq] at equality
          subst data
          exact ⟨rfl, rfl⟩
        · rw [dif_neg residualCheck] at equality
          contradiction
      · rw [dif_neg strictCheck] at equality
        contradiction

theorem gridDataOfIsSome_base
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next)
    (success : (gridData? current separation selected next nextRefines
      base).isSome) :
    (gridDataOfIsSome current separation selected next nextRefines base
      success).base = base.point := by
  apply (gridData?_fields_of_eq_some current separation selected next
    nextRefines base ?_).1
  exact (Option.some_get success).symm

theorem gridDataOfIsSome_basePriors
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next)
    (success : (gridData? current separation selected next nextRefines
      base).isSome) :
    (gridDataOfIsSome current separation selected next nextRefines base
      success).basePriors = base.priors := by
  apply (gridData?_fields_of_eq_some current separation selected next
    nextRefines base ?_).2
  exact (Option.some_get success).symm

namespace GridData

theorem base_inverseDenominator
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    (adjugate (RawParser.parse current.word).matrix).c * data.base +
        (adjugate (RawParser.parse current.word).matrix).d ≠ 0 :=
  separation_denominator_ne separation
    (nextRefines.contains data.baseStrict.contains)

theorem currentFormula_holds_base
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    (inputStateFormula (RawParser.parse current.word)).Holds data.base := by
  rcases data.baseRepresented with ⟨tail, represents⟩
  apply inputStateFormula_holds_of_represents
    (RawParser.parse current.word) data.base tail
    (by simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word)
    data.base_inverseDenominator represents

theorem currentEvaluation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    formulaEvalWith (inputStateFormula (RawParser.parse current.word))
      (fun form => form.eval data.base) = true :=
  (formulaEvalWith_eval_eq_true_iff
    (inputStateFormula (RawParser.parse current.word)) data.base).2
      data.currentFormula_holds_base

theorem priors_nonzero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    ∀ form ∈ positiveEventPriorForms current selected data.basePriors
      data.base next.box,
      form.eval data.base ≠ 0 := by
  intro form member
  simp only [positiveEventPriorForms, List.mem_append,
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
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    ∀ form ∈ positiveEventActiveForms current selected data.base,
      |form.eval data.base| < approximateBoundaryBudget data.direction
        (positiveEventPriorForms current selected data.basePriors data.base
          next.box) := by
  intro form member
  exact data.selectedActiveResidual form member

def point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) : QI :=
  step data.base
    (multiOwnerEpsilon data.direction
      (positiveEventPriorForms current selected data.basePriors data.base
        next.box))
    data.direction.vector

theorem entered
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    ∀ form ∈ positiveEventActiveForms current selected data.base,
      0 < form.eval data.point := by
  simpa only [point] using
    (enters_all_boundaries_of_residual data.direction
      (positiveEventPriorForms current selected data.basePriors data.base
        next.box)
      data.priors_nonzero data.active_residual)

theorem preserved
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    ∀ form ∈ positiveEventPriorForms current selected data.basePriors
      data.base next.box,
      0 < form.eval data.base * form.eval data.point := by
  simpa only [point] using
    (preserves_all_priors data.direction
      (positiveEventPriorForms current selected data.basePriors data.base
        next.box)
      data.priors_nonzero)

theorem point_inside
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    next.box.Contains data.point := by
  change next.box.Contains (step data.base
    (multiOwnerEpsilon data.direction
      (positiveEventPriorForms current selected data.basePriors data.base
        next.box))
    data.direction.vector)
  apply multiOwner_step_mem_box_of_strict_priors data.direction
    data.priors_nonzero next.box
    (boxForms_pos_of_strictContains data.baseStrict)
  intro form member
  simp [positiveEventPriorForms, member]

theorem point_nonzero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    data.point ≠ 0 := by
  let normForm := affineNormForm 1 0
  have normMember : normForm ∈
      positiveEventPriorForms current selected data.basePriors data.base
        next.box := by
    simp [positiveEventPriorForms, normForm]
  have product := data.preserved normForm normMember
  have basePositive : 0 < normForm.eval data.base := by
    simpa [normForm, eval_affineNormForm] using normSq_pos data.baseNonzero
  have pointPositive : 0 < normForm.eval data.point := by
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
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    (inputStateFormula (RawParser.parse current.word)).Holds data.point := by
  have represented : RawParserSemantics.Represented current.word data.point := by
    apply data.baseStable
      ((nextRefines.trans separation.refines).contains data.point_inside)
    intro form member
    apply data.preserved form
    simp [positiveEventPriorForms, member]
  rcases represented with ⟨tail, represents⟩
  apply inputStateFormula_holds_of_represents
    (RawParser.parse current.word) data.point tail
    (by simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word)
    (separation_denominator_ne separation
      (nextRefines.contains data.point_inside)) represents

theorem point_represented
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    RawParserSemantics.Represented current.word data.point := by
  apply data.baseStable
    ((nextRefines.trans separation.refines).contains data.point_inside)
  intro form member
  apply data.preserved form
  simp [positiveEventPriorForms, member]

theorem selectedIncrementalFormula_holds_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    (inputIncrementalAdvanceFormula (RawParser.parse current.word)
      selected.bit).Holds data.point := by
  apply selectedIncrementalEvent_holds_of_owner_form_lists selected data.point
  · intro form member
    exact data.entered form member
  · intro form member
    apply mul_pos_trans (data.selectedStrictAtBase form member)
    apply data.preserved form
    simp [positiveEventPriorForms, member]

/-- Every selected strict face has its canonical orientation at the final
grid point, not only at the represented base. -/
theorem selectedStrictAtPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    ∀ form ∈ selectedIncrementalStrictPriorForms selected,
      0 < selectedEventCanonicalValue selected form * form.eval data.point := by
  intro form member
  apply mul_pos_trans (data.selectedStrictAtBase form member)
  apply data.preserved form
  simp [positiveEventPriorForms, member]

def sample
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines separation.state.box}
    (data : GridData current separation selected next nextRefines) :
    OwnerInputSample current selected.bit next separation.state.box where
  outcome :=
    { point := data.point
      inside := data.point_inside
      nonzero := data.point_nonzero
      semantics :=
        CCLBranchSampling.represented_append_of_inputIncrementalFormula
        current.word data.point selected.bit
        (separation_denominator_ne separation
          (nextRefines.contains data.point_inside))
        data.point_represented data.selectedIncrementalFormula_holds_point
      priors := data.basePriors ++
        selectedIncrementalActiveOwnerForms selected ++
        selectedIncrementalStrictPriorForms selected
      priorsNonzero := by
        intro form member
        simp only [List.mem_append] at member
        rcases member with (currentPrior | selectedActive) | selectedStrict
        · have product := data.preserved form (by
            simp [positiveEventPriorForms, currentPrior])
          intro zero
          have impossible : ¬(0 <
              form.eval data.base * form.eval data.point) := by
            simp [zero]
          exact impossible product
        · exact (data.entered form selectedActive).ne'
        · have positive := mul_pos_trans
            (data.selectedStrictAtBase form selectedStrict)
            (data.preserved form (by
              simp [positiveEventPriorForms, selectedStrict]))
          intro zero
          have impossible : ¬(0 < selectedEventCanonicalValue selected form *
              form.eval data.point) := by
            simp [zero]
          exact impossible positive
      stable := by
        intro point inside preserved
        have oldRepresented :
            RawParserSemantics.Represented current.word point := by
          apply data.baseStable (separation.refines.contains inside)
          intro form member
          apply mul_pos_trans
            (data.preserved form (by
              simp [positiveEventPriorForms, member]))
          exact preserved form (by simp [member])
        have selectedHolds :
            (inputIncrementalAdvanceFormula (RawParser.parse current.word)
              selected.bit).Holds point := by
          apply selectedIncrementalEvent_holds_of_owner_form_lists selected
            point
          · intro form member
            have atGrid := data.entered form member
            have sameSign := preserved form (by simp [member])
            rcases mul_pos_iff.mp sameSign with signs | signs
            · exact signs.2
            · exact (not_lt_of_ge atGrid.le signs.1).elim
          · intro form member
            apply mul_pos_trans
              (mul_pos_trans (data.selectedStrictAtBase form member)
                (data.preserved form (by
                  simp [positiveEventPriorForms, member])))
            exact preserved form (by simp [member])
        exact CCLBranchSampling.represented_append_of_inputIncrementalFormula
          current.word point selected.bit
          (separation_denominator_ne separation
            inside)
          oldRepresented selectedHolds }

end GridData

/-- A successful owner-grid record in every later winding box, with its base
priors identified with the coupled state's fixed list and oriented relative
to the state's anchor sample.  These are exactly the coherence obligations
left after the local grid construction has proved its geometric fields. -/
structure PersistentGridDataFamily
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation) where
  data : (next : WindingOneState p ambient) →
    (nextRefines : next.box.Refines separation.state.box) →
      GridData current separation selected next nextRefines
  basePriors : ∀ next nextRefines,
    (data next nextRefines).basePriors = current.priors
  baseSameSigns : ∀ next nextRefines form, form ∈ current.priors →
    0 < form.eval current.sample *
      form.eval (data next nextRefines).base

/-- Coherent successful grid data automatically supplies the persistent owner
sampler required by the coupled controller. -/
def PersistentGridDataFamily.ownerSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    (family : PersistentGridDataFamily current separation selected) :
    PersistentOwnerSamples current separation selected where
  sample next nextRefines := (family.data next nextRefines).sample
  sample_priors := by
    intro next nextRefines
    have anchorPriors := family.basePriors separation.state
      (RatBox.refines_refl separation.state.box)
    have nextPriors := family.basePriors next nextRefines
    change (family.data next nextRefines).basePriors ++
        selectedIncrementalActiveOwnerForms selected ++
          selectedIncrementalStrictPriorForms selected =
      (family.data separation.state
        (RatBox.refines_refl separation.state.box)).basePriors ++
          selectedIncrementalActiveOwnerForms selected ++
            selectedIncrementalStrictPriorForms selected
    rw [nextPriors, anchorPriors]
  sample_sameSigns := by
    intro next nextRefines form member
    let anchor := family.data separation.state
      (RatBox.refines_refl separation.state.box)
    let later := family.data next nextRefines
    change form ∈ anchor.basePriors ++
      selectedIncrementalActiveOwnerForms selected ++
        selectedIncrementalStrictPriorForms selected at member
    change 0 < form.eval anchor.point * form.eval later.point
    simp only [List.mem_append] at member
    rcases member with (old | active) | strict
    · have oldCurrent : form ∈ current.priors := by
        rw [← family.basePriors separation.state
          (RatBox.refines_refl separation.state.box)]
        exact old
      have anchorPreserved := anchor.preserved form (by
        simp [positiveEventPriorForms, old])
      have baseToBase := CCLCoupledTrack.sameSign_of_common_anchor
        (family.baseSameSigns separation.state
          (RatBox.refines_refl separation.state.box) form oldCurrent)
        (family.baseSameSigns next nextRefines form oldCurrent)
      have laterOld : form ∈ later.basePriors := by
        rw [family.basePriors next nextRefines]
        exact oldCurrent
      have laterPreserved := later.preserved form (by
        simp [positiveEventPriorForms, laterOld])
      have anchorPointToBase :
          0 < form.eval anchor.point * form.eval anchor.base := by
        rw [_root_.mul_comm]
        exact anchorPreserved
      apply mul_pos_trans
      · apply mul_pos_trans
        · exact anchorPointToBase
        · exact baseToBase
      · exact laterPreserved
    · exact mul_pos (anchor.entered form active) (later.entered form active)
    · exact CCLCoupledTrack.sameSign_of_common_anchor
        (anchor.selectedStrictAtPoint form strict)
        (later.selectedStrictAtPoint form strict)

def gridSample?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (base : GridBase current next) :
    Option (OwnerInputSample current selected.bit next separation.state.box) :=
  (gridData? current separation selected next nextRefines base).map
    fun data => data.sample

/-- One finite grid attempt after a caller-selected positive inner refinement
width.  Repeating this function over an explicitly bounded width schedule is
the final search layer of the persistent event sampler. -/
def gridSampleAtWidth?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
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
  gridSample? current separation selected next nextRefines base

end CCLPositiveEventGrid
end FTA
