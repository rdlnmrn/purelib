import FTA.CCLDirectTrack
import FTA.CCLRawCylinderEnvelope
import FTA.CCLBranchSampling

/-!
# Whole-box CCL cylinder checkpoints

The direct x--y controller and the metric contraction argument do not need a
rational point that survives every later winding box.  At a descent
checkpoint it is enough to certify that every rational point of the retained
box realizes the current raw word.  The rational box center then supplies the
temporary box--cylinder coupling used by the chordal estimate.

Numerical refinement at a fixed word preserves this whole-box certificate.
Appending a bit deliberately asks for a new certificate: this is the exact
remaining interface to the x--y Sturm descent, rather than a hidden persistent
sample assumption.
-/

namespace FTA
namespace CCLBoxCylinderCheckpoint

open CCL
open FTA.CCLChordalEnvelope
open FTA.CCLBranchEvidence
open FTA.CCLDirectTrack
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLRawCylinderEnvelope
open FTA.CCLStrictChildSemantics
open FTA.CCLTerminalSeparation
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- A raw CCL cylinder wraps a rational box when every rational point of the
box has affine raw-parser semantics for the cylinder word. -/
def Wraps (word : Prefix.Word) (box : RatBox) : Prop :=
  ∀ {point : QI}, box.Contains point →
    RawParserSemantics.Represented word point

/-- A sample-free direct controller state at a whole-box cylinder checkpoint.
The metric envelope and winding box are independent; `wraps` couples them only
through a universal finite-word statement. -/
structure State (p : GaussianPolynomial) (ambient : RatBox) where
  core : CCLDirectTrack.State p ambient
  cylinder : RawCylinderEnvelope
  cylinder_word : cylinder.truncation.word = core.word
  wraps : Wraps core.word core.numerical.box

namespace State

/-- Every nested winding box of a wrapped checkpoint contains an explicit
nonzero represented point.  The point is used only to adapt the universal
whole-box invariant to older geometric APIs; no witness is retained by the
checkpoint itself. -/
def wrappedOutcome
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines state.core.numerical.box) :
    CCLCoupledTrack.StableRepresentedOutcome state.core.word numerical.box
      state.core.numerical.box := by
  by_cases centerZero : numerical.box.center = 0
  · let point : QI := ⟨numerical.box.xLower, numerical.box.center.im⟩
    have centerRe :
        (numerical.box.xLower + numerical.box.xUpper) / 2 = 0 := by
      have equality := congrArg CCL.GaussianRat.re centerZero
      simpa only [RatBox.center_re, CCL.GaussianRat.zero_re] using equality
    have leftNegative : numerical.box.xLower < 0 := by
      linarith [numerical.proper.1]
    have inside : numerical.box.Contains point := by
      refine ⟨le_rfl, numerical.box.x_valid, ?_, ?_⟩
      · exact numerical.box.contains_center.2.2.1
      · exact numerical.box.contains_center.2.2.2
    have nonzero : point ≠ 0 := by
      intro equality
      have realEquality := congrArg CCL.GaussianRat.re equality
      simp only [point, CCL.GaussianRat.zero_re] at realEquality
      linarith
    exact
      { point := point
        inside := inside
        nonzero := nonzero
        semantics := state.wraps (refines.contains inside)
        priors := []
        priorsNonzero := by simp
        stable := by
          intro nextPoint nextInside _preserved
          exact state.wraps nextInside }
  · exact
      { point := numerical.box.center
        inside := numerical.box.contains_center
        nonzero := centerZero
        semantics := state.wraps
          (refines.contains numerical.box.contains_center)
        priors := []
        priorsNonzero := by simp
        stable := by
          intro nextPoint nextInside _preserved
          exact state.wraps nextInside }

/-- A wrapped checkpoint can be viewed by the legacy event-grid machinery as
a coupled state with an empty historical sign list.  Universal wrapping
supplies every re-anchored sample directly, so this adapter does not weaken
the sample-free checkpoint invariant. -/
def asCoupled
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) : CCLCoupledTrack.State p ambient := by
  let sample := state.wrappedOutcome state.core.numerical
    (RatBox.refines_refl state.core.numerical.box)
  exact
    { numerical := state.core.numerical
      word := state.core.word
      sample := sample.point
      sampleInside := sample.inside
      sampleNonzero := sample.nonzero
      sampleRepresented := sample.semantics
      priors := []
      samplePriorsNonzero := by simp
      sampleInRefinement := fun next nextRefines =>
        state.wrappedOutcome next nextRefines
      sampleInRefinement_priors := by
        intro next nextRefines
        unfold wrappedOutcome
        split <;> rfl
      sampleInRefinement_sameSigns := by simp }

/-- The box center is a represented point because wrapping is a whole-box
certificate, not because a sample was retained from an earlier state. -/
theorem center_represented
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) :
    RawParserSemantics.Represented state.core.word
      state.core.numerical.box.center :=
  state.wraps state.core.numerical.box.contains_center

/-- Temporary coupling data manufactured at the checkpoint from the rational
center. -/
def coupling
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) : BoxCylinderCoupling where
  box := state.core.numerical.box
  cylinder := state.cylinder
  witness := state.core.numerical.box.center
  witnessInside := state.core.numerical.box.contains_center
  witnessRepresented := by
    rw [state.cylinder_word]
    exact state.center_represented

/-- Sum of the independently shrinking numerical and raw-cylinder terms. -/
def componentError
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) : ℚ :=
  state.core.numerical.box.diagonalSq + state.cylinder.radiusSq

theorem coupling_errorSq_eq_two_componentError
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) :
    state.coupling.errorSq = 2 * state.componentError := rfl

/-- Independent numerical/cylinder refinement. -/
def Refines
    {p : GaussianPolynomial} {ambient : RatBox}
    (new old : State p ambient) : Prop :=
  new.core.numerical.box.Refines old.core.numerical.box ∧
    new.cylinder.Refines old.cylinder

theorem refines_refl
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) : state.Refines state :=
  ⟨RatBox.refines_refl _, RawCylinderEnvelope.refines_refl _⟩

theorem Refines.trans
    {p : GaussianPolynomial} {ambient : RatBox}
    {new middle old : State p ambient}
    (newMiddle : new.Refines middle) (middleOld : middle.Refines old) :
    new.Refines old :=
  ⟨newMiddle.1.trans middleOld.1, newMiddle.2.trans middleOld.2⟩

theorem Refines.componentError_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {new old : State p ambient} (refines : new.Refines old) :
    new.componentError ≤ old.componentError := by
  have diagonal :=
    CCLClearanceExclusion.RatBox.diagonalSq_le_of_refines refines.1
  exact add_le_add diagonal refines.2.2

/-- Terminal separation supplies existence of a next child at every point of
a wrapped box.  Wrapping supplies current raw semantics at that particular
point; no point is selected globally or retained in the result. -/
theorem exists_inputAdvance_of_wrapped
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (terminal : CCLTerminalSeparation.SeparationOutput p ambient
      (RawParser.parse current.core.word) separation.state [false, true])
    (input : QI) (inside : terminal.numerical.box.Contains input) :
    ∃ bit, (inputAdvanceFormula
      (RawParser.parse current.core.word) bit).Holds input := by
  let parser := RawParser.parse current.core.word
  have oldInside : current.core.numerical.box.Contains input :=
    separation.refines.contains (terminal.refines.contains inside)
  have represented : RawParserSemantics.Represented current.core.word input :=
    current.wraps oldInside
  have determinantNonzero : determinant parser.matrix ≠ 0 := by
    simpa only [parser, determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have inverseDenominator :
      (adjugate parser.matrix).c * input +
        (adjugate parser.matrix).d ≠ 0 :=
    separation_denominator_ne separation (terminal.refines.contains inside)
  have currentHolds : parser.Holds
      (RatBox.homographic (adjugate parser.matrix) input) := by
    rcases represented with ⟨tail, represents⟩
    rw [CCLBranchSampling.inverse_tail_eq_of_represents parser input tail
      determinantNonzero inverseDenominator represents]
    exact represents.2.2
  by_cases falseHolds :
      (inputAdvanceFormula parser false).Holds input
  · exact ⟨false, falseHolds⟩
  · by_cases trueHolds :
        (inputAdvanceFormula parser true).Holds input
    · exact ⟨true, trueHolds⟩
    · have none : ∀ bit,
          ¬(inputAdvanceFormula parser bit).Holds input := by
        intro bit
        cases bit
        · exact falseHolds
        · exact trueHolds
      exact ((terminal.excludes_no_children input determinantNonzero
        inverseDenominator currentHolds none) inside).elim

/-- The strict-cell Boolean extends the whole wrapped box.  Child existence
comes pointwise from terminal separation, while `StrictCellDecision` forces
all of those children to carry its center-computed bit. -/
theorem wraps_append_of_strictCell
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (terminal : CCLTerminalSeparation.SeparationOutput p ambient
      (RawParser.parse current.core.word) separation.state [false, true])
    (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines terminal.numerical.box)
    (decision : StrictCellDecision
      (RawParser.parse current.core.word) numerical.box) :
    Wraps (current.core.word ++ [decision.bit]) numerical.box := by
  intro input inside
  have terminalInside : terminal.numerical.box.Contains input :=
    refines.contains inside
  rcases exists_inputAdvance_of_wrapped current separation terminal input
      terminalInside with ⟨other, otherHolds⟩
  have separationInside : separation.state.box.Contains input :=
    terminal.refines.contains terminalInside
  have inverseDenominator :
      (adjugate (RawParser.parse current.core.word).matrix).c * input +
        (adjugate (RawParser.parse current.core.word).matrix).d ≠ 0 :=
    separation_denominator_ne separation separationInside
  have bitEq : other = decision.bit :=
    decision.selects inside inverseDenominator otherHolds
  subst other
  apply CCLBranchSampling.represented_append_of_inputFormula
    current.core.word input decision.bit inverseDenominator
  · exact current.wraps
      (separation.refines.contains separationInside)
  · exact otherHolds

/-- The concrete all-clear plan already packages the pointwise semantic
extension proved from terminal separation and strict-cell uniqueness.
Consequently a wrapped checkpoint yields a wrapped appended word directly,
without exposing or choosing any of those pointwise witnesses. -/
theorem wraps_append_of_plannedBit
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (planned : CCLDirectTrack.PlannedBit current.core) :
    Wraps (current.core.word ++ [planned.decision.bit])
      planned.numerical.box := by
  intro input inside
  exact planned.representedAppend inside
    (current.wraps (planned.refines.contains inside))

/-- Uniform truth of the genuinely new child predicate extends a wrapped
checkpoint throughout the retained numerical box.  The represented old word
supplies all historical parser constraints pointwise, so the premise contains
only the next bit's incremental formula. -/
theorem wraps_append_of_incrementalFormula
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines separation.state.box)
    (bit : Bool)
    (selected : ∀ {input : QI}, numerical.box.Contains input →
      (inputIncrementalAdvanceFormula
        (RawParser.parse current.core.word) bit).Holds input) :
    Wraps (current.core.word ++ [bit]) numerical.box := by
  intro input inside
  have separationInside : separation.state.box.Contains input :=
    refines.contains inside
  exact CCLBranchSampling.represented_append_of_inputIncrementalFormula
    current.core.word input bit
    (separation_denominator_ne separation separationInside)
    (current.wraps (separation.refines.contains separationInside))
    (selected inside)

/-- Equip a direct state with the universal unit cylinder at a checkpoint
where the x--y descent has established whole-box wrapping. -/
def ofDirect
    {p : GaussianPolynomial} {ambient : RatBox}
    (core : CCLDirectTrack.State p ambient)
    (wraps : Wraps core.word core.numerical.box) : State p ambient where
  core := core
  cylinder := RawCylinderEnvelope.unit ⟨core.word⟩
  cylinder_word := rfl
  wraps := wraps

/-- Shrinking the winding box at a fixed word preserves whole-box wrapping
by restriction.  The cylinder is left untouched. -/
def refineBox
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines state.core.numerical.box) :
    State p ambient where
  core := state.core.refine numerical refines
  cylinder := state.cylinder
  cylinder_word := state.cylinder_word
  wraps := by
    intro point inside
    exact state.wraps (refines.contains inside)

theorem refineBox_refines
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines state.core.numerical.box) :
    (state.refineBox numerical refines).Refines state :=
  ⟨refines, RawCylinderEnvelope.refines_refl _⟩

/-- Replace the metric envelope at the same direct state. -/
def replaceCylinder
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (cylinder : RawCylinderEnvelope)
    (word : cylinder.truncation.word = state.core.word) : State p ambient where
  core := state.core
  cylinder := cylinder
  cylinder_word := word
  wraps := state.wraps

theorem replaceCylinder_refines
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (cylinder : RawCylinderEnvelope)
    (word : cylinder.truncation.word = state.core.word)
    (smaller : cylinder.radiusSq ≤ state.cylinder.radiusSq) :
    (state.replaceCylinder cylinder word).Refines state := by
  refine ⟨RatBox.refines_refl _, ?_⟩
  constructor
  · change state.cylinder.truncation.word <+: cylinder.truncation.word
    rw [state.cylinder_word, word]
  · exact smaller

/-- Install one appended direct bit.  Restricting the old envelope is
automatic; the caller supplies exactly the new whole-box wrapping theorem
produced by the descent. -/
def next
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (bit : Bool)
    (core : CCLDirectTrack.State p ambient)
    (wordEq : core.word = current.core.word ++ [bit])
    (wraps : Wraps core.word core.numerical.box) : State p ambient := by
  let truncation : TaggedTruncation := ⟨core.word⟩
  have isPrefix : List.IsPrefix current.cylinder.truncation.word
      truncation.word := by
    change List.IsPrefix current.cylinder.truncation.word core.word
    rw [current.cylinder_word, wordEq]
    exact List.prefix_append _ _
  exact
    { core := core
      cylinder := current.cylinder.restrict truncation isPrefix
      cylinder_word := rfl
      wraps := wraps }

theorem next_refines
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (bit : Bool)
    (core : CCLDirectTrack.State p ambient)
    (coreRefines : core.numerical.box.Refines current.core.numerical.box)
    (wordEq : core.word = current.core.word ++ [bit])
    (wraps : Wraps core.word core.numerical.box) :
    (current.next bit core wordEq wraps).Refines current := by
  unfold next Refines
  dsimp only
  exact ⟨coreRefines, RawCylinderEnvelope.restrict_refines _ _ _⟩

/-- Install an appended direct bit as soon as the x--y descent has produced a
nested box on which the selected incremental predicate is uniform.  This is
the concrete checkpoint transition shared by strict-cell and event-grid
branches. -/
def nextOfIncrementalFormula
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines separation.state.box)
    (bit : Bool)
    (selected : ∀ {input : QI}, numerical.box.Contains input →
      (inputIncrementalAdvanceFormula
        (RawParser.parse current.core.word) bit).Holds input) :
    State p ambient :=
  let core : CCLDirectTrack.State p ambient :=
    { numerical := numerical
      word := current.core.word ++ [bit] }
  State.next (current := current) (bit := bit) (core := core) (by rfl) (by
    change Wraps (current.core.word ++ [bit]) numerical.box
    exact wraps_append_of_incrementalFormula current separation numerical
      refines bit selected)

theorem nextOfIncrementalFormula_refines
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines separation.state.box)
    (bit : Bool)
    (selected : ∀ {input : QI}, numerical.box.Contains input →
      (inputIncrementalAdvanceFormula
        (RawParser.parse current.core.word) bit).Holds input) :
    (State.nextOfIncrementalFormula (current := current) separation numerical
      refines bit selected).Refines current := by
  let core : CCLDirectTrack.State p ambient :=
    { numerical := numerical
      word := current.core.word ++ [bit] }
  let wraps : Wraps core.word core.numerical.box := by
    change Wraps (current.core.word ++ [bit]) numerical.box
    exact wraps_append_of_incrementalFormula current separation numerical
      refines bit selected
  change (State.next current bit core (by rfl) wraps).Refines current
  exact next_refines current bit core (refines.trans separation.refines)
    (by rfl) wraps

end State

/-- Once the two independently shrinking component sums fit below the stored
coordinate gap, no rational realizations of the two wrapped raw cylinders can
denote the same projective point. -/
theorem represented_points_not_equivalent_of_component_error_lt_gap
    {p : GaussianPolynomial} {ambient : RatBox}
    {left right : State p ambient} {coordinateGap : ℚ}
    (gapPositive : 0 < coordinateGap)
    (coordinateSeparated :
      left.core.numerical.box.xUpper + coordinateGap ≤
          right.core.numerical.box.xLower ∨
      right.core.numerical.box.xUpper + coordinateGap ≤
          left.core.numerical.box.xLower ∨
      left.core.numerical.box.yUpper + coordinateGap ≤
          right.core.numerical.box.yLower ∨
      right.core.numerical.box.yUpper + coordinateGap ≤
          left.core.numerical.box.yLower)
    (thin : 8 * (left.componentError + right.componentError) <
      CCLChordalEnvelope.chordalGapSq left.core.numerical.box
        right.core.numerical.box coordinateGap)
    {leftPoint rightPoint : QI}
    (leftRepresented : RawParserSemantics.Represented
      left.core.word leftPoint)
    (rightRepresented : RawParserSemantics.Represented
      right.core.word rightPoint) :
    ¬(Proj.affine leftPoint).Equivalent (Proj.affine rightPoint) := by
  have coupledThin :
      4 * (left.coupling.errorSq + right.coupling.errorSq) <
        CCLChordalEnvelope.chordalGapSq left.core.numerical.box
          right.core.numerical.box coordinateGap := by
    rw [left.coupling_errorSq_eq_two_componentError,
      right.coupling_errorSq_eq_two_componentError]
    convert thin using 1
    ring
  apply
    CCLRawCylinderEnvelope.represented_points_not_equivalent_of_error_sum_lt_gap
      gapPositive coordinateSeparated rfl rfl coupledThin
  · change RawParserSemantics.Represented
      left.cylinder.truncation.word leftPoint
    rw [left.cylinder_word]
    exact leftRepresented
  · change RawParserSemantics.Represented
      right.cylinder.truncation.word rightPoint
    rw [right.cylinder_word]
    exact rightRepresented

end CCLBoxCylinderCheckpoint
end FTA
