import FTA.CCLCoupledTrack
import FTA.CCLHomographicCylinder

/-!
# Coupled winding, CCL, and chordal-envelope states

This module installs the revised metric invariant on the existing persistent
CCL controller.  The winding box and raw cylinder remain independent finite
certificates.  Their shared represented rational witness produces the exact
box--cylinder coupling, while numerical refinements preserve the cylinder and
each decided bit restricts it constructively.  A later sharper diameter
certificate can replace the inherited one without changing the root track.
-/

namespace FTA
namespace CCLMetricTrack

open CCL
open FTA.CCLChordalEnvelope
open FTA.CCLRawCylinderEnvelope
open FTA.CCLHomographicCylinder

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Executable precomputed coordinate separation between two root regions.
Unlike a proposition-only existential, the rational gap remains an explicit
field available to later finite error comparisons. -/
structure RegionGap (left right : RatBox) where
  coordinateGap : ℚ
  positive : 0 < coordinateGap
  separated :
    left.xUpper + coordinateGap ≤ right.xLower ∨
    right.xUpper + coordinateGap ≤ left.xLower ∨
    left.yUpper + coordinateGap ≤ right.yLower ∨
    right.yUpper + coordinateGap ≤ left.yLower

namespace RegionGap

/-- Deterministically inspect the four possible coordinate separations and
retain half of the first positive gap found. -/
def compute? (left right : RatBox) : Option (RegionGap left right) := by
  if separated : left.xUpper < right.xLower then
    let gap := (right.xLower - left.xUpper) / 2
    exact some
      { coordinateGap := gap
        positive := by dsimp only [gap]; linarith
        separated := Or.inl (by dsimp only [gap]; linarith) }
  else if separated : right.xUpper < left.xLower then
    let gap := (left.xLower - right.xUpper) / 2
    exact some
      { coordinateGap := gap
        positive := by dsimp only [gap]; linarith
        separated := Or.inr (Or.inl (by dsimp only [gap]; linarith)) }
  else if separated : left.yUpper < right.yLower then
    let gap := (right.yLower - left.yUpper) / 2
    exact some
      { coordinateGap := gap
        positive := by dsimp only [gap]; linarith
        separated := Or.inr (Or.inr
          (Or.inl (by dsimp only [gap]; linarith))) }
  else if separated : right.yUpper < left.yLower then
    let gap := (left.yLower - right.yUpper) / 2
    exact some
      { coordinateGap := gap
        positive := by dsimp only [gap]; linarith
        separated := Or.inr (Or.inr
          (Or.inr (by dsimp only [gap]; linarith))) }
  else
    exact none

theorem compute?_isSome_of_separated {left right : RatBox}
    (separated : left.Separated right) : (compute? left right).isSome := by
  rcases separated with ⟨gap, gapPositive, coordinateSeparated⟩
  unfold compute?
  split
  · simp
  · rename_i notFirst
    split
    · simp
    · rename_i notSecond
      split
      · simp
      · rename_i notThird
        split
        · simp
        · rename_i notFourth
          rcases coordinateSeparated with
            first | second | third | fourth
          · linarith
          · linarith
          · linarith
          · linarith

/-- Total stored rational gap obtained from the proposition-level separation
proof only after the executable comparison has materialized its data. -/
def compute (left right : RatBox) (separated : left.Separated right) :
    RegionGap left right :=
  (compute? left right).get (compute?_isSome_of_separated separated)

/-- The same stored rational gap remains valid in nested root boxes. -/
def refine {left right newLeft newRight : RatBox}
    (gap : RegionGap left right) (leftRefines : newLeft.Refines left)
    (rightRefines : newRight.Refines right) : RegionGap newLeft newRight where
  coordinateGap := gap.coordinateGap
  positive := gap.positive
  separated := by
    rcases leftRefines with
      ⟨leftLower, leftUpper, leftYLower, leftYUpper⟩
    rcases rightRefines with
      ⟨rightLower, rightUpper, rightYLower, rightYUpper⟩
    rcases gap.separated with separated | separated | separated | separated
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))

end RegionGap

/-- The persistent winding/CCL state equipped with a diameter certificate for
exactly its current raw word. -/
structure State (p : GaussianPolynomial) (ambient : RatBox) where
  core : CCLCoupledTrack.PersistentState p ambient
  cylinder : RawCylinderEnvelope
  cylinder_word : cylinder.truncation.word = core.word

namespace State

/-- The current represented witness, valid for both open-cell and constrained
boundary persistence modes. -/
def outcome {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) :
    CCLCompatibleCandidates.RepresentedOutcome state.core.word
      state.core.numerical.box :=
  state.core.outcome

/-- The metric invariant's finite coupling object. -/
def coupling {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) : BoxCylinderCoupling where
  box := state.core.numerical.box
  cylinder := state.cylinder
  witness := state.outcome.point
  witnessInside := state.outcome.inside
  witnessRepresented := by
    rw [state.cylinder_word]
    exact state.outcome.semantics

/-- Sum of the independently controlled box and cylinder components before
the square-root-free triangle factor is applied. -/
def componentError {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) : ℚ :=
  state.core.numerical.box.diagonalSq + state.cylinder.radiusSq

theorem coupling_errorSq_eq_two_componentError
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) :
    state.coupling.errorSq = 2 * state.componentError := by
  rfl

/-- Equip any persistent controller state with the universal unit envelope.
Subsequent certified contraction replaces this coarse initial radius. -/
def ofCore {p : GaussianPolynomial} {ambient : RatBox}
    (core : CCLCoupledTrack.PersistentState p ambient) : State p ambient where
  core := core
  cylinder := RawCylinderEnvelope.unit ⟨core.word⟩
  cylinder_word := rfl

/-- Simultaneous refinement of the independent numerical and cylinder
components. -/
def Refines {p : GaussianPolynomial} {ambient : RatBox}
    (new old : State p ambient) : Prop :=
  new.core.numerical.box.Refines old.core.numerical.box ∧
    new.cylinder.Refines old.cylinder

theorem refines_refl {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) : state.Refines state := by
  exact ⟨RatBox.refines_refl _, RawCylinderEnvelope.refines_refl _⟩

theorem Refines.trans {p : GaussianPolynomial} {ambient : RatBox}
    {new middle old : State p ambient}
    (newMiddle : new.Refines middle) (middleOld : middle.Refines old) :
    new.Refines old := by
  exact ⟨newMiddle.1.trans middleOld.1,
    newMiddle.2.trans middleOld.2⟩

theorem Refines.word_prefix {p : GaussianPolynomial} {ambient : RatBox}
    {new old : State p ambient} (refines : new.Refines old) :
    old.core.word <+: new.core.word := by
  have isPrefix := refines.2.1
  rw [old.cylinder_word, new.cylinder_word] at isPrefix
  exact isPrefix

theorem Refines.cylinderRadiusSq_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {new old : State p ambient} (refines : new.Refines old) :
    new.cylinder.radiusSq ≤ old.cylinder.radiusSq :=
  refines.2.2

/-- Replace the cylinder certificate at the same symbolic state. -/
def replaceCylinder {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (cylinder : RawCylinderEnvelope)
    (word : cylinder.truncation.word = state.core.word) : State p ambient where
  core := state.core
  cylinder := cylinder
  cylinder_word := word

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

theorem replaceCylinder_coupling_error_le
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (cylinder : RawCylinderEnvelope)
    (word : cylinder.truncation.word = state.core.word) {radius : ℚ}
    (radiusBound : cylinder.radiusSq ≤ radius) :
    (state.replaceCylinder cylinder word).coupling.errorSq ≤
      2 * (state.core.numerical.box.diagonalSq + radius) := by
  exact BoxCylinderCoupling.errorSq_le le_rfl radiusBound

/-- A sharper cylinder for the same controller word, certified against one
requested rational squared diameter. -/
structure CylinderContraction {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ) where
  cylinder : RawCylinderEnvelope
  cylinder_word : cylinder.truncation.word = state.core.word
  radiusSq_le : cylinder.radiusSq ≤ epsilon

/-- A contracted successor that also retains monotonicity against the current
metric state. -/
structure ContractionResult {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ) where
  contracted : State p ambient
  refines : contracted.Refines state
  radiusSq_le : contracted.cylinder.radiusSq ≤ epsilon
  word_eq : contracted.core.word = state.core.word

/-- Install a same-word contraction certificate without modifying the winding
box, represented witness, or symbolic persistence data. -/
def installContraction {p : GaussianPolynomial} {ambient : RatBox}
    {state : State p ambient} {epsilon : ℚ}
    (certificate : CylinderContraction state epsilon) : State p ambient :=
  state.replaceCylinder certificate.cylinder certificate.cylinder_word

theorem installContraction_radiusSq_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : State p ambient} {epsilon : ℚ}
    (certificate : CylinderContraction state epsilon) :
    (state.installContraction certificate).cylinder.radiusSq ≤ epsilon :=
  certificate.radiusSq_le

theorem installContraction_refines
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : State p ambient} {epsilon : ℚ}
    (certificate : CylinderContraction state epsilon)
    (budget : epsilon ≤ state.cylinder.radiusSq) :
    (state.installContraction certificate).Refines state := by
  exact state.replaceCylinder_refines certificate.cylinder
    certificate.cylinder_word (certificate.radiusSq_le.trans budget)

theorem installContraction_coupling_error_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : State p ambient} {epsilon : ℚ}
    (certificate : CylinderContraction state epsilon) :
    (state.installContraction certificate).coupling.errorSq ≤
      2 * (state.core.numerical.box.diagonalSq + epsilon) := by
  exact state.replaceCylinder_coupling_error_le certificate.cylinder
    certificate.cylinder_word certificate.radiusSq_le

/-- Install a supplied contraction only when it improves the old radius; if
the old certificate already meets the request, retain it unchanged. -/
def contractWith {p : GaussianPolynomial} {ambient : RatBox}
    {state : State p ambient} {epsilon : ℚ}
    (certificate : CylinderContraction state epsilon) :
    ContractionResult state epsilon := by
  if already : state.cylinder.radiusSq ≤ epsilon then
    exact
      { contracted := state
        refines := state.refines_refl
        radiusSq_le := already
        word_eq := rfl }
  else
    have epsilonLtOld : epsilon < state.cylinder.radiusSq :=
      lt_of_not_ge already
    exact
      { contracted := state.installContraction certificate
        refines := installContraction_refines certificate epsilonLtOld.le
        radiusSq_le := installContraction_radiusSq_le certificate
        word_eq := rfl }

/-- Executable contraction attempt from the parser phase alone.  It first
accepts an already-small inherited radius; otherwise it asks the homographic
phase checker for a sharper envelope and installs it exactly when that
candidate meets the request. -/
def automaticContraction? {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ) :
    Option (ContractionResult state epsilon) := by
  if already : state.cylinder.radiusSq ≤ epsilon then
    exact some
      { contracted := state
        refines := state.refines_refl
        radiusSq_le := already
        word_eq := rfl }
  else
    match found : automaticEnvelope? state.core.word with
    | none => exact none
    | some cylinder =>
        if candidate : cylinder.radiusSq ≤ epsilon then
          have epsilonLtOld : epsilon < state.cylinder.radiusSq :=
            lt_of_not_ge already
          let next := state.replaceCylinder cylinder
            (automaticEnvelope?_word found)
          exact some
            { contracted := next
              refines := state.replaceCylinder_refines cylinder
                (automaticEnvelope?_word found)
                (candidate.trans epsilonLtOld.le)
              radiusSq_le := candidate
              word_eq := rfl }
        else
          exact none

theorem automaticContraction?_isSome_of_radiusSq_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : State p ambient} {epsilon : ℚ}
    (small : state.cylinder.radiusSq ≤ epsilon) :
    (state.automaticContraction? epsilon).isSome := by
  unfold automaticContraction?
  rw [dif_pos small]
  rfl

/-- Build the installable certificate when a loop-unary phase has reached the
decoder-specific computed exponent. -/
def loopUnaryContraction {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse state.core.word).phase = .loopUnary
      (decoderUnaryDepth (RawParser.parse state.core.word).matrix epsilon)) :
    CylinderContraction state epsilon where
  cylinder := loopUnaryContractedEnvelope state.core.word epsilon
    epsilonPositive phase
  cylinder_word := rfl
  radiusSq_le := loopUnaryContractedEnvelope_radiusSq_le state.core.word
    epsilonPositive phase

/-- Initial-high unary contraction in installable controller form. -/
def highUnaryContraction {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse state.core.word).phase = .highUnary
      (decoderUnaryDepth (RawParser.parse state.core.word).matrix epsilon)) :
    CylinderContraction state epsilon where
  cylinder := highUnaryContractedEnvelope state.core.word epsilon
    epsilonPositive phase
  cylinder_word := rfl
  radiusSq_le := highUnaryContractedEnvelope_radiusSq_le state.core.word
    epsilonPositive phase

/-- Loop-sector contraction retained through any partial sector-bit code. -/
def loopSectorContraction {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (bits : RawParser.SectorBits)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse state.core.word).phase = .sector .loop
      (decoderUnaryDepth (RawParser.parse state.core.word).matrix epsilon)
        bits) : CylinderContraction state epsilon where
  cylinder := loopSectorContractedEnvelope state.core.word bits epsilon
    epsilonPositive phase
  cylinder_word := rfl
  radiusSq_le := loopSectorContractedEnvelope_radiusSq_le state.core.word bits
    epsilonPositive phase

/-- Initial-high sector contraction retained through any partial code. -/
def highSectorContraction {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (bits : RawParser.SectorBits)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse state.core.word).phase = .sector .initialHigh
      (decoderUnaryDepth (RawParser.parse state.core.word).matrix epsilon)
        bits) : CylinderContraction state epsilon where
  cylinder := highSectorContractedEnvelope state.core.word bits epsilon
    epsilonPositive phase
  cylinder_word := rfl
  radiusSq_le := highSectorContractedEnvelope_radiusSq_le state.core.word bits
    epsilonPositive phase

/-- Initial-low unary contraction at its common parser-progress target. -/
def lowUnaryContraction {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse state.core.word).phase = .lowUnary
      (initialLowContractionDepth epsilon)) :
    CylinderContraction state epsilon where
  cylinder := lowUnaryEnvelopeOfPhase state.core.word
    (CCLUnaryCylinder.binaryDepth epsilon) (by
      simpa only [initialLowContractionDepth] using phase)
  cylinder_word := rfl
  radiusSq_le := CCLUnaryCylinder.lowRadiusSq_binaryDepth_le epsilonPositive

/-- The initial-low delimiter and either partial sector code retain contraction
at the same common parser-progress target. -/
def initialLowSectorContraction
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (bits : RawParser.SectorBits)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse state.core.word).phase = .sector .initialLow
      (initialLowContractionDepth epsilon) bits) :
    CylinderContraction state epsilon where
  cylinder := initialLowSectorEnvelopeOfPhase state.core.word
    (initialLowContractionDepth epsilon) bits phase
  cylinder_word := rfl
  radiusSq_le :=
    initialLowSectorRadiusSq_contractionDepth_le epsilonPositive

end State

/-- Once the two independent component-error sums fit below their stored
projective gap, rational realizations of the two root words cannot denote the
same projective point. -/
theorem represented_points_not_equivalent_of_component_error_lt_gap
    {p : GaussianPolynomial} {ambient : RatBox}
    {left right : State p ambient}
    (gap : RegionGap left.core.numerical.box right.core.numerical.box)
    (thin : 8 * (left.componentError + right.componentError) <
      CCLChordalEnvelope.chordalGapSq left.core.numerical.box
        right.core.numerical.box gap.coordinateGap)
    {leftPoint rightPoint : QI}
    (leftRepresented : RawParserSemantics.Represented left.core.word leftPoint)
    (rightRepresented : RawParserSemantics.Represented right.core.word rightPoint) :
    ¬(Proj.affine leftPoint).Equivalent (Proj.affine rightPoint) := by
  have coupledThin :
      4 * (left.coupling.errorSq + right.coupling.errorSq) <
        CCLChordalEnvelope.chordalGapSq left.core.numerical.box
          right.core.numerical.box gap.coordinateGap := by
    rw [left.coupling_errorSq_eq_two_componentError,
      right.coupling_errorSq_eq_two_componentError]
    convert thin using 1
    ring
  apply CCLRawCylinderEnvelope.represented_points_not_equivalent_of_error_sum_lt_gap
    gap.positive gap.separated rfl rfl coupledThin
  · change RawParserSemantics.Represented
      left.cylinder.truncation.word leftPoint
    rw [left.cylinder_word]
    exact leftRepresented
  · change RawParserSemantics.Represented
      right.cylinder.truncation.word rightPoint
    rw [right.cylinder_word]
    exact rightRepresented

/-- Numerical accuracy refinement leaves the tagged cylinder untouched. -/
def refineState {p : GaussianPolynomial} {ambient : RatBox}
    (machine : CCLCoupledTrack.PersistentMachine p ambient)
    (current : State p ambient) (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    State p ambient := by
  let core := machine.refine current.core epsilon epsilonPositive
  exact
    { core := core
      cylinder := current.cylinder
      cylinder_word := current.cylinder_word.trans
        (machine.refine_word current.core epsilon epsilonPositive).symm }

theorem refineState_refines
    {p : GaussianPolynomial} {ambient : RatBox}
    (machine : CCLCoupledTrack.PersistentMachine p ambient)
    (current : State p ambient) (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    (refineState machine current epsilon epsilonPositive).Refines current := by
  exact ⟨machine.refine_nested current.core epsilon epsilonPositive,
    RawCylinderEnvelope.refines_refl current.cylinder⟩

theorem refineState_accurate
    {p : GaussianPolynomial} {ambient : RatBox}
    (machine : CCLCoupledTrack.PersistentMachine p ambient)
    (current : State p ambient) (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    (refineState machine current epsilon epsilonPositive).core.numerical.box.diagonalSq ≤
      epsilon ^ 2 := by
  exact machine.refine_accurate current.core epsilon epsilonPositive

theorem refineState_word
    {p : GaussianPolynomial} {ambient : RatBox}
    (machine : CCLCoupledTrack.PersistentMachine p ambient)
    (current : State p ambient) (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    (refineState machine current epsilon epsilonPositive).core.word =
      current.core.word :=
  machine.refine_word current.core epsilon epsilonPositive

/-- One exact next-bit result after installing metric-cylinder bookkeeping. -/
inductive StepResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) where
  | zero (root : p.eval 0 = 0)
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
  | next (bit : Bool) (state : State p ambient)
      (refines : state.Refines current)
      (word_eq : state.core.word = current.core.word ++ [bit])

/-- Install metric-cylinder bookkeeping around one already-computed persistent
controller result.  This factoring also lets a whole-box checkpoint feed a
single certified event step into the existing metric pipeline. -/
def liftStepResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (result : CCLCoupledTrack.PersistentStepResult current.core) :
    StepResult current := by
  match result with
  | .zero root => exact .zero root
  | .terminal point root nonzero completeWord complete =>
      exact .terminal point root nonzero completeWord complete
  | .next bit core coreRefines wordEq =>
      let truncation : TaggedTruncation := ⟨core.word⟩
      have isPrefix : current.cylinder.truncation.word <+: truncation.word := by
        change current.cylinder.truncation.word <+: core.word
        rw [current.cylinder_word, wordEq]
        exact List.prefix_append _ _
      let cylinder := current.cylinder.restrict truncation isPrefix
      let state : State p ambient :=
        { core := core
          cylinder := cylinder
          cylinder_word := rfl }
      exact .next bit state
        ⟨coreRefines, current.cylinder.restrict_refines truncation isPrefix⟩
        wordEq

/-- Lift one existing x--y/curve-count bit decision.  The new word restricts
the old cylinder certificate, so its radius never increases even inside an
unfinished unary or sector fragment. -/
def step {p : GaussianPolynomial} {ambient : RatBox}
    (machine : CCLCoupledTrack.PersistentMachine p ambient)
    (current : State p ambient) : StepResult current :=
  liftStepResult current (machine.step current.core)

/-- Result of structurally reading a requested number of further CCL bits.
The cylinder certificate and winding box both refine the input state. -/
inductive AdvanceResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) : ℕ → Type where
  | zero {count : ℕ} (root : p.eval 0 = 0) : AdvanceResult current count
  | terminal {count : ℕ} (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero) :
      AdvanceResult current count
  | advanced {count : ℕ} (state : State p ambient)
      (refines : state.Refines current)
      (bits : Prefix.Word)
      (bits_length : bits.length = count)
      (word_eq : state.core.word = current.core.word ++ bits)
      (length_eq : state.core.word.length = current.core.word.length + count) :
      AdvanceResult current count

/-- Finite recursion on the requested bit count. -/
def advanceBits {p : GaussianPolynomial} {ambient : RatBox}
    (machine : CCLCoupledTrack.PersistentMachine p ambient)
    (current : State p ambient) : (count : ℕ) → AdvanceResult current count
  | 0 => .advanced current (State.refines_refl current) [] rfl (by simp)
      (by simp)
  | count + 1 =>
      match step machine current with
      | .zero root => .zero root
      | .terminal point root nonzero completeWord complete =>
          .terminal point root nonzero completeWord complete
      | .next bit next nextRefines wordEq =>
          match advanceBits machine next count with
          | .zero root => .zero root
          | .terminal point root nonzero completeWord complete =>
              .terminal point root nonzero completeWord complete
          | .advanced final finalRefines finalBits finalBitsLength
              finalWord finalLength =>
              .advanced final (finalRefines.trans nextRefines)
                (bit :: finalBits) (by simp [finalBitsLength]) (by
                  rw [finalWord, wordEq]
                  simp [List.append_assoc]) (by
                have nextLength :
                    next.core.word.length = current.core.word.length + 1 := by
                  rw [wordEq]
                  simp
                omega)

/-- A joint finite request returns numerical accuracy, symbolic bit growth,
monotone cylinder refinement, and the explicit rational coupling bound. -/
inductive RequestResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (epsilon : ℚ) (count : ℕ) where
  | zero (root : p.eval 0 = 0)
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
  | nonterminal (state : State p ambient)
      (refines : state.Refines current)
      (accurate : state.core.numerical.box.diagonalSq ≤ epsilon ^ 2)
      (length_eq : state.core.word.length = current.core.word.length + count)
      (coupledError : state.coupling.errorSq ≤
        2 * (epsilon ^ 2 + current.cylinder.radiusSq))

/-- Refine the winding box once, then read exactly the requested number of
nonterminal bits.  Bit steps can only reduce the inherited cylinder radius. -/
def request {p : GaussianPolynomial} {ambient : RatBox}
    (machine : CCLCoupledTrack.PersistentMachine p ambient)
    (current : State p ambient) (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (count : ℕ) : RequestResult current epsilon count := by
  let accurate := refineState machine current epsilon epsilonPositive
  let run := advanceBits machine accurate count
  match run with
  | .zero root => exact .zero root
  | .terminal point root nonzero completeWord complete =>
      exact .terminal point root nonzero completeWord complete
  | .advanced final finalRefines _bits _bitsLength _wordEq finalLength =>
      have refinesCurrent : final.Refines current :=
        finalRefines.trans
          (refineState_refines machine current epsilon epsilonPositive)
      have diagonalMonotone : final.core.numerical.box.diagonalSq ≤
          accurate.core.numerical.box.diagonalSq :=
        CCLClearanceExclusion.RatBox.diagonalSq_le_of_refines finalRefines.1
      have accurateBound : accurate.core.numerical.box.diagonalSq ≤ epsilon ^ 2 :=
        refineState_accurate machine current epsilon epsilonPositive
      have diagonalBound := diagonalMonotone.trans accurateBound
      have radiusBound : final.cylinder.radiusSq ≤ current.cylinder.radiusSq :=
        refinesCurrent.cylinderRadiusSq_le
      exact .nonterminal final refinesCurrent diagonalBound (by
        rw [finalLength, refineState_word machine current epsilon epsilonPositive])
        (final.coupling.errorSq_le diagonalBound radiusBound)

end CCLMetricTrack
end FTA
