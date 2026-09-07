import mathlib.Tactic.QuotientFreeOmega
import CCL.Boundary.NextBit
import RFAP.Isolation.ShrinkingTrack

/-!
# Persistent constructive CCL prefixes on shrinking root boxes

A fresh rational sample from each refined box need not retain any prefix of
the preceding sample's CCL word.  The persistent invariant below records the
stronger fact actually needed by the paper: every later winding-one subbox
has an explicit nonzero rational sample represented by the same raw prefix.

The second half of the file is deliberately structural.  It proves that a
finite one-bit controller with this invariant can be iterated for any
requested natural number of bits while the numerical box is independently
contracted to a requested rational accuracy.  Constructing that one-bit
controller from the finite curve-count and equality-owner geometry is a
separate obligation; it is not postulated as a theorem here.
-/

namespace CCL.PersistentCCL

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Word := List Bool
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev Represented := CCL.RawParserSemantics.Represented
abbrev Formula := CCL.CCLFormula.Formula

/-- One displayed nonzero rational point in a box that has the indicated raw
CCL prefix. -/
structure CompatibleSample (word : Word) (box : Box) where
  point : Gaussian
  inside : box.Contains point
  nonzero : point ≠ 0
  represented : Represented word point

namespace CompatibleSample

/-- Proof-bearing local decision data at one compatible sample. -/
structure NextDecision (word : Word) (input : Gaussian) where
  tail : Gaussian
  represents : CCL.RawParserSemantics.Represents
    (CCL.RawParser.parse word) input tail
  decision : CCL.CCLNextBit.Decision
    (CCL.RawParser.parse word) input tail

/-- Expose the finite Hermitian formula satisfied by the explicit affine
tail witnessing a sample's raw-prefix representation.  This is the precise
finite predicate consumed by the geometric one-bit controller. -/
theorem tailFormula
    {word : Word} {box : Box} (sample : CompatibleSample word box) :
    ∃ tail : Gaussian,
      (CCL.CCLFormula.parseFormula word).Holds tail ∧
        CCL.RawParserSemantics.Represents
          (CCL.RawParser.parse word) sample.point tail := by
  rcases sample.represented with ⟨tail, represents⟩
  exact ⟨tail,
    (CCL.CCLFormula.parseFormula_iff word tail).2
      represents.2.2,
    represents⟩

/-- Every compatible rational sample has a total finite local next-bit
decision.  Persistence of one selected decision across all later subboxes is
the geometric obligation of the controller. -/
def nextDecision
    {word : Word} {box : Box} (sample : CompatibleSample word box) :
    NextDecision word sample.point := by
  let parser := CCL.RawParser.parse word
  let tail := CCL.RawParser.homographic
    (CCL.CCLPullback.adjugate parser.matrix) sample.point
  have determinantNonzero :
      CCL.CCLPullback.determinant parser.matrix ≠ 0 := by
    simpa only [parser, CCL.CCLPullback.determinant] using
      CCL.RawParser.parse_det_ne word
  have represents : CCL.RawParserSemantics.Represents
      parser sample.point tail := by
    exact CCL.CCLNextBit.represents_inverse_tail_of_represented
      parser sample.point determinantNonzero sample.represented
  exact
    { tail := tail
      represents := represents
      decision := CCL.CCLNextBit.decide
        parser sample.point tail (CCL.RawParser.parse_det_ne word)
        represents }

end CompatibleSample

/-- Persistent compatibility means that a sample can be computed in every
supplied later winding-one subbox, not merely in the currently displayed
box.  The quantification is over explicit finite states and refinement
certificates; it does not form a set or a completed root. -/
structure PersistentSamples
    {p : GaussianPolynomial} {ambient : Box}
    (word : Word) (current : WindingOneState p ambient) where
  sample : (later : WindingOneState p ambient) →
    later.box.Refines current.box → CompatibleSample word later.box

/-- The empty raw prefix is represented by every displayed rational point,
so every winding-one state has an initial persistent provider. -/
def PersistentSamples.initial
    {p : GaussianPolynomial} {ambient : Box}
    (current : WindingOneState p ambient) : PersistentSamples [] current where
  sample := fun later _refines =>
    let sample := later.box.nonzeroSample later.proper
    { point := sample.point
      inside := sample.inside
      nonzero := sample.nonzero
      represented :=
        CCL.RawParserSemantics.represented_nil sample.point }

/-- A numerical winding-one state together with one raw prefix that persists
under all subsequent supplied refinements. -/
structure State (p : GaussianPolynomial) (ambient : Box) where
  numerical : WindingOneState p ambient
  word : Word
  samples : PersistentSamples word numerical

namespace State

/-- Canonical persistent state at the empty word. -/
def initial
    {p : GaussianPolynomial} {ambient : Box}
    (numerical : WindingOneState p ambient) : State p ambient :=
  { numerical := numerical
    word := []
    samples := PersistentSamples.initial numerical }

/-- Obtain the current displayed compatible sample by applying the provider
to the current box itself. -/
def currentSample
    {p : GaussianPolynomial} {ambient : Box}
    (state : State p ambient) : CompatibleSample state.word state.numerical.box :=
  state.samples.sample state.numerical
    (RFAP.Boxes.Box.refines_refl state.numerical.box)

/-- Refine only the numerical box, preserving the same raw prefix by
composition of explicit box-refinement certificates. -/
def refine
    {p : GaussianPolynomial} {ambient : Box}
    (state : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines state.numerical.box) : State p ambient :=
  { numerical := numerical
    word := state.word
    samples :=
      { sample := fun later laterRefines =>
          state.samples.sample later (laterRefines.trans refines) } }

@[simp] theorem refine_word
    {p : GaussianPolynomial} {ambient : Box}
    (state : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines state.numerical.box) :
    (state.refine numerical refines).word = state.word := rfl

theorem refine_box
    {p : GaussianPolynomial} {ambient : Box}
    (state : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines state.numerical.box) :
    (state.refine numerical refines).numerical.box.Refines
      state.numerical.box :=
  refines

end State

/-- Joint order on persistent states: boxes only shrink and words only grow
by right extension. -/
structure StateRefines
    {p : GaussianPolynomial} {ambient : Box}
    (inner outer : State p ambient) : Prop where
  box : inner.numerical.box.Refines outer.numerical.box
  word : outer.word.IsPrefix inner.word

theorem stateRefines_refl
    {p : GaussianPolynomial} {ambient : Box}
    (state : State p ambient) : StateRefines state state :=
  ⟨RFAP.Boxes.Box.refines_refl state.numerical.box,
    List.prefix_refl _⟩

theorem StateRefines.trans
    {p : GaussianPolynomial} {ambient : Box}
    {inner middle outer : State p ambient}
    (innerMiddle : StateRefines inner middle)
    (middleOuter : StateRefines middle outer) : StateRefines inner outer :=
  ⟨innerMiddle.box.trans middleOuter.box,
    middleOuter.word.trans innerMiddle.word⟩

/-- A displayed exact rational root found inside the current finite box. -/
structure ExactRootIn
    (p : GaussianPolynomial) (box : Box) where
  point : Gaussian
  root : p.eval point = 0
  inside : box.Contains point

/-- Contract only the numerical component of a persistent state. -/
def refineAlong
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) : State p ambient :=
  current.refine (track.refine current.numerical epsilon positive)
    (track.nested current.numerical epsilon positive)

theorem refineAlong_refines
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    StateRefines (refineAlong track current epsilon positive) current :=
  ⟨track.nested current.numerical epsilon positive, List.prefix_refl _⟩

theorem refineAlong_accurate
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (refineAlong track current epsilon positive).numerical.box.diagonalSq ≤
      epsilon ^ 2 :=
  track.accurate current.numerical epsilon positive

/-- Output contract of the remaining geometric controller.  A nonterminal
step appends exactly one bit while preserving the persistent provider;
otherwise it returns an exact displayed rational root in the current box. -/
inductive StepResult
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  | exact (root : ExactRootIn p current.numerical.box)
  | next (bit : Bool) (state : State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word ++ [bit])

/-- Finite data needed to turn one persistent raw prefix into its next bit.
The concrete implementation must be supplied by the constructive
curve-count/equality-owner development. -/
structure Controller (p : GaussianPolynomial) (ambient : Box) where
  step : (current : State p ambient) → StepResult current

/-- Result of structurally requesting a finite number of further bits. -/
inductive AdvanceResult
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) : Nat → Type where
  | exact {count : Nat} (root : ExactRootIn p current.numerical.box) :
      AdvanceResult current count
  | advanced {count : Nat} (state : State p ambient)
      (refines : StateRefines state current)
      (extension : Word)
      (extension_length : extension.length = count)
      (word_eq : state.word = current.word ++ extension)
      (length_eq : state.word.length = current.word.length + count) :
      AdvanceResult current count

/-- Structural recursion on the requested number of raw bits. -/
def advanceBits
    {p : GaussianPolynomial} {ambient : Box}
    (controller : Controller p ambient) (current : State p ambient) :
    (count : Nat) → AdvanceResult current count
  | 0 => .advanced current (stateRefines_refl current) [] rfl (by simp) (by simp)
  | count + 1 =>
      match controller.step current with
      | .exact root => .exact root
      | .next bit next boxRefines nextWord =>
          match advanceBits controller next count with
          | .exact root => .exact
              { point := root.point
                root := root.root
                inside := boxRefines.contains root.inside }
          | .advanced final finalRefines extension extensionLength
              finalWord finalLength =>
              have nextRefines : StateRefines next current := by
                refine ⟨boxRefines, ?_⟩
                rw [nextWord]
                exact List.prefix_append _ _
              .advanced final (finalRefines.trans nextRefines)
                (bit :: extension) (by simp [extensionLength]) (by
                  rw [finalWord, nextWord]
                  simp [List.append_assoc]) (by
                    rw [finalLength, nextWord]
                    simp only [List.length_append, List.length_singleton]
                    rw [Nat.add_assoc, Nat.add_comm 1 count])

/-- Joint finite request: first contract the numerical box to the requested
accuracy and then request exactly `count` additional bits unless an exact
rational root is encountered. -/
inductive RequestResult
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) (epsilon : Coordinate) (count : Nat) where
  | exact (root : ExactRootIn p current.numerical.box)
  | nonterminal (state : State p ambient)
      (refines : StateRefines state current)
      (accurate : state.numerical.box.diagonalSq ≤ epsilon ^ 2)
      (length_eq : state.word.length = current.word.length + count)

def request
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (controller : Controller p ambient)
    (current : State p ambient) (epsilon : Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    RequestResult current epsilon count := by
  let contracted := refineAlong track current epsilon positive
  let run := advanceBits controller contracted count
  match run with
  | .exact root =>
      exact .exact
        { point := root.point
          root := root.root
          inside :=
            (refineAlong_refines track current epsilon positive).box.contains
              root.inside }
  | .advanced final finalRefines _extension _extensionLength _wordEq
      finalLength =>
      have refinesCurrent : StateRefines final current :=
        finalRefines.trans (refineAlong_refines track current epsilon positive)
      have diagonalMonotone : final.numerical.box.diagonalSq ≤
          contracted.numerical.box.diagonalSq :=
        RFAP.Boxes.Box.diagonalSq_le_of_refines finalRefines.box
      exact .nonterminal final refinesCurrent
        (diagonalMonotone.trans
          (refineAlong_accurate track current epsilon positive)) (by
            simpa only [contracted, refineAlong, State.refine_word] using
              finalLength)

end CCL.PersistentCCL
