import FTA.CCLBranchSampling
import FTA.CCLClearanceExclusion
import FTA.ProjectivePath

/-!
# Finite orchestration of CCL-coupled winding-one tracks

This module isolates the finite recursion in Theorem 10.5 from the geometric
construction of each next-bit certificate.  A nonterminal state carries its
winding-one box, finite raw word, and a represented compatible rational
sample.  A machine supplies one accuracy refinement and one proof-bearing
branch step.  Structural recursion on the requested bit count then terminates
with either an exact rational-root record or a state meeting both requested
accuracy and word-growth bounds.
-/

namespace FTA
namespace CCLCoupledTrack

open CCL
open FTA.CCLCompatibleCandidates
open FTA.CCLGeometry
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Two strict sign comparisons against the same nonzero anchor induce a
strict sign comparison between the compared values. -/
theorem sameSign_of_common_anchor {anchor first second : ℚ}
    (firstSign : 0 < anchor * first)
    (secondSign : 0 < anchor * second) :
    0 < first * second := by
  have anchorNonzero : anchor ≠ 0 := by
    intro equality
    simp only [equality, zero_mul, lt_self_iff_false] at firstSign
  have anchorSquarePositive : 0 < anchor * anchor :=
    mul_self_pos.mpr anchorNonzero
  have productPositive :
      0 < (anchor * anchor) * (first * second) := by
    rw [← mul_mul_mul_comm]
    exact mul_pos firstSign secondSign
  exact pos_of_mul_pos_right productPositive anchorSquarePositive.le

/-- A represented sample together with a finite strict-sign neighbourhood
certificate.  Any point in the same box that preserves the displayed prior
signs represents the same raw prefix.  This is the persistent information
needed after a later owner-grid perturbation; retaining only one represented
point would lose the strict history branch chosen at the preceding step. -/
structure StableRepresentedOutcome
    (word : Prefix.Word) (sampleBox domain : RatBox)
    extends RepresentedOutcome word sampleBox where
  priors : List HermitianForm
  priorsNonzero : ∀ form ∈ priors, form.eval point ≠ 0
  stable : ∀ {nextPoint : QI}, domain.Contains nextPoint →
    (∀ form ∈ priors, 0 < form.eval point * form.eval nextPoint) →
      RawParserSemantics.Represented word nextPoint

/-- Restrict only the domain on which a stable represented outcome may be
perturbed; its displayed sample box and witness are unchanged. -/
def StableRepresentedOutcome.restrictDomain
    {word : Prefix.Word} {sampleBox domain smaller : RatBox}
    (outcome : StableRepresentedOutcome word sampleBox domain)
    (refines : smaller.Refines domain) :
    StableRepresentedOutcome word sampleBox smaller where
  toRepresentedOutcome := outcome.toRepresentedOutcome
  priors := outcome.priors
  priorsNonzero := outcome.priorsNonzero
  stable := by
    intro nextPoint inside preserved
    exact outcome.stable (refines.contains inside) preserved

/-- Finite descriptor of a rational lower-dimensional CCL cylinder. -/
structure RationalPathCylinder where
  path : FTA.ProjectivePath.Path
  interval : FTA.SturmTransducer.RationalInterval
  denominator_ne : ∀ {parameter : ℚ},
    interval.lower ≤ parameter → parameter ≤ interval.upper →
      path.denominator.eval (FTA.PathPolynomial.ofRat parameter) ≠ 0

def RationalPathCylinder.Contains
    (cylinder : RationalPathCylinder) (point : QI) : Prop :=
  ∃ parameter : ℚ,
    cylinder.interval.lower ≤ parameter ∧
      parameter ≤ cylinder.interval.upper ∧
      point = cylinder.path.value parameter

/-- A represented sample constrained to a fixed, possibly lower-dimensional
support.  Unlike `StableRepresentedOutcome`, this record makes no claim that
the represented word persists on an open sign cell.  It is the honest local
output for a CCL cylinder forced to remain on a rational source path. -/
structure ConstrainedRepresentedOutcome
    (word : Prefix.Word) (sampleBox : RatBox) (support : QI → Prop)
    extends RepresentedOutcome word sampleBox where
  supported : support point

/-- Semantic persistence of a represented word on a fixed constrained
support through every later winding-one box.  Open owner cells continue to
use `StableRepresentedOutcome`; this separate family records exactly the
weaker invariant required by genuine lower-dimensional cylinders. -/
structure PersistentConstrainedRepresentedSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    (word : Prefix.Word) (numerical : WindingOneState p ambient)
    (support : QI → Prop) where
  sample : (next : WindingOneState p ambient) →
    next.box.Refines numerical.box →
      ConstrainedRepresentedOutcome word next.box support

/-- The existing open-cell persistence invariant, factored into one record so
it can form one constructor of the general persistence mode. -/
structure PersistentStableRepresentedSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    (word : Prefix.Word) (numerical : WindingOneState p ambient) where
  sample : (next : WindingOneState p ambient) →
    next.box.Refines numerical.box →
      StableRepresentedOutcome word next.box numerical.box
  sample_priors : ∀ next nextRefines,
    (sample next nextRefines).priors =
      (sample numerical (RatBox.refines_refl numerical.box)).priors
  sample_sameSigns : ∀ next nextRefines form,
    form ∈ (sample numerical
      (RatBox.refines_refl numerical.box)).priors →
      0 < form.eval (sample numerical
          (RatBox.refines_refl numerical.box)).point *
        form.eval (sample next nextRefines).point

/-- General persistence of a represented finite word.  Ordinary cylinders
retain the stronger open sign-cell certificate; genuine boundary cylinders
retain a fixed constrained support instead. -/
inductive SamplePersistence
    {p : GaussianPolynomial} {ambient : RatBox}
    (word : Prefix.Word) (numerical : WindingOneState p ambient) where
  | stable (samples : PersistentStableRepresentedSamples word numerical)
  | constrained (cylinder : RationalPathCylinder)
      (samples : PersistentConstrainedRepresentedSamples word numerical
        cylinder.Contains)

def SamplePersistence.sampleOutcome
    {p : GaussianPolynomial} {ambient : RatBox}
    {word : Prefix.Word} {numerical next : WindingOneState p ambient}
    (persistence : SamplePersistence word numerical)
    (nextRefines : next.box.Refines numerical.box) :
    RepresentedOutcome word next.box :=
  match persistence with
  | .stable samples =>
      (samples.sample next nextRefines).toRepresentedOutcome
  | .constrained _ samples =>
      (samples.sample next nextRefines).toRepresentedOutcome

/-- Coupled state with the honest open-or-constrained persistence invariant.
The legacy `State` below is its open-cell specialization while controller
consumers are migrated. -/
structure PersistentState (p : GaussianPolynomial) (ambient : RatBox) where
  numerical : WindingOneState p ambient
  word : Prefix.Word
  persistence : SamplePersistence word numerical

def PersistentState.outcome
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : PersistentState p ambient) :
    RepresentedOutcome current.word current.numerical.box :=
  current.persistence.sampleOutcome
    (RatBox.refines_refl current.numerical.box)

/-- One nonterminal coupled numerical/symbolic state. -/
structure State (p : GaussianPolynomial) (ambient : RatBox) where
  numerical : WindingOneState p ambient
  word : Prefix.Word
  sample : QI
  sampleInside : numerical.box.Contains sample
  sampleNonzero : sample ≠ 0
  sampleRepresented : RawParserSemantics.Represented word sample
  /-- The finite historical forms are fixed for the lifetime of this symbolic
  state; refinements may move the witness but do not invent a new prior list. -/
  priors : List HermitianForm
  samplePriorsNonzero : ∀ form ∈ priors, form.eval sample ≠ 0
  /-- Constructive persistence of the symbolic prefix along the numerical
  track.  A single current sample is not enough: an accuracy refinement may
  exclude it, so every nested winding box must carry a newly bounded
  compatible sample and its strict-sign neighbourhood for the same word. -/
  sampleInRefinement : (next : WindingOneState p ambient) →
    next.box.Refines numerical.box →
      StableRepresentedOutcome word next.box numerical.box
  sampleInRefinement_priors : ∀ next nextRefines,
    (sampleInRefinement next nextRefines).priors = priors
  /-- Every nested witness uses the same orientation of every fixed prior.
  This is the quantitative coherence needed by bounded owner refinement. -/
  sampleInRefinement_sameSigns : ∀ next nextRefines form, form ∈ priors →
    0 < form.eval sample *
      form.eval (sampleInRefinement next nextRefines).point

/-- Factor a legacy open-cell state into the general stable persistence
constructor without changing any witness or sign invariant. -/
def State.stableSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) :
    PersistentStableRepresentedSamples current.word current.numerical where
  sample := current.sampleInRefinement
  sample_priors := by
    intro next nextRefines
    exact (current.sampleInRefinement_priors next nextRefines).trans
      (current.sampleInRefinement_priors current.numerical
        (RatBox.refines_refl current.numerical.box)).symm
  sample_sameSigns := by
    intro next nextRefines form member
    have basePriors := current.sampleInRefinement_priors current.numerical
      (RatBox.refines_refl current.numerical.box)
    have formMember : form ∈ current.priors := by
      rw [basePriors] at member
      exact member
    apply sameSign_of_common_anchor
    · exact current.sampleInRefinement_sameSigns current.numerical
        (RatBox.refines_refl current.numerical.box) form formMember
    · exact current.sampleInRefinement_sameSigns next nextRefines form
        formMember

/-- Reconstruct the legacy open-cell specialization from a factored stable
family. -/
def State.ofStableSamples
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical : WindingOneState p ambient}
    (samples : PersistentStableRepresentedSamples word numerical) :
    State p ambient := by
  let base := samples.sample numerical
    (RatBox.refines_refl numerical.box)
  exact
    { numerical := numerical
      word := word
      sample := base.point
      sampleInside := base.inside
      sampleNonzero := base.nonzero
      sampleRepresented := base.semantics
      priors := base.priors
      samplePriorsNonzero := base.priorsNonzero
      sampleInRefinement := samples.sample
      sampleInRefinement_priors := samples.sample_priors
      sampleInRefinement_sameSigns := samples.sample_sameSigns }

def PersistentState.ofStableSamples
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical : WindingOneState p ambient}
    (samples : PersistentStableRepresentedSamples word numerical) :
    PersistentState p ambient where
  numerical := numerical
  word := word
  persistence := .stable samples

def PersistentState.ofConstrainedSamples
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical : WindingOneState p ambient}
    (cylinder : RationalPathCylinder)
    (samples : PersistentConstrainedRepresentedSamples word numerical
      cylinder.Contains) : PersistentState p ambient where
  numerical := numerical
  word := word
  persistence := .constrained cylinder samples

def State.toPersistentState
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) : PersistentState p ambient where
  numerical := current.numerical
  word := current.word
  persistence := .stable current.stableSamples

/-- Every proper rational winding box contains an explicit nonzero rational
point representing the empty raw word.  If the center is zero, the left edge
at the center height is nonzero because the box has positive width. -/
def emptyWordSample
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) :
    StableRepresentedOutcome [] numerical.box numerical.box := by
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
        semantics := ⟨point, by
          simpa only [RawParser.parse, List.foldl_nil] using
            CCL.RawParserSemantics.initialState_represents point⟩
        priors := []
        priorsNonzero := by simp
        stable := by
          intro nextPoint _inside _preserved
          exact ⟨nextPoint, by
            simpa only [RawParser.parse, List.foldl_nil] using
              CCL.RawParserSemantics.initialState_represents nextPoint⟩ }
  · exact
      { point := numerical.box.center
        inside := numerical.box.contains_center
        nonzero := centerZero
        semantics := ⟨numerical.box.center, by
          simpa only [RawParser.parse, List.foldl_nil] using
            CCL.RawParserSemantics.initialState_represents
              numerical.box.center⟩
        priors := []
        priorsNonzero := by simp
        stable := by
          intro nextPoint _inside _preserved
          exact ⟨nextPoint, by
            simpa only [RawParser.parse, List.foldl_nil] using
              CCL.RawParserSemantics.initialState_represents nextPoint⟩ }

/-- Canonical persistent coupled state for the empty raw prefix. -/
def State.ofWindingOne
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) : State p ambient := by
  let sample := emptyWordSample numerical
  exact
    { numerical := numerical
      word := []
      sample := sample.point
      sampleInside := sample.inside
      sampleNonzero := sample.nonzero
      sampleRepresented := sample.semantics
      priors := []
      samplePriorsNonzero := by simp
      sampleInRefinement := fun next _refines =>
        let nextSample := emptyWordSample next
        { toRepresentedOutcome := nextSample.toRepresentedOutcome
          priors := []
          priorsNonzero := by simp
          stable := by
            intro nextPoint _inside _preserved
            exact ⟨nextPoint, by
              simpa only [RawParser.parse, List.foldl_nil] using
                CCL.RawParserSemantics.initialState_represents nextPoint⟩ }
      sampleInRefinement_priors := by simp
      sampleInRefinement_sameSigns := by simp }

def PersistentState.ofWindingOne
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) : PersistentState p ambient :=
  (State.ofWindingOne numerical).toPersistentState

/-- The persistent sample invariant makes an arbitrary finite track
refinement into a coupled-state refinement without changing the word. -/
def State.refineWithTrack
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (epsilon : ℚ) (positive : 0 < epsilon) : State p ambient := by
  let numerical := track.refine current.numerical epsilon positive
  have refines : numerical.box.Refines current.numerical.box :=
    track.nested current.numerical epsilon positive
  let sample := current.sampleInRefinement numerical refines
  let restrictedSample := sample.restrictDomain refines
  have samplePriors : restrictedSample.priors = current.priors := by
    simpa only [restrictedSample, sample,
      StableRepresentedOutcome.restrictDomain] using
      current.sampleInRefinement_priors numerical refines
  exact
    { numerical := numerical
      word := current.word
      sample := restrictedSample.point
      sampleInside := restrictedSample.inside
      sampleNonzero := restrictedSample.nonzero
      sampleRepresented := restrictedSample.semantics
      priors := current.priors
      samplePriorsNonzero := by
        intro form member
        apply restrictedSample.priorsNonzero form
        rw [samplePriors]
        exact member
      sampleInRefinement := fun next nextRefines =>
        (current.sampleInRefinement next
          (nextRefines.trans refines)).restrictDomain refines
      sampleInRefinement_priors := by
        intro next nextRefines
        simpa only [StableRepresentedOutcome.restrictDomain] using
          current.sampleInRefinement_priors next
            (nextRefines.trans refines)
      sampleInRefinement_sameSigns := by
        intro next nextRefines form member
        have first := current.sampleInRefinement_sameSigns numerical refines
          form member
        have second := current.sampleInRefinement_sameSigns next
          (nextRefines.trans refines) form member
        apply sameSign_of_common_anchor
        · simpa only [restrictedSample, sample,
            StableRepresentedOutcome.restrictDomain] using first
        · simpa only [StableRepresentedOutcome.restrictDomain] using second }

/-- Rebase an open stable family on a nested winding-one state. -/
def PersistentStableRepresentedSamples.refine
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical refined : WindingOneState p ambient}
    (samples : PersistentStableRepresentedSamples word numerical)
    (refines : refined.box.Refines numerical.box) :
    PersistentStableRepresentedSamples word refined where
  sample next nextRefines :=
    (samples.sample next (nextRefines.trans refines)).restrictDomain refines
  sample_priors := by
    intro next nextRefines
    simpa only [StableRepresentedOutcome.restrictDomain] using
      (samples.sample_priors next (nextRefines.trans refines)).trans
        (samples.sample_priors refined refines).symm
  sample_sameSigns := by
    intro next nextRefines form member
    have refinedPriors := samples.sample_priors refined refines
    have formMember : form ∈
        (samples.sample numerical
          (RatBox.refines_refl numerical.box)).priors := by
      rw [← refinedPriors]
      simpa only [StableRepresentedOutcome.restrictDomain] using member
    have first := samples.sample_sameSigns refined refines form formMember
    have second := samples.sample_sameSigns next
      (nextRefines.trans refines) form formMember
    apply sameSign_of_common_anchor
    · simpa only [StableRepresentedOutcome.restrictDomain] using first
    · simpa only [StableRepresentedOutcome.restrictDomain] using second

/-- Rebase a constrained semantic family on a nested winding-one state; its
fixed support and represented points are unchanged. -/
def PersistentConstrainedRepresentedSamples.refine
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical refined : WindingOneState p ambient} {support : QI → Prop}
    (samples : PersistentConstrainedRepresentedSamples word numerical support)
    (refines : refined.box.Refines numerical.box) :
    PersistentConstrainedRepresentedSamples word refined support where
  sample next nextRefines := samples.sample next (nextRefines.trans refines)

/-- Accuracy refinement preserves either persistence mode without converting
a lower-dimensional cylinder into a fictitious open cell. -/
def SamplePersistence.refine
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical refined : WindingOneState p ambient}
    (persistence : SamplePersistence word numerical)
    (refines : refined.box.Refines numerical.box) :
    SamplePersistence word refined :=
  match persistence with
  | .stable samples => .stable (samples.refine refines)
  | .constrained cylinder samples =>
      .constrained cylinder (samples.refine refines)

def PersistentState.refineWithTrack
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (current : PersistentState p ambient)
    (epsilon : ℚ) (positive : 0 < epsilon) : PersistentState p ambient := by
  let numerical := track.refine current.numerical epsilon positive
  have refines : numerical.box.Refines current.numerical.box :=
    track.nested current.numerical epsilon positive
  exact
    { numerical := numerical
      word := current.word
      persistence := current.persistence.refine refines }

/-- One exact next-bit outcome.  Zero has a dedicated finite terminal tag,
because the terminating CCL encoder is defined precisely on nonzero Gaussian
rationals.  A nonzero terminal result carries its complete finite encoding;
a nonterminal result already carries the new compatible sample. -/
inductive StepResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) where
  | zero (root : p.eval 0 = 0)
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
  | next (bit : Bool) (state : State p ambient)
      (refines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word ++ [bit])

/-- One exact next-bit outcome for the general open-or-constrained coupled
state. -/
inductive PersistentStepResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : PersistentState p ambient) where
  | zero (root : p.eval 0 = 0)
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
  | next (bit : Bool) (state : PersistentState p ambient)
      (refines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word ++ [bit])

/-- Every legacy open-cell step is a step of the general persistence
controller. -/
def StepResult.toPersistent
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : State p ambient} (result : StepResult current) :
    PersistentStepResult current.toPersistentState :=
  match result with
  | .zero root => .zero root
  | .terminal point root nonzero completeWord complete =>
      .terminal point root nonzero completeWord complete
  | .next bit state refines wordEq =>
      .next bit state.toPersistentState refines wordEq

/-- The finite interfaces supplied by unique-child refinement, compatible
sampling, and the completed next-bit branch controller. -/
structure Machine (p : GaussianPolynomial) (ambient : RatBox) where
  refine : (current : State p ambient) →
    (epsilon : ℚ) → 0 < epsilon → State p ambient
  refine_nested : ∀ current epsilon positive,
    (refine current epsilon positive).numerical.box.Refines
      current.numerical.box
  refine_accurate : ∀ current epsilon positive,
    (refine current epsilon positive).numerical.box.diagonalSq ≤ epsilon ^ 2
  refine_word : ∀ current epsilon positive,
    (refine current epsilon positive).word = current.word
  step : (current : State p ambient) → StepResult current

/-- Assemble the accuracy half of the coupled machine directly from the
finite winding track.  Only the proof-bearing next-bit operation remains as
an input. -/
def Machine.ofTrack
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (step : (current : State p ambient) → StepResult current) :
    Machine p ambient where
  refine := State.refineWithTrack track
  refine_nested := by
    intro current epsilon positive
    simpa only [State.refineWithTrack] using
      track.nested current.numerical epsilon positive
  refine_accurate := by
    intro current epsilon positive
    simpa only [State.refineWithTrack] using
      track.accurate current.numerical epsilon positive
  refine_word := by
    intro current epsilon positive
    rfl
  step := step

/-- Result after requesting exactly `count` further nonterminal bits.  An
early terminal result is retained; otherwise the word length grows by the
requested natural number and the numerical box refines the input state. -/
inductive AdvanceResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) : ℕ → Type where
  | zero {count : ℕ} (root : p.eval 0 = 0) :
      AdvanceResult current count
  | terminal {count : ℕ} (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero) :
      AdvanceResult current count
  | advanced {count : ℕ} (state : State p ambient)
      (refines : state.numerical.box.Refines current.numerical.box)
      (length_eq : state.word.length = current.word.length + count) :
      AdvanceResult current count

/-- Structural finite-bit recursion.  No persistence search or recursion
limit override is involved. -/
def advanceBits
    {p : GaussianPolynomial} {ambient : RatBox}
    (machine : Machine p ambient) (current : State p ambient) :
    (count : ℕ) → AdvanceResult current count
  | 0 => .advanced current (RatBox.refines_refl current.numerical.box) (by simp)
  | count + 1 =>
      match machine.step current with
      | .zero root => .zero root
      | .terminal point root nonzero completeWord complete =>
          .terminal point root nonzero completeWord complete
      | .next bit next refines word_eq =>
          match advanceBits machine next count with
          | .zero root => .zero root
          | .terminal point root nonzero completeWord complete =>
              .terminal point root nonzero completeWord complete
          | .advanced final finalRefines finalLength =>
              .advanced final (finalRefines.trans refines) (by
                have nextLength : next.word.length = current.word.length + 1 := by
                  rw [word_eq]
                  simp
                omega)

/-- Combined finite request result from Theorem 10.5. -/
inductive RequestResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (epsilon : ℚ) (count : ℕ) where
  | zero (root : p.eval 0 = 0)
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
  | nonterminal (state : State p ambient)
      (refines : state.numerical.box.Refines current.numerical.box)
      (accurate : state.numerical.box.diagonalSq ≤ epsilon ^ 2)
      (length_eq : state.word.length = current.word.length + count)

/-- One accuracy call followed by the requested finite number of bit calls.
Nesting preserves the first call's squared-diagonal certificate. -/
def request
    {p : GaussianPolynomial} {ambient : RatBox}
    (machine : Machine p ambient) (current : State p ambient)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon) (count : ℕ) :
    RequestResult current epsilon count := by
  let accurate := machine.refine current epsilon epsilonPositive
  let run := advanceBits machine accurate count
  match run with
  | .zero root => exact .zero root
  | .terminal point root nonzero completeWord complete =>
      exact .terminal point root nonzero completeWord complete
  | .advanced final finalRefines finalLength =>
      have refinesCurrent : final.numerical.box.Refines current.numerical.box :=
        finalRefines.trans
          (machine.refine_nested current epsilon epsilonPositive)
      have diagonalMonotone : final.numerical.box.diagonalSq ≤
          accurate.numerical.box.diagonalSq :=
        CCLClearanceExclusion.RatBox.diagonalSq_le_of_refines finalRefines
      have accurateBound : accurate.numerical.box.diagonalSq ≤ epsilon ^ 2 :=
        machine.refine_accurate current epsilon epsilonPositive
      have wordUnchanged : accurate.word = current.word :=
        machine.refine_word current epsilon epsilonPositive
      exact .nonterminal final refinesCurrent
        (diagonalMonotone.trans accurateBound) (by
          rw [finalLength, wordUnchanged])

/-- Finite machine interface for the honest open-or-constrained coupled
state. -/
structure PersistentMachine (p : GaussianPolynomial) (ambient : RatBox) where
  refine : (current : PersistentState p ambient) →
    (epsilon : ℚ) → 0 < epsilon → PersistentState p ambient
  refine_nested : ∀ current epsilon positive,
    (refine current epsilon positive).numerical.box.Refines
      current.numerical.box
  refine_accurate : ∀ current epsilon positive,
    (refine current epsilon positive).numerical.box.diagonalSq ≤ epsilon ^ 2
  refine_word : ∀ current epsilon positive,
    (refine current epsilon positive).word = current.word
  step : (current : PersistentState p ambient) → PersistentStepResult current

def PersistentMachine.ofTrack
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (step : (current : PersistentState p ambient) →
      PersistentStepResult current) :
    PersistentMachine p ambient where
  refine := PersistentState.refineWithTrack track
  refine_nested := by
    intro current epsilon positive
    simpa only [PersistentState.refineWithTrack] using
      track.nested current.numerical epsilon positive
  refine_accurate := by
    intro current epsilon positive
    simpa only [PersistentState.refineWithTrack] using
      track.accurate current.numerical epsilon positive
  refine_word := by
    intro current epsilon positive
    rfl
  step := step

/-- Result after requesting exactly `count` further bits from the generalized
persistence machine. -/
inductive PersistentAdvanceResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : PersistentState p ambient) : ℕ → Type where
  | zero {count : ℕ} (root : p.eval 0 = 0) :
      PersistentAdvanceResult current count
  | terminal {count : ℕ} (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero) :
      PersistentAdvanceResult current count
  | advanced {count : ℕ} (state : PersistentState p ambient)
      (refines : state.numerical.box.Refines current.numerical.box)
      (length_eq : state.word.length = current.word.length + count) :
      PersistentAdvanceResult current count

/-- Structural finite-bit recursion for both persistence modes. -/
def persistentAdvanceBits
    {p : GaussianPolynomial} {ambient : RatBox}
    (machine : PersistentMachine p ambient)
    (current : PersistentState p ambient) :
    (count : ℕ) → PersistentAdvanceResult current count
  | 0 => .advanced current (RatBox.refines_refl current.numerical.box) (by simp)
  | count + 1 =>
      match machine.step current with
      | .zero root => .zero root
      | .terminal point root nonzero completeWord complete =>
          .terminal point root nonzero completeWord complete
      | .next bit next refines wordEq =>
          match persistentAdvanceBits machine next count with
          | .zero root => .zero root
          | .terminal point root nonzero completeWord complete =>
              .terminal point root nonzero completeWord complete
          | .advanced final finalRefines finalLength =>
              .advanced final (finalRefines.trans refines) (by
                have nextLength :
                    next.word.length = current.word.length + 1 := by
                  rw [wordEq]
                  simp
                omega)

inductive PersistentRequestResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : PersistentState p ambient) (epsilon : ℚ) (count : ℕ) where
  | zero (root : p.eval 0 = 0)
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
  | nonterminal (state : PersistentState p ambient)
      (refines : state.numerical.box.Refines current.numerical.box)
      (accurate : state.numerical.box.diagonalSq ≤ epsilon ^ 2)
      (length_eq : state.word.length = current.word.length + count)

/-- One accuracy call followed by any requested finite number of generalized
controller steps. -/
def persistentRequest
    {p : GaussianPolynomial} {ambient : RatBox}
    (machine : PersistentMachine p ambient)
    (current : PersistentState p ambient)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon) (count : ℕ) :
    PersistentRequestResult current epsilon count := by
  let accurate := machine.refine current epsilon epsilonPositive
  let run := persistentAdvanceBits machine accurate count
  match run with
  | .zero root => exact .zero root
  | .terminal point root nonzero completeWord complete =>
      exact .terminal point root nonzero completeWord complete
  | .advanced final finalRefines finalLength =>
      have refinesCurrent : final.numerical.box.Refines current.numerical.box :=
        finalRefines.trans
          (machine.refine_nested current epsilon epsilonPositive)
      have diagonalMonotone : final.numerical.box.diagonalSq ≤
          accurate.numerical.box.diagonalSq :=
        CCLClearanceExclusion.RatBox.diagonalSq_le_of_refines finalRefines
      have accurateBound : accurate.numerical.box.diagonalSq ≤ epsilon ^ 2 :=
        machine.refine_accurate current epsilon epsilonPositive
      have wordUnchanged : accurate.word = current.word :=
        machine.refine_word current epsilon epsilonPositive
      exact .nonterminal final refinesCurrent
        (diagonalMonotone.trans accurateBound) (by
          rw [finalLength, wordUnchanged])

end CCLCoupledTrack
end FTA
