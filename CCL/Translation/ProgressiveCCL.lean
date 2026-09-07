import CCL.Translation.Enclosures
import CCL.Arithmetic.OperationalEquivalence
import CCL.Progressive.MachineSemantics

/-!
# Finite translations through a progressive CCL cursor

A finite CCL observation contains two synchronized interfaces to one named
program: a persistent raw prefix of an explicitly requested length and a
finite rational sample/error observation.  The prefix has exact projective
machine semantics; the sidecar supplies the rational precision gauge used for
cross-representation comparison.
-/

namespace CCL.FiniteTranslation

abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Machine := CCL.ProgressiveTransducer.Machine
abbrev OperationalApproximation :=
  CCL.ProgressiveApproximation.Approximation

/-- Running two successive finite bit requests is the same executable machine
as running their sum in one request. -/
theorem advance_add (machine : Machine) (first second : Nat) :
    CCL.ProgressiveTransducer.advance
        (CCL.ProgressiveTransducer.advance machine first) second =
      CCL.ProgressiveTransducer.advance machine (first + second) := by
  induction first generalizing machine with
  | zero => simp only [CCL.ProgressiveTransducer.advance, Nat.zero_add]
  | succ first inductionHypothesis =>
      simp only [Nat.succ_add, CCL.ProgressiveTransducer.advance]
      exact inductionHypothesis
        (CCL.ProgressiveTransducer.nextBit machine).2

/-- One finite raw prefix together with one finite quantitative observation of
the same progressive CCL name. -/
structure CursorObservation (name : Named) where
  sampleIndex : Nat
  bitCount : Nat
deriving DecidableEq, Repr

namespace CursorObservation

def approximation (name : Named) : OperationalApproximation :=
  CCL.ProgressiveSampling.approximation name

def word {name : Named} (observation : CursorObservation name) : List Bool :=
  (CCL.ProgressiveTransducer.advance name.machine
    observation.bitCount).emitted

theorem word_length {name : Named} (observation : CursorObservation name) :
    observation.word.length = observation.bitCount :=
  (name.productive observation.bitCount).2

theorem word_isPrefix_of_bitCount_le {name : Named}
    {earlier later : CursorObservation name}
    (order : earlier.bitCount ≤ later.bitCount) :
    earlier.word.IsPrefix later.word := by
  obtain ⟨extra, identity⟩ := Nat.exists_eq_add_of_le order
  change
    (CCL.ProgressiveTransducer.advance name.machine
      earlier.bitCount).emitted.IsPrefix
      (CCL.ProgressiveTransducer.advance name.machine
        later.bitCount).emitted
  rw [identity, ← advance_add]
  exact CCL.ProgressiveTransducer.advance_extends
    (CCL.ProgressiveTransducer.advance name.machine earlier.bitCount) extra

/-- The whole internally committed parser chunk has exact projective
semantics after every finite exposed-prefix request. -/
theorem exactCursor {name : Named} (observation : CursorObservation name) :
    CCL.ProgressiveMachineSemantics.ExactCursor name.process name.state
      (CCL.ProgressiveTransducer.advance name.machine observation.bitCount) :=
  CCL.ProgressiveMachineSemantics.Named.advance_exact name
    observation.bitCount

end CursorObservation

/-- Finite CCL cursor observations.  Refinement simultaneously advances the
quantitative sample index and preserves the raw prefix. -/
def cursorRepresentation (name : Named) : FiniteRepresentation where
  Observation := CursorObservation name
  Possible observation value :=
    (CursorObservation.approximation name).Possible
      observation.sampleIndex value
  witness observation :=
    (CursorObservation.approximation name).sample observation.sampleIndex
  witness_possible observation :=
    (CursorObservation.approximation name).sample_possible
      observation.sampleIndex
  Refines inner outer :=
    outer.sampleIndex ≤ inner.sampleIndex ∧
      outer.bitCount ≤ inner.bitCount
  refines_refl _ := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refines_trans innerMiddle middleOuter :=
    ⟨middleOuter.1.trans innerMiddle.1,
      middleOuter.2.trans innerMiddle.2⟩
  possible_persists refines possible :=
    (CursorObservation.approximation name).possible_persists
      refines.1 possible
  precisionSq observation :=
    (CursorObservation.approximation name).radiusSq observation.sampleIndex
  precisionSq_nonneg observation :=
    (CursorObservation.approximation name).radiusSq_nonneg
      observation.sampleIndex
  boundary := .projective

/-- Forgetting the persistent raw-prefix counter recovers the ordinary finite
approximation observation with no precision loss. -/
def cursorToApproximation (name : Named) :
    ObservationMap (cursorRepresentation name)
      (approximationRepresentation
        (CursorObservation.approximation name)) where
  map observation := observation.sampleIndex
  covers possible := possible
  coherent refines :=
    FiniteRepresentation.compatible_of_refines refines.1
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le _ := by simp [cursorRepresentation, approximationRepresentation]
  schedule _ :=
    { sourceRefinements := 0
      emittedUnits := 0
      arithmeticSteps := 1 }
  costBound _ := 1
  cost_le _ := Nat.le_refl 1

/-- Indices selected by the already-proved operational round trip for one
finite request.  Naming this computation keeps the realizer and its coherence
proof definitionally synchronized. -/
def approximationToCursorComparison
    (approximation : OperationalApproximation) (index : Nat)
    (request : Request) :=
  let cclApproximation :=
    CursorObservation.approximation approximation.toNamed
  let accurateStart := cclApproximation.refineIndex 0 request.targetSq
    request.positive
  let equivalent :=
    CCL.OperationalEquivalence.Equivalent.toNamed_sampling approximation
  equivalent.compare accurateStart index request.targetSq request.positive

/-- The canonical finite realizer from random-access fast-Cauchy observations
to the productive CCL protocol.  The comparison indices come from the existing
operational round-trip theorem.  `bitCount = sampleIndex + 1` exposes the
sequential cost of retaining a raw prefix alongside a random-access query. -/
def approximationToCursor (approximation : OperationalApproximation) :
    FiniteRealizer (approximationRepresentation approximation)
      (cursorRepresentation approximation.toNamed) where
  translate index request := by
    let cclApproximation :=
      CursorObservation.approximation approximation.toNamed
    let accurateStart := cclApproximation.refineIndex 0 request.targetSq
      request.positive
    let comparison :=
      approximationToCursorComparison approximation index request
    let output : CursorObservation approximation.toNamed :=
      { sampleIndex := comparison.leftIndex
        bitCount := comparison.leftIndex + 1 }
    exact
      { source' := comparison.rightIndex
        output := output
        source_refines := comparison.right_ge
        relates := fun sourceValue targetValue =>
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (targetValue - sourceValue) < request.targetSq
        source_to_target := by
          rintro sourceValue ⟨sourceLater, sourceOrder, rfl⟩
          refine ⟨cclApproximation.sample comparison.leftIndex,
            cclApproximation.sample_possible comparison.leftIndex, ?_⟩
          exact comparison.close (Nat.le_refl _) sourceOrder
        target_to_source := by
          rintro targetValue ⟨targetLater, targetOrder, rfl⟩
          refine ⟨approximation.sample comparison.rightIndex,
            approximation.sample_possible comparison.rightIndex, ?_⟩
          exact comparison.close targetOrder (Nat.le_refl _)
        precisionLoss := 0
        precisionLoss_nonneg := le_rfl
        precision := by
          change cclApproximation.radiusSq comparison.leftIndex <
            request.targetSq + 0
          calc
            cclApproximation.radiusSq comparison.leftIndex ≤
                cclApproximation.radiusSq accurateStart := by
              change CCL.FiniteGeometric.quarterRadius 4
                  comparison.leftIndex ≤
                CCL.FiniteGeometric.quarterRadius 4 accurateStart
              exact CCL.FiniteGeometric.quarterRadius_antitone
                (by decide) comparison.left_ge
            _ < request.targetSq :=
              cclApproximation.refineIndex_accurate 0 request.targetSq
                request.positive
            _ = request.targetSq + 0 := by ring1
        schedule :=
          { sourceRefinements := comparison.leftIndex + 1
            emittedUnits := comparison.leftIndex + 1
            arithmeticSteps := 2 }
        costBound := 2 * (comparison.leftIndex + 1) + 2
        cost_le := by
          change
            (comparison.leftIndex + 1) + (comparison.leftIndex + 1) + 2 ≤
              2 * (comparison.leftIndex + 1) + 2
          omega }

/-- Nat-indexed executable entry point for clients of the fast-Cauchy
representation. -/
def approximationToCursorAt (approximation : OperationalApproximation)
    (index : Nat) (request : Request) :=
  (approximationToCursor approximation).translate index request

@[simp] theorem approximationToCursorAt_bitCount
    (approximation : OperationalApproximation) (index : Nat)
    (request : Request) :
    (approximationToCursorAt approximation index request).output.bitCount =
      (approximationToCursorAt approximation index request).output.sampleIndex +
        1 := rfl

@[simp] theorem approximationToCursorAt_costBound
    (approximation : OperationalApproximation) (index : Nat)
    (request : Request) :
    (approximationToCursorAt approximation index request).costBound =
      2 * ((approximationToCursorAt approximation index request).output.sampleIndex +
        1) + 2 := rfl

theorem approximationToCursorAt_schedule
    (approximation : OperationalApproximation) (index : Nat)
    (request : Request) :
    let result := approximationToCursorAt approximation index request
    result.output.word.length = result.output.bitCount ∧
      result.output.bitCount = result.output.sampleIndex + 1 ∧
      result.costBound = 2 * (result.output.sampleIndex + 1) + 2 := by
  dsimp only
  exact ⟨CursorObservation.word_length _,
    approximationToCursorAt_bitCount approximation index request,
    approximationToCursorAt_costBound approximation index request⟩

theorem approximationToCursorAt_precision
    (approximation : OperationalApproximation) (index : Nat)
    (request : Request) :
    (cursorRepresentation approximation.toNamed).precisionSq
        (approximationToCursorAt approximation index request).output <
      request.targetSq := by
  let result := approximationToCursorAt approximation index request
  calc
    (cursorRepresentation approximation.toNamed).precisionSq result.output <
        request.targetSq + result.precisionLoss := result.precision
    _ = request.targetSq := by
      change request.targetSq + 0 = request.targetSq
      ring1

/-- The emitted raw word in every translated response has exactly the
displayed sequential cost and exact machine semantics. -/
theorem approximationToCursor_word_certificate
    (approximation : OperationalApproximation) (index : Nat)
    (request : Request) :
    let result := (approximationToCursor approximation).translate index request
    result.output.word.length = result.output.bitCount ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        approximation.toNamed.process approximation.toNamed.state
        (CCL.ProgressiveTransducer.advance approximation.toNamed.machine
          result.output.bitCount) := by
  dsimp only
  exact ⟨CursorObservation.word_length _, CursorObservation.exactCursor _⟩

/-- One headline finite-request certificate.  It collects the quantitative
sidecar precision, exact productive-machine prefix semantics, and the measured
schedule bound which are otherwise stored in separate projections of the
translation result. -/
theorem approximationToCursorAt_certified
    (approximation : OperationalApproximation) (index : Nat)
    (request : Request) :
    let result := approximationToCursorAt approximation index request
    result.output.word.length = result.output.bitCount ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        approximation.toNamed.process approximation.toNamed.state
        (CCL.ProgressiveTransducer.advance approximation.toNamed.machine
          result.output.bitCount) ∧
      (cursorRepresentation approximation.toNamed).precisionSq result.output <
        request.targetSq ∧
      result.schedule.work ≤ result.costBound ∧
      result.costBound = 2 * (result.output.sampleIndex + 1) + 2 := by
  dsimp only
  exact ⟨CursorObservation.word_length _, CursorObservation.exactCursor _,
    approximationToCursorAt_precision approximation index request,
    (approximationToCursorAt approximation index request).cost_le,
    approximationToCursorAt_costBound approximation index request⟩

/-- Independent requests from the same approximation retain one persistent
external protocol.  Their output cursors are ordered by refinement, and the
raw word of the coarser cursor is literally a prefix of the finer word. -/
theorem approximationToCursorAt_persistent
    (approximation : OperationalApproximation)
    (leftIndex rightIndex : Nat) (leftRequest rightRequest : Request) :
    let left := approximationToCursorAt approximation leftIndex leftRequest
    let right := approximationToCursorAt approximation rightIndex rightRequest
    ((cursorRepresentation approximation.toNamed).Refines
          right.output left.output ∧
        left.output.word.IsPrefix right.output.word) ∨
      ((cursorRepresentation approximation.toNamed).Refines
          left.output right.output ∧
        right.output.word.IsPrefix left.output.word) := by
  dsimp only
  have leftSynchronized := approximationToCursorAt_bitCount approximation
    leftIndex leftRequest
  have rightSynchronized := approximationToCursorAt_bitCount approximation
    rightIndex rightRequest
  rcases Nat.le_total
      (approximationToCursorAt approximation leftIndex leftRequest).output.sampleIndex
      (approximationToCursorAt approximation rightIndex rightRequest).output.sampleIndex
      with leftBeforeRight | rightBeforeLeft
  · apply Or.inl
    have bitOrder :
        (approximationToCursorAt approximation leftIndex leftRequest).output.bitCount ≤
          (approximationToCursorAt approximation rightIndex rightRequest).output.bitCount := by
      rw [leftSynchronized, rightSynchronized]
      exact Nat.add_le_add_right leftBeforeRight 1
    exact ⟨⟨leftBeforeRight, bitOrder⟩,
      CursorObservation.word_isPrefix_of_bitCount_le bitOrder⟩
  · apply Or.inr
    have bitOrder :
        (approximationToCursorAt approximation rightIndex rightRequest).output.bitCount ≤
          (approximationToCursorAt approximation leftIndex leftRequest).output.bitCount := by
      rw [leftSynchronized, rightSynchronized]
      exact Nat.add_le_add_right rightBeforeLeft 1
    exact ⟨⟨rightBeforeLeft, bitOrder⟩,
      CursorObservation.word_isPrefix_of_bitCount_le bitOrder⟩

/-- The name-level round trip is the repository's operational equivalence,
not equality of the two finite sample programs. -/
def approximationCursorRoundTrip
    (approximation : OperationalApproximation) :
    CCL.OperationalEquivalence.Equivalent
      (CursorObservation.approximation approximation.toNamed)
      approximation :=
  CCL.OperationalEquivalence.Equivalent.toNamed_sampling approximation

/-- The complete certified relationship between one random-access finite
approximation and its productive CCL name.  The forward realizer, lossless
cursor-forgetting map, operational round trip, per-request certificate, and
cross-request prefix persistence are packaged as one reusable object. -/
structure CertifiedApproximationCursorRoundTrip
    (approximation : OperationalApproximation) where
  forward : FiniteRealizer (approximationRepresentation approximation)
    (cursorRepresentation approximation.toNamed)
  backward : ObservationMap (cursorRepresentation approximation.toNamed)
    (approximationRepresentation
      (CursorObservation.approximation approximation.toNamed))
  operational : CCL.OperationalEquivalence.Equivalent
    (CursorObservation.approximation approximation.toNamed) approximation
  request_certified : ∀ (index : Nat) (request : Request),
    let result := forward.translate index request
    result.output.word.length = result.output.bitCount ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        approximation.toNamed.process approximation.toNamed.state
        (CCL.ProgressiveTransducer.advance approximation.toNamed.machine
          result.output.bitCount) ∧
      (cursorRepresentation approximation.toNamed).precisionSq result.output <
        request.targetSq ∧
      result.schedule.work ≤ result.costBound ∧
      result.costBound = 2 * (result.output.sampleIndex + 1) + 2
  outputs_persistent : ∀ (leftIndex rightIndex : Nat)
      (leftRequest rightRequest : Request),
    let left := forward.translate leftIndex leftRequest
    let right := forward.translate rightIndex rightRequest
    ((cursorRepresentation approximation.toNamed).Refines
          right.output left.output ∧
        left.output.word.IsPrefix right.output.word) ∨
      ((cursorRepresentation approximation.toNamed).Refines
          left.output right.output ∧
        right.output.word.IsPrefix left.output.word)

/-- Canonical bundled round trip for every executable finite approximation. -/
def certifiedApproximationCursorRoundTrip
    (approximation : OperationalApproximation) :
    CertifiedApproximationCursorRoundTrip approximation where
  forward := approximationToCursor approximation
  backward := cursorToApproximation approximation.toNamed
  operational := approximationCursorRoundTrip approximation
  request_certified := approximationToCursorAt_certified approximation
  outputs_persistent := approximationToCursorAt_persistent approximation

end CCL.FiniteTranslation
