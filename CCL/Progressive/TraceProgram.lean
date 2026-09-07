import CCL.Progressive.PartialCalculus

/-!
# One certified finite program for progressive quadratic CCL calculus

The lower trace modules construct the arithmetic and analytic certificates.
This file packages those constructors into one indexed finite program.  The
index is the actual semantic `Trace`, so a program cannot pair unrelated value
and slope names: every node computes one common increment, base, output,
slope, remainder, and rational quadratic factor.

Partial nodes store their displayed lower-quadrance or disk evidence in the
constructor.  The total decision wrappers expose a precise missing
certificate.  Finally, the strengthened request contract combines the
quadratic law with persistent word extension, exact raw-parser semantics, and
the requested projective-cylinder diameter for every one of the five live CCL
channels.
-/

namespace CCL.ProgressiveTraceProgram

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Trace := CCL.ProgressiveQuadraticTrace.Trace
abbrev Decision (α : Type) :=
  CCL.ProgressivePartialCalculus.Decision α
abbrev MissingCertificate :=
  CCL.ProgressivePartialCalculus.MissingCertificate

open RFAP.ConstructiveGaussian.Gaussian

/-- Finite provenance for one semantic progressive quadratic trace.  A source
is already a trace certificate, not an unconstrained pair of coherent names. -/
inductive Program : {increment : Nat → Gaussian} → Trace increment → Prop
  | source (trace : Trace increment) : Program trace
  | scale (scalar : Gaussian) {trace : Trace increment} :
      Program trace →
      Program
        (CCL.ProgressiveAutomaticQuadraticTrace.Trace.scaleAutomatic
          scalar trace)
  | add {left right : Trace increment} : Program left → Program right →
      Program (CCL.ProgressiveQuadraticTrace.Trace.add left right)
  | neg {trace : Trace increment} : Program trace →
      Program (CCL.ProgressiveQuadraticTrace.Trace.neg trace)
  | mul {left right : Trace increment} : Program left → Program right →
      Program
        (CCL.ProgressiveAutomaticQuadraticTrace.Trace.mulAutomatic
          left right)
  | reciprocal {trace : Trace increment} : Program trace →
      (baseLower outputLower : Coordinate) →
      (basePositive : 0 < baseLower) →
      (outputPositive : 0 < outputLower) →
      (baseApart : ∀ index,
        baseLower ≤ normSq (trace.certificate index).base) →
      (outputApart : ∀ index,
        outputLower ≤ normSq (trace.certificate index).output) →
      Program
        (CCL.ProgressiveAutomaticQuadraticTrace.Trace.reciprocalAutomatic
          trace baseLower outputLower basePositive outputPositive baseApart
            outputApart)
  | div {numerator denominator : Trace increment} :
      Program numerator → Program denominator →
      (baseLower outputLower : Coordinate) →
      (basePositive : 0 < baseLower) →
      (outputPositive : 0 < outputLower) →
      (baseApart : ∀ index,
        baseLower ≤ normSq (denominator.certificate index).base) →
      (outputApart : ∀ index,
        outputLower ≤ normSq (denominator.certificate index).output) →
      Program
        (CCL.ProgressiveAutomaticQuadraticTrace.Trace.divAutomatic
          numerator denominator baseLower outputLower basePositive
            outputPositive baseApart outputApart)
  | compose {inner : Trace increment}
      {outer : Trace (fun index =>
        (inner.certificate index).output - (inner.certificate index).base)} :
      Program inner → Program outer →
      (incrementUnit : ∀ index, normSq (increment index) ≤ 1) →
      Program
        (CCL.ProgressiveAutomaticQuadraticTrace.Trace.composeAutomatic
          inner outer incrementUnit)
  | exponential {inner : Trace increment} : Program inner →
      (baseUnit : ∀ index, normSq (inner.certificate index).base ≤ 1) →
      (movementUnit : ∀ index,
        normSq ((inner.certificate index).output -
          (inner.certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index, normSq (increment index) ≤ 1) →
      Program
        (CCL.ProgressiveAutomaticQuadraticTrace.Trace.exponentialAutomatic
          inner baseUnit movementUnit incrementUnit)
  | reducedLog {inner : Trace increment} : Program inner →
      (movementDisk : ∀ index,
        normSq ((inner.certificate index).output -
          (inner.certificate index).base) ≤ 1 / 9) →
      (incrementUnit : ∀ index, normSq (increment index) ≤ 1) →
      Program
        (CCL.ProgressiveAutomaticQuadraticTrace.Trace.reducedLogAutomatic
          inner movementDisk incrementUnit)
  | sine {inner : Trace increment} : Program inner →
      (rotatedBaseUnit : ∀ index,
        normSq
          ((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
            inner).certificate index).base ≤ 1) →
      (rotatedMovementUnit : ∀ index,
        normSq
          (((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
              inner).certificate index).output -
            ((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
              inner).certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index, normSq (increment index) ≤ 1) →
      Program
        (CCL.ProgressiveAutomaticQuadraticTrace.Trace.sineAutomatic
          inner rotatedBaseUnit rotatedMovementUnit incrementUnit)
  | cosine {inner : Trace increment} : Program inner →
      (rotatedBaseUnit : ∀ index,
        normSq
          ((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
            inner).certificate index).base ≤ 1) →
      (rotatedMovementUnit : ∀ index,
        normSq
          (((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
              inner).certificate index).output -
            ((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
              inner).certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index, normSq (increment index) ≤ 1) →
      Program
        (CCL.ProgressiveAutomaticQuadraticTrace.Trace.cosineAutomatic
          inner rotatedBaseUnit rotatedMovementUnit incrementUnit)

/-- A semantic trace together with the finite program which produced it. -/
structure Calculation (increment : Nat → Gaussian) where
  trace : Trace increment
  program : Program trace

namespace Calculation

def source {increment : Nat → Gaussian} (trace : Trace increment) :
    Calculation increment := ⟨trace, Program.source trace⟩

def scale (scalar : Gaussian) {increment : Nat → Gaussian}
    (calculation : Calculation increment) : Calculation increment :=
  ⟨CCL.ProgressiveAutomaticQuadraticTrace.Trace.scaleAutomatic
      scalar calculation.trace,
    Program.scale scalar calculation.program⟩

def add {increment : Nat → Gaussian}
    (left right : Calculation increment) : Calculation increment :=
  ⟨CCL.ProgressiveQuadraticTrace.Trace.add left.trace right.trace,
    Program.add left.program right.program⟩

def neg {increment : Nat → Gaussian} (calculation : Calculation increment) :
    Calculation increment :=
  ⟨CCL.ProgressiveQuadraticTrace.Trace.neg calculation.trace,
    Program.neg calculation.program⟩

def sub {increment : Nat → Gaussian}
    (left right : Calculation increment) : Calculation increment :=
  add left (neg right)

def mul {increment : Nat → Gaussian}
    (left right : Calculation increment) : Calculation increment :=
  ⟨CCL.ProgressiveAutomaticQuadraticTrace.Trace.mulAutomatic
      left.trace right.trace,
    Program.mul left.program right.program⟩

def reciprocal {increment : Nat → Gaussian}
    (calculation : Calculation increment)
    (baseLower outputLower : Coordinate)
    (basePositive : 0 < baseLower) (outputPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ normSq (calculation.trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ normSq (calculation.trace.certificate index).output) :
    Calculation increment :=
  ⟨CCL.ProgressiveAutomaticQuadraticTrace.Trace.reciprocalAutomatic
      calculation.trace baseLower outputLower basePositive outputPositive
        baseApart outputApart,
    Program.reciprocal calculation.program baseLower outputLower basePositive
      outputPositive baseApart outputApart⟩

def div {increment : Nat → Gaussian}
    (numerator denominator : Calculation increment)
    (baseLower outputLower : Coordinate)
    (basePositive : 0 < baseLower) (outputPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ normSq (denominator.trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ normSq (denominator.trace.certificate index).output) :
    Calculation increment :=
  ⟨CCL.ProgressiveAutomaticQuadraticTrace.Trace.divAutomatic
      numerator.trace denominator.trace baseLower outputLower basePositive
        outputPositive baseApart outputApart,
    Program.div numerator.program denominator.program baseLower outputLower
      basePositive outputPositive baseApart outputApart⟩

def compose {increment : Nat → Gaussian}
    (inner : Calculation increment)
    (outer : Calculation (fun index =>
      (inner.trace.certificate index).output -
        (inner.trace.certificate index).base))
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨CCL.ProgressiveAutomaticQuadraticTrace.Trace.composeAutomatic
      inner.trace outer.trace incrementUnit,
    Program.compose inner.program outer.program incrementUnit⟩

def exponential {increment : Nat → Gaussian}
    (inner : Calculation increment)
    (baseUnit : ∀ index, normSq (inner.trace.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      normSq ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨CCL.ProgressiveAutomaticQuadraticTrace.Trace.exponentialAutomatic
      inner.trace baseUnit movementUnit incrementUnit,
    Program.exponential inner.program baseUnit movementUnit incrementUnit⟩

def reducedLog {increment : Nat → Gaussian}
    (inner : Calculation increment)
    (movementDisk : ∀ index,
      normSq ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨CCL.ProgressiveAutomaticQuadraticTrace.Trace.reducedLogAutomatic
      inner.trace movementDisk incrementUnit,
    Program.reducedLog inner.program movementDisk incrementUnit⟩

def sine {increment : Nat → Gaussian} (inner : Calculation increment)
    (rotatedBaseUnit : ∀ index,
      normSq
        ((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
          inner.trace).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      normSq
        (((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
            inner.trace).certificate index).output -
          ((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
            inner.trace).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨CCL.ProgressiveAutomaticQuadraticTrace.Trace.sineAutomatic
      inner.trace rotatedBaseUnit rotatedMovementUnit incrementUnit,
    Program.sine inner.program rotatedBaseUnit rotatedMovementUnit
      incrementUnit⟩

def cosine {increment : Nat → Gaussian} (inner : Calculation increment)
    (rotatedBaseUnit : ∀ index,
      normSq
        ((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
          inner.trace).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      normSq
        (((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
            inner.trace).certificate index).output -
          ((CCL.ProgressiveAutomaticQuadraticTrace.Trace.rotateAutomatic
            inner.trace).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨CCL.ProgressiveAutomaticQuadraticTrace.Trace.cosineAutomatic
      inner.trace rotatedBaseUnit rotatedMovementUnit incrementUnit,
    Program.cosine inner.program rotatedBaseUnit rotatedMovementUnit
      incrementUnit⟩

/-! ## Explicit decisions for partial constructors -/

def decideReciprocal {increment : Nat → Gaussian}
    (calculation : Calculation increment) :
    CCL.ProgressivePartialCalculus.AutomaticReciprocalEvidence
        calculation.trace → Decision (Calculation increment)
  | .supplied baseLower outputLower basePositive outputPositive
      baseApart outputApart =>
      .accepted (calculation.reciprocal baseLower outputLower basePositive
        outputPositive baseApart outputApart)
  | .missingBaseApartness => .rejected .denominatorApartness
  | .missingOutputApartness => .rejected .outputApartness

def decideExponential {increment : Nat → Gaussian}
    (calculation : Calculation increment) :
    CCL.ProgressivePartialCalculus.AutomaticExponentialEvidence
        calculation.trace → Decision (Calculation increment)
  | .supplied baseUnit movementUnit incrementUnit =>
      .accepted
        (calculation.exponential baseUnit movementUnit incrementUnit)
  | .missingDisk => .rejected .inputDisk

def decideReducedLog {increment : Nat → Gaussian}
    (calculation : Calculation increment) :
    CCL.ProgressivePartialCalculus.AutomaticReducedLogEvidence
        calculation.trace → Decision (Calculation increment)
  | .supplied movementDisk incrementUnit =>
      .accepted (calculation.reducedLog movementDisk incrementUnit)
  | .missingChart => .rejected .safeLogarithmChart

@[simp] theorem decideReciprocal_missing_base
    {increment : Nat → Gaussian} (calculation : Calculation increment) :
    (decideReciprocal calculation .missingBaseApartness).missing? =
      some .denominatorApartness := rfl

@[simp] theorem decideReciprocal_missing_output
    {increment : Nat → Gaussian} (calculation : Calculation increment) :
    (decideReciprocal calculation .missingOutputApartness).missing? =
      some .outputApartness := rfl

@[simp] theorem decideExponential_missing_disk
    {increment : Nat → Gaussian} (calculation : Calculation increment) :
    (decideExponential calculation .missingDisk).missing? =
      some .inputDisk := rfl

@[simp] theorem decideReducedLog_missing_chart
    {increment : Nat → Gaussian} (calculation : Calculation increment) :
    (decideReducedLog calculation .missingChart).missing? =
      some .safeLogarithmChart := rfl

/-! ## Strengthened persistent request contract -/

open CCL.ProgressiveMachineSemantics

/-- Every entry of the five-channel common-index request carries all of the
persistent representation facts, not merely its new word length. -/
structure EntryRequestContract
    (entry : CCL.ProgressivePersistentTable.ChannelCursor)
    (target : Coordinate) (positive : 0 < target) (count : Nat) : Prop where
  word_extends : entry.cursor.machine.emitted.IsPrefix
    (entry.request target positive count).cursor.machine.emitted
  word_length :
    (entry.request target positive count).cursor.machine.emitted.length =
      entry.cursor.machine.emitted.length + count
  exact : ExactCursor entry.channel.name.process entry.rootState
    (entry.request target positive count).cursor.machine
  cylinder : ∀ {left right : Gaussian},
    SemanticMode.possible
        (entry.request target positive count).cursor.machine.mode left →
      SemanticMode.possible
        (entry.request target positive count).cursor.machine.mode right →
      CCL.Chordal.chordalSq
          ((entry.request target positive count).cursor.machine.image left)
          ((entry.request target positive count).cursor.machine.image right) ≤
        target

/-- End-to-end request contract for a finite certified calculation. -/
structure PersistentRequestContract {increment : Nat → Gaussian}
    (calculation : Calculation increment) (current : Nat)
    (target : Coordinate) (positive : 0 < target) (count : Nat) : Prop where
  quadratic :
    CCL.ProgressiveQuadraticTrace.Trace.RequestContract
      calculation.trace current target positive count
  entries : ∀ entry,
    entry ∈ (calculation.trace.cursorTableAt
      (calculation.trace.requestIndex current target)).entries →
      EntryRequestContract entry target positive count

theorem persistent_bitstream_and_quadratic_law
    {increment : Nat → Gaussian} (calculation : Calculation increment)
    (current : Nat) (target : Coordinate) (positive : 0 < target)
    (count : Nat) :
    PersistentRequestContract calculation current target positive count := by
  refine
    { quadratic := calculation.trace.bitstream_and_quadratic_law
        current target positive count
      entries := ?_ }
  intro entry member
  exact
    { word_extends := entry.request_word_extends target positive count
      word_length := entry.request_word_length target positive count
      exact := entry.request_exact target positive count
      cylinder := by
        intro left right leftPossible rightPossible
        exact entry.request_pair_chordalSq_le target positive count
          leftPossible rightPossible }

/-! ## Executable regression witnesses -/

def changingInput : Calculation
    CCL.ProgressiveQuadraticTrace.Trace.exponentialWitnessApproximation.sample :=
  source CCL.ProgressiveQuadraticTrace.Trace.nonterminatingIdentity

def changingArithmetic : Calculation
    CCL.ProgressiveQuadraticTrace.Trace.exponentialWitnessApproximation.sample :=
  changingInput.mul (changingInput.add changingInput)

theorem changingArithmetic_input_changes :
    CCL.ProgressiveQuadraticTrace.Trace.exponentialWitnessApproximation.sample
        0 ≠
      CCL.ProgressiveQuadraticTrace.Trace.exponentialWitnessApproximation.sample
        1 :=
  CCL.ProgressiveQuadraticTrace.Trace.nonterminatingIdentity_changes

theorem changingArithmetic_keeps_emitting (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    PersistentRequestContract changingArithmetic 0 target positive count :=
  changingArithmetic.persistent_bitstream_and_quadratic_law
    0 target positive count

def exactCalculation {increment : Gaussian}
    (certificate : CCL.QuadraticJet.Certificate increment) :
    Calculation (fun _ => increment) :=
  source (CCL.ProgressiveQuadraticTrace.Trace.exact certificate)

@[simp] theorem exactCalculation_certificate {increment : Gaussian}
    (certificate : CCL.QuadraticJet.Certificate increment)
    (index : Nat) :
    (exactCalculation certificate).trace.certificate index = certificate :=
  CCL.ProgressiveQuadraticTrace.Trace.exact_certificate
    certificate index

end Calculation

end CCL.ProgressiveTraceProgram
