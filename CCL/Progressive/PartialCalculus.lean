import CCL.Arithmetic.CertifiedExpression
import CCL.Progressive.AutomaticQuadraticTrace

/-!
# Explicit finite failure states for partial progressive operations

Reciprocal, division, logarithm, chart transition, and branch selection are
not total operations on opaque CCL names.  Their constructors below consume a
finite evidence state and return either a constructed program or a visible
reason why the request cannot proceed.  Thus failure is data; it is never a
silent appeal to a completed nonzero value or a globally chosen branch.
-/

namespace CCL.ProgressivePartialCalculus

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev ProgressiveFirstJet :=
  CCL.ProgressiveFirstJet.FirstJet
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart

/-- Finite evidence which a rejected program still needs. -/
inductive MissingCertificate where
  | denominatorApartness
  | outputApartness
  | safeLogarithmChart
  | chartOverlap
  | branchAlignment
  | quadraticTransport
  | inputDisk
deriving DecidableEq, Repr

universe u

/-- A total result type for an operation with a constructive domain. -/
inductive Decision (α : Type u) : Type u where
  | accepted : α → Decision α
  | rejected : MissingCertificate → Decision α

namespace Decision

def missing? {α : Type u} : Decision α → Option MissingCertificate
  | .accepted _ => none
  | .rejected missing => some missing

@[simp] theorem missing?_accepted {α : Type u} (value : α) :
    (Decision.accepted value).missing? = none := rfl

@[simp] theorem missing?_rejected {α : Type u}
    (missing : MissingCertificate) :
    (Decision.rejected (α := α) missing).missing? = some missing := rfl

end Decision

/-! ## Ordinary progressive first jets -/

inductive ReciprocalEvidence (jet : ProgressiveFirstJet) where
  | supplied : CCL.ProgressiveTransducer.Named.Apart
      jet.value.name → ReciprocalEvidence jet
  | missing : ReciprocalEvidence jet

def reciprocal (jet : ProgressiveFirstJet) :
    ReciprocalEvidence jet → Decision ProgressiveFirstJet
  | .supplied apart => .accepted (jet.reciprocal apart)
  | .missing => .rejected .denominatorApartness

inductive DivisionEvidence (denominator : ProgressiveFirstJet) where
  | supplied : CCL.ProgressiveTransducer.Named.Apart
      denominator.value.name → DivisionEvidence denominator
  | missing : DivisionEvidence denominator

def div (numerator denominator : ProgressiveFirstJet) :
    DivisionEvidence denominator → Decision ProgressiveFirstJet
  | .supplied apart => .accepted (numerator.div denominator apart)
  | .missing => .rejected .denominatorApartness

/-- A logarithm needs both the actual anchored branch chart and apartness for
the derivative's reciprocal channel. -/
inductive LogarithmEvidence (jet : ProgressiveFirstJet) where
  | supplied : (branch : AnchoredChart jet.value) →
      CCL.ProgressiveTransducer.Named.Apart jet.value.name →
        LogarithmEvidence jet
  | missingChart : LogarithmEvidence jet
  | missingApartness : AnchoredChart jet.value → LogarithmEvidence jet

def logarithm (jet : ProgressiveFirstJet) :
    LogarithmEvidence jet → Decision ProgressiveFirstJet
  | .supplied branch apart => .accepted (jet.logarithm branch apart)
  | .missingChart => .rejected .safeLogarithmChart
  | .missingApartness _branch => .rejected .denominatorApartness

@[simp] theorem reciprocal_missing_exposes_requirement
    (jet : ProgressiveFirstJet) :
    (reciprocal jet .missing).missing? = some .denominatorApartness := rfl

@[simp] theorem division_missing_exposes_requirement
    (numerator denominator : ProgressiveFirstJet) :
    (div numerator denominator .missing).missing? =
      some .denominatorApartness := rfl

@[simp] theorem logarithm_missing_chart_exposes_requirement
    (jet : ProgressiveFirstJet) :
    (logarithm jet .missingChart).missing? = some .safeLogarithmChart := rfl

@[simp] theorem logarithm_missing_apartness_exposes_requirement
    (jet : ProgressiveFirstJet) (branch : AnchoredChart jet.value) :
    (logarithm jet (.missingApartness branch)).missing? =
      some .denominatorApartness := rfl

/-! ## Semantic quadratic traces -/

abbrev Trace := CCL.ProgressiveQuadraticTrace.Trace
abbrev Transport := CCL.ProgressiveQuadraticTrace.Trace.Transport
abbrev AutomaticTrace :=
  CCL.ProgressiveAutomaticQuadraticTrace.Trace

/-- All finite evidence needed by pointwise reciprocal transport. -/
inductive TraceReciprocalEvidence {increment : Nat → Gaussian}
    (trace : Trace increment) where
  | supplied :
      (baseNonzero : ∀ index, (trace.certificate index).base ≠ 0) →
      (outputNonzero : ∀ index, (trace.certificate index).output ≠ 0) →
      Transport increment
        (fun index => (trace.certificate index).reciprocal
          (baseNonzero index) (outputNonzero index)) →
      TraceReciprocalEvidence trace
  | missingBaseApartness : TraceReciprocalEvidence trace
  | missingOutputApartness : TraceReciprocalEvidence trace
  | missingTransport :
      (baseNonzero : ∀ index, (trace.certificate index).base ≠ 0) →
      (outputNonzero : ∀ index, (trace.certificate index).output ≠ 0) →
      TraceReciprocalEvidence trace

def traceReciprocal {increment : Nat → Gaussian} (trace : Trace increment) :
    TraceReciprocalEvidence trace → Decision (Trace increment)
  | .supplied baseNonzero outputNonzero transport =>
      .accepted (trace.reciprocal baseNonzero outputNonzero transport)
  | .missingBaseApartness => .rejected .denominatorApartness
  | .missingOutputApartness => .rejected .outputApartness
  | .missingTransport _ _ => .rejected .quadraticTransport

@[simp] theorem traceReciprocal_missing_exposes_requirement
    {increment : Nat → Gaussian} (trace : Trace increment) :
    (traceReciprocal trace .missingBaseApartness).missing? =
      some .denominatorApartness := rfl

@[simp] theorem traceReciprocal_missing_output_exposes_requirement
    {increment : Nat → Gaussian} (trace : Trace increment) :
    (traceReciprocal trace .missingOutputApartness).missing? =
      some .outputApartness := rfl

@[simp] theorem traceReciprocal_missing_transport_exposes_requirement
    {increment : Nat → Gaussian} (trace : Trace increment)
    (baseNonzero : ∀ index, (trace.certificate index).base ≠ 0)
    (outputNonzero : ∀ index, (trace.certificate index).output ≠ 0) :
    (traceReciprocal trace
      (.missingTransport baseNonzero outputNonzero)).missing? =
        some .quadraticTransport := rfl

/-- The local exponential trace exposes every disk and transport obligation. -/
inductive TraceExponentialEvidence {increment : Nat → Gaussian}
    (trace : Trace increment) where
  | supplied :
      (baseUnit : ∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (trace.certificate index).base ≤ 1) →
      (movementUnit : ∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((trace.certificate index).output -
            (trace.certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq (increment index) ≤ 1) →
      Transport increment
        (fun index => (trace.certificate index).compose
          (CCL.QuadraticJet.Certificate.exponential
            (baseUnit index) (movementUnit index) index)
          (incrementUnit index)) →
      TraceExponentialEvidence trace
  | missingDisk : TraceExponentialEvidence trace
  | missingTransport :
      (baseUnit : ∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (trace.certificate index).base ≤ 1) →
      (movementUnit : ∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((trace.certificate index).output -
            (trace.certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq (increment index) ≤ 1) →
      TraceExponentialEvidence trace

def traceExponential {increment : Nat → Gaussian} (trace : Trace increment) :
    TraceExponentialEvidence trace → Decision (Trace increment)
  | .supplied baseUnit movementUnit incrementUnit transport =>
      .accepted
        (trace.exponential baseUnit movementUnit incrementUnit transport)
  | .missingDisk => .rejected .inputDisk
  | .missingTransport _ _ _ => .rejected .quadraticTransport

@[simp] theorem traceExponential_missing_exposes_requirement
    {increment : Nat → Gaussian} (trace : Trace increment) :
    (traceExponential trace .missingDisk).missing? = some .inputDisk := rfl

@[simp] theorem traceExponential_missing_transport_exposes_requirement
    {increment : Nat → Gaussian} (trace : Trace increment)
    (baseUnit : ∀ index,
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (trace.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((trace.certificate index).output -
          (trace.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index,
      RFAP.ConstructiveGaussian.Gaussian.normSq (increment index) ≤ 1) :
    (traceExponential trace
      (.missingTransport baseUnit movementUnit incrementUnit)).missing? =
        some .quadraticTransport := rfl

/-! ## Automatically transported semantic traces -/

/-- Constructive reciprocal evidence is a pair of displayed positive lower
quadrances, not merely a proposition that each sampled denominator is
nonzero. -/
inductive AutomaticReciprocalEvidence {increment : Nat → Gaussian}
    (trace : Trace increment) where
  | supplied :
      (baseLower outputLower : Coordinate) →
      0 < baseLower → 0 < outputLower →
      (∀ index, baseLower ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (trace.certificate index).base) →
      (∀ index, outputLower ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (trace.certificate index).output) →
      AutomaticReciprocalEvidence trace
  | missingBaseApartness : AutomaticReciprocalEvidence trace
  | missingOutputApartness : AutomaticReciprocalEvidence trace

def automaticReciprocal {increment : Nat → Gaussian} (trace : Trace increment) :
    AutomaticReciprocalEvidence trace → Decision (Trace increment)
  | .supplied baseLower outputLower basePositive outputPositive
      baseApart outputApart =>
    .accepted
      (CCL.ProgressiveAutomaticQuadraticTrace.Trace.reciprocalAutomatic
        trace baseLower outputLower basePositive outputPositive baseApart
          outputApart)
  | .missingBaseApartness => .rejected .denominatorApartness
  | .missingOutputApartness => .rejected .outputApartness

@[simp] theorem automaticReciprocal_missing_base_exposes_requirement
    {increment : Nat → Gaussian} (trace : Trace increment) :
    (automaticReciprocal trace .missingBaseApartness).missing? =
      some .denominatorApartness := rfl

@[simp] theorem automaticReciprocal_missing_output_exposes_requirement
    {increment : Nat → Gaussian} (trace : Trace increment) :
    (automaticReciprocal trace .missingOutputApartness).missing? =
      some .outputApartness := rfl

/-- The automatic local exponential needs only its three displayed disk
certificates; the geometric transport is computed internally. -/
inductive AutomaticExponentialEvidence {increment : Nat → Gaussian}
    (trace : Trace increment) where
  | supplied :
      (∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (trace.certificate index).base ≤ 1) →
      (∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((trace.certificate index).output -
            (trace.certificate index).base) ≤ 1) →
      (∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq (increment index) ≤ 1) →
      AutomaticExponentialEvidence trace
  | missingDisk : AutomaticExponentialEvidence trace

def automaticExponential {increment : Nat → Gaussian} (trace : Trace increment) :
    AutomaticExponentialEvidence trace → Decision (Trace increment)
  | .supplied baseUnit movementUnit incrementUnit =>
    .accepted
      (CCL.ProgressiveAutomaticQuadraticTrace.Trace.exponentialAutomatic
        trace baseUnit movementUnit incrementUnit)
  | .missingDisk => .rejected .inputDisk

@[simp] theorem automaticExponential_missing_exposes_requirement
    {increment : Nat → Gaussian} (trace : Trace increment) :
    (automaticExponential trace .missingDisk).missing? =
      some .inputDisk := rfl

/-- The reduced complex logarithm similarly consumes its explicit local disk
and original increment disk, with no separate continuity record. -/
inductive AutomaticReducedLogEvidence {increment : Nat → Gaussian}
    (trace : Trace increment) where
  | supplied :
      (∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((trace.certificate index).output -
            (trace.certificate index).base) ≤ 1 / 9) →
      (∀ index,
        RFAP.ConstructiveGaussian.Gaussian.normSq (increment index) ≤ 1) →
      AutomaticReducedLogEvidence trace
  | missingChart : AutomaticReducedLogEvidence trace

def automaticReducedLog {increment : Nat → Gaussian} (trace : Trace increment) :
    AutomaticReducedLogEvidence trace → Decision (Trace increment)
  | .supplied movementDisk incrementUnit =>
    .accepted
      (CCL.ProgressiveAutomaticQuadraticTrace.Trace.reducedLogAutomatic
        trace movementDisk incrementUnit)
  | .missingChart => .rejected .safeLogarithmChart

@[simp] theorem automaticReducedLog_missing_exposes_requirement
    {increment : Nat → Gaussian} (trace : Trace increment) :
    (automaticReducedLog trace .missingChart).missing? =
      some .safeLogarithmChart := rfl

/-! ## Chart and branch transitions -/

/-- The minimal finite state for a chart transition: an overlap certificate
and a branch-alignment certificate are logically separate obligations. -/
inductive TransitionEvidence (overlap alignment : Prop) where
  | supplied : overlap → alignment → TransitionEvidence overlap alignment
  | missingOverlap : TransitionEvidence overlap alignment
  | missingAlignment : overlap → TransitionEvidence overlap alignment

structure TransitionProof (overlap alignment : Prop) : Type where
  overlapProof : overlap
  alignmentProof : alignment

def transition {overlap alignment : Prop} :
    TransitionEvidence overlap alignment →
      Decision (TransitionProof overlap alignment)
  | .supplied overlapProof alignmentProof =>
      .accepted ⟨overlapProof, alignmentProof⟩
  | .missingOverlap => .rejected .chartOverlap
  | .missingAlignment _ => .rejected .branchAlignment

@[simp] theorem transition_missing_overlap {overlap alignment : Prop} :
    (transition (overlap := overlap) (alignment := alignment)
      .missingOverlap).missing? = some .chartOverlap := rfl

@[simp] theorem transition_missing_alignment {overlap alignment : Prop}
    (overlapProof : overlap) :
    (transition (.missingAlignment overlapProof :
      TransitionEvidence overlap alignment)).missing? =
        some .branchAlignment := rfl

end CCL.ProgressivePartialCalculus
