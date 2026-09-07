import CCL.Progressive.DivisionObstructions

/-!
# Exact provenance and operational zero obstructions

Exact identities concern finite observation protocols, not equality of every
approximate candidate. One explicit comparison at an apartness lower bound
refutes an identity to zero. Rational provenance then gives exact division
decisions while leaving the original numerical channel unchanged.
-/

namespace CCL.ProgressiveExactProvenance

abbrev Q := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev Apart := CCL.ProgressiveTransducer.Named.Apart
abbrev State := CCL.ProgressivePartialDivision.State

open RFAP.ConstructiveGaussian.Gaussian

def ZeroIdentity (channel : CoherentNamed) :=
  NamedEquivalent channel.name (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name

/-- A prepared equivalent presentation need not have the same process states
or candidate predicate as the original channel. Both presentations are
retained, with their finite operational comparison. -/
structure Prepared (channel : CoherentNamed) where
  denominator : CoherentNamed
  apart : Apart denominator.name
  equivalent : NamedEquivalent channel.name denominator.name

namespace ZeroIdentity

/-- The contradiction uses one finite request at the supplied positive
apartness bound, not a completed value or an equality decision on readings. -/
theorem incompatible_apart {channel : CoherentNamed} (zero : ZeroIdentity channel)
    (apart : Apart channel.name) : False := by
  let comparison := zero.compare 0 0 apart.certificate.lowerSq apart.certificate.positive
  have close := comparison.close (Nat.le_refl comparison.leftIndex)
    (Nat.le_refl comparison.rightIndex)
  change normSq ((CCL.ProgressiveSampling.approximation channel.name).sample
    comparison.leftIndex - 0) < apart.certificate.lowerSq at close
  rw [RFAP.ConstructiveGaussian.Gaussian.sub_zero] at close
  exact (not_lt_of_ge (CCL.ProgressiveDivisionCongruence.sampled_lower channel apart
    comparison.leftIndex)) close

theorem incompatible_prepared {channel : CoherentNamed} (zero : ZeroIdentity channel)
    (prepared : Prepared channel) : False :=
  ZeroIdentity.incompatible_apart
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm prepared.equivalent) zero)
    prepared.apart

/-- This operational obstruction applies even at independently rebased
states; the existing based/apartified equivalence is the required bridge. -/
theorem no_evidence {channel : CoherentNamed} (zero : ZeroIdentity channel)
    (state : State channel)
    (evidence : CCL.ProgressiveCharts.PossibleApart
      (CCL.ProgressiveCharts.based channel.name.process state.source)) : False :=
  zero.incompatible_prepared
    { denominator := CCL.ProgressivePartialDivision.preparedDenominator state evidence
      apart := CCL.ProgressivePartialDivision.preparedApart state evidence
      equivalent := CCL.ProgressivePartialDivision.preparedDenominatorEquivalent state evidence }

theorem no_ready {numerator channel : CoherentNamed} (zero : ZeroIdentity channel)
    {state : State channel} {output : CoherentNamed}
    (ready : CCL.ProgressivePartialDivision.Ready numerator channel state output) : False :=
  zero.no_evidence state ready.evidence

theorem not_separated {channel : CoherentNamed} (zero : ZeroIdentity channel)
    (state : State channel) :
    ¬ 2 * (channel.name.process.ball state.source).radiusSq <
      normSq (channel.name.process.ball state.source).center :=
  fun separated => zero.no_evidence state
    (CCL.ProgressivePartialDivision.evidenceOfSeparation state separated)

theorem attempt_exhausts {channel : CoherentNamed} (zero : ZeroIdentity channel)
    (numerator : CoherentNamed) (state : State channel) (fuel : Nat) :
    ∃ final reachable, CCL.ProgressivePartialDivision.attempt numerator channel state fuel =
      .exhausted final reachable := by
  induction fuel generalizing state with
  | zero => exact ⟨state, .refl state, rfl⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨final, path, exhausted⟩ := inductionHypothesis state.advance
      exact ⟨final, .tail (.refined state) path,
        CCL.ProgressivePartialDivision.attempt_succ_eq_exhausted_of_step_progressed
          numerator channel state state.advance final fuel (.refined state) path
          (CCL.ProgressivePartialDivision.step_eq_progressed_of_not_separated
            numerator channel state (zero.not_separated state)) exhausted⟩

end ZeroIdentity

/-- Uniform apartness for a displayed exact Gaussian rational. -/
def exactApart (value : Gaussian) (nonzero : value ≠ 0) :
    Apart (CCL.ProgressiveCoherence.CoherentNamed.exact value).name where
  certificate :=
    { lowerSq := normSq value
      positive := normSq_pos nonzero
      lower := by
        intro state candidate inside
        change normSq (candidate - value) ≤ 0 at inside
        have differenceZero := normSq_eq_zero.mp
          (le_antisymm inside (normSq_nonneg _))
        have equal : candidate = value := sub_eq_zero.mp differenceZero
        rw [equal] }

/-- Numerical identity and exact rational data are stored separately. The
sidecar does not replace the original numerical channel. -/
structure RationalSidecar (channel : CoherentNamed) where
  value : Gaussian
  equivalent : NamedEquivalent channel.name (CCL.ProgressiveCoherence.CoherentNamed.exact value).name

def RationalSidecar.exact (value : Gaussian) :
    RationalSidecar (CCL.ProgressiveCoherence.CoherentNamed.exact value) :=
  ⟨value, CCL.OperationalEquivalence.NamedEquivalent.refl _⟩

def RationalSidecar.zero {channel : CoherentNamed} (identity : ZeroIdentity channel) :
    RationalSidecar channel := ⟨0, identity⟩

inductive Decision (channel : CoherentNamed) : Type 1
  | prepared (result : Prepared channel)
  | excluded (identity : ZeroIdentity channel)

/-- Decidability comes from the finite rational sidecar, not an equality
test on an opaque progressive channel. -/
def RationalSidecar.decide {channel : CoherentNamed} (sidecar : RationalSidecar channel) :
    Decision channel :=
  if zero : sidecar.value = 0 then
    .excluded (by unfold ZeroIdentity; simpa only [zero] using sidecar.equivalent)
  else .prepared
    { denominator := CCL.ProgressiveCoherence.CoherentNamed.exact sidecar.value
      apart := exactApart sidecar.value zero
      equivalent := sidecar.equivalent }

def Prepared.quotient {channel : CoherentNamed} (prepared : Prepared channel)
    (numerator : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.div numerator prepared.denominator prepared.apart

/-- Independently prepared equivalent presentations give the same quotient. -/
def Prepared.quotient_respects {channel : CoherentNamed} (first second : Prepared channel)
    (numerator : CoherentNamed) :
    NamedEquivalent (first.quotient numerator).name (second.quotient numerator).name :=
  CCL.ProgressiveDivisionCongruence.coherentDiv_respects numerator numerator
    first.denominator second.denominator first.apart second.apart
    (CCL.OperationalEquivalence.NamedEquivalent.refl _)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm first.equivalent) second.equivalent)

def Prepared.ofEvidence {channel : CoherentNamed} (state : State channel)
    (evidence : CCL.ProgressiveCharts.PossibleApart
      (CCL.ProgressiveCharts.based channel.name.process state.source)) : Prepared channel :=
  { denominator := CCL.ProgressivePartialDivision.preparedDenominator state evidence
    apart := CCL.ProgressivePartialDivision.preparedApart state evidence
    equivalent := CCL.ProgressivePartialDivision.preparedDenominatorEquivalent state evidence }

/-- Compatibility includes the existing automatic and manual `Ready` API. -/
def Prepared.quotient_respects_ready {channel numerator : CoherentNamed}
    (prepared : Prepared channel) {state : State channel} {output : CoherentNamed}
    (ready : CCL.ProgressivePartialDivision.Ready numerator channel state output) :
    NamedEquivalent (prepared.quotient numerator).name output.name := by
  rw [ready.output_eq]
  exact prepared.quotient_respects (Prepared.ofEvidence state ready.evidence) numerator

/-- Optional provenance can be forgotten without changing the channel or its
raw output. Unsupported operations need not fabricate symbolic information. -/
structure WithRationalSidecar where
  channel : CoherentNamed
  sidecar : Option (RationalSidecar channel)

def WithRationalSidecar.forget (input : WithRationalSidecar) : WithRationalSidecar :=
  { channel := input.channel, sidecar := none }

@[simp] theorem WithRationalSidecar.forget_channel (input : WithRationalSidecar) :
    input.forget.channel = input.channel := rfl

end CCL.ProgressiveExactProvenance
