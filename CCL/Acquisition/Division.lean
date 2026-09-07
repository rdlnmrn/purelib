import CCL.Acquisition.Expressions

/-!
# Evidence-directed division with reusable state

The dispatcher first reuses an exact decision, then tries inferred finite
provenance, then an optional proved candidate gap, and finally one bounded
numerical request. A small result is inconclusive, not zero. Gap exclusion
is explicitly scoped to the retained branch. Exact provenance concerns
operational identities and is never used as a pointwise candidate gap.

All routes return the retained state. Requested refinements preserve the
retry index and transport optional gap evidence. Exact decisions, including
negative ones, are cached for subsequent numerators and requests.
-/

namespace CCL.AcquisitionAutomation.Division

open CCL.FiniteAcquisition (Q Gaussian CoherentNamed State Provenance)
open CCL.ProgressiveExactProvenance (Prepared Decision ZeroIdentity NamedEquivalent)
open CCL.ProgressiveBoundedDivision (Inspection Small)

structure CandidateGap (channel : CoherentNamed) (state : State channel) where
  gap : Q
  positive : 0 < gap
  certificate : CCL.ProgressiveGapDivision.Gap channel state gap

def CandidateGap.after {channel : CoherentNamed} {first last : State channel}
    (gap : CandidateGap channel first)
    (persists : ∀ {value : Gaussian}, channel.name.process.Possible last.source value →
      channel.name.process.Possible first.source value) : CandidateGap channel last :=
  ⟨gap.gap, gap.positive, CCL.ProgressiveGapDivision.Gap.after gap.certificate persists⟩

structure Input (channel : CoherentNamed) where
  state : State channel
  provenance : Option (Provenance channel)
  cached : Option (Decision channel) := none
  gap : Option (CandidateGap channel state) := none

def start (input : Annotated) : Input input.channel :=
  { state := CCL.FiniteAcquisition.State.initial input.channel
    provenance := input.provenance }

inductive Route where
  | cached | symbolic | gap | numerical
  deriving DecidableEq

/-- The history records actual candidate persistence, not a falsely claimed
canonical refinement step. Optional provenance is kept unchanged. -/
structure Step {channel : CoherentNamed} (input : Input channel) where
  next : Input channel
  route : Route
  provenance_eq : next.provenance = input.provenance
  index_eq : next.state.nextIndex = input.state.nextIndex
  persists : ∀ {value : Gaussian}, channel.name.process.Possible next.state.source value →
    channel.name.process.Possible input.state.source value

def Step.unchanged {channel : CoherentNamed} (input : Input channel) (route : Route) : Step input :=
  ⟨input, route, rfl, rfl, fun possible => possible⟩

def Step.inspected {channel : CoherentNamed} (input : Input channel) (route : Route)
    {target : Q} {positive : 0 < target}
    (inspection : Inspection channel input.state target positive) : Step input :=
  { next :=
      { state := inspection.retained
        provenance := input.provenance
        cached := input.cached
        gap := input.gap.map fun gap => gap.after inspection.possible_at_start }
    route := route
    provenance_eq := rfl
    index_eq := inspection.index_eq
    persists := inspection.possible_at_start }

def Step.cache {channel : CoherentNamed} {input : Input channel}
    (step : Step input) (decision : Decision channel) : Step input :=
  { step with next := { step.next with cached := some decision } }

@[simp] theorem Step.cache_reuses {channel : CoherentNamed} {input : Input channel}
    (step : Step input) (decision : Decision channel) :
    (step.cache decision).next.cached = some decision := rfl

structure Quotient (numerator channel : CoherentNamed) where
  prepared : Prepared channel
  output : CoherentNamed
  output_eq : output = prepared.quotient numerator

def quotient {channel : CoherentNamed} (numerator : CoherentNamed) (prepared : Prepared channel) :
    Quotient numerator channel := ⟨prepared, prepared.quotient numerator, rfl⟩

def Quotient.respects {first second firstNumerator secondNumerator : CoherentNamed}
    (left : Quotient firstNumerator first) (right : Quotient secondNumerator second)
    (denominators : NamedEquivalent first.name second.name)
    (numerators : NamedEquivalent firstNumerator.name secondNumerator.name) :
    NamedEquivalent left.output.name right.output.name := by
  rw [left.output_eq, right.output_eq]
  exact CCL.FiniteAcquisition.quotients_respect left.prepared right.prepared denominators numerators

/-- Cache the inspected ball as well as its persistent candidate bound. -/
structure SmallCertificate (channel : CoherentNamed) (state : State channel) (threshold : Q) where
  ball : CCL.ArithmeticEnclosures.Ball
  ball_eq : ball = channel.name.process.ball state.source
  whole_ball : CCL.ResidualDecision.SmallBall ball threshold
  candidates : Small channel state threshold

inductive Outcome (numerator channel : CoherentNamed) (state : State channel) (threshold : Q) : Type 1
  | ready (result : Quotient numerator channel)
  | zero (identity : ZeroIdentity channel)
  | branchZero (certificate : CCL.ProgressiveDivisionObstructions.ZeroCandidates channel state)
  | small (certificate : SmallCertificate channel state threshold)

inductive Status where
  | ready | zero | branchZero | small
  deriving DecidableEq

def Outcome.status {numerator channel : CoherentNamed} {state : State channel} {threshold : Q} :
    Outcome numerator channel state threshold → Status
  | .ready _ => .ready
  | .zero _ => .zero
  | .branchZero _ => .branchZero
  | .small _ => .small

def Report (numerator : CoherentNamed) {channel : CoherentNamed} (input : Input channel) (threshold : Q) :=
  Sigma fun step : Step input => Outcome numerator channel step.next.state threshold

def fromDecision {channel : CoherentNamed} {input : Input channel} (numerator : CoherentNamed)
    (threshold : Q) (step : Step input) (decision : Decision channel) : Report numerator input threshold :=
  ⟨step.cache decision, match decision with
    | .prepared prepared => .ready (quotient numerator prepared)
    | .excluded zero => .zero zero⟩

def acquire (numerator : CoherentNamed) {channel : CoherentNamed} (input : Input channel)
    (threshold : Q) (positive : 0 < threshold) : Report numerator input threshold :=
  match input.cached with
  | some decision => fromDecision numerator threshold (Step.unchanged input .cached) decision
  | none => match input.provenance with
    | some provenance => fromDecision numerator threshold (Step.unchanged input .symbolic)
        (CCL.FiniteAcquisition.exact provenance)
    | none => match input.gap with
      | some gap =>
          let report := CCL.ProgressiveGapDivision.acquire input.state gap.gap gap.positive gap.certificate
          let step := Step.inspected input .gap report.1
          match report.2 with
          | .prepared evidence => fromDecision numerator threshold step
              (.prepared (Prepared.ofEvidence report.1.retained evidence))
          | .excluded zero => ⟨step, .branchZero zero⟩
      | none =>
          let report := CCL.ProgressiveBoundedDivision.acquire input.state threshold positive
          let step := Step.inspected input .numerical report.inspection
          match selected : report.outcome with
          | .inl evidence => fromDecision numerator threshold step
              (.prepared (Prepared.ofEvidence report.inspection.retained evidence))
          | .inr small => ⟨step, .small
              ⟨report.inspection.ball, report.inspection.ball_eq, report.small_ball small selected, small⟩⟩

def Report.resume {numerator channel : CoherentNamed} {input : Input channel} {threshold : Q}
    (report : Report numerator input threshold) (nextNumerator : CoherentNamed)
    (nextThreshold : Q) (positive : 0 < nextThreshold) : Report nextNumerator report.1.next nextThreshold :=
  acquire nextNumerator report.1.next nextThreshold positive

theorem acquire_cached (numerator : CoherentNamed) {channel : CoherentNamed} (input : Input channel)
    (threshold : Q) (positive : 0 < threshold) (decision : Decision channel)
    (cached : input.cached = some decision) :
    (acquire numerator input threshold positive).1.route = .cached ∧
    (acquire numerator input threshold positive).1.next.state = input.state := by
  unfold acquire
  rw [cached]
  exact ⟨rfl, rfl⟩

/-- Supported provenance always resolves the exact operational question;
the small and branch-only outcomes cannot occur on this route. -/
theorem acquire_symbolic_decisive (numerator : CoherentNamed) {channel : CoherentNamed}
    (input : Input channel) (threshold : Q) (positive : 0 < threshold)
    (provenance : Provenance channel) (uncached : input.cached = none)
    (inferred : input.provenance = some provenance) :
    (acquire numerator input threshold positive).2.status = .ready ∨
    (acquire numerator input threshold positive).2.status = .zero := by
  unfold acquire
  rw [uncached, inferred]
  dsimp only
  unfold fromDecision
  dsimp only
  cases CCL.FiniteAcquisition.exact provenance with
  | prepared prepared => exact .inl rfl
  | excluded zero => exact .inr rfl

/-- A computed zero sidecar is enough to route automatically to exact
exclusion. The caller supplies no operational identity to the dispatcher. -/
theorem start_rational_zero (numerator : CoherentNamed) (input : Annotated)
    (threshold : Q) (positive : 0 < threshold) (zero : input.rationalValue = some 0) :
    (acquire numerator (start input) threshold positive).2.status = .zero := by
  cases selected : input.provenance with
  | none => simp only [Annotated.rationalValue, selected] at zero; cases zero
  | some provenance =>
      cases provenance with
      | inr root => simp only [Annotated.rationalValue, selected] at zero; cases zero
      | inl rational =>
          have valueZero : rational.value = 0 := by
            apply Option.some.inj
            simpa only [Annotated.rationalValue, selected] using zero
          unfold acquire start
          dsimp only
          rw [selected]
          dsimp only
          dsimp only [CCL.FiniteAcquisition.exact]
          unfold CCL.ProgressiveExactProvenance.RationalSidecar.decide
          rw [dif_pos valueZero]
          rfl

/-- Uniform public contract: successful output, global operational
obstruction, branch-scoped obstruction, or persistent threshold smallness. -/
theorem Report.spec {numerator channel : CoherentNamed} {input : Input channel} {threshold : Q}
    (report : Report numerator input threshold) :
    report.1.next.provenance = input.provenance ∧
    report.1.next.state.nextIndex = input.state.nextIndex ∧
    match report.2 with
    | .ready result => result.output = result.prepared.quotient numerator
    | .zero _ => ∀ (state : State channel) (output : CoherentNamed),
        CCL.ProgressivePartialDivision.Ready numerator channel state output → False
    | .branchZero _ => ∀ (state : State channel),
        CCL.ProgressivePartialDivision.Reachable report.1.next.state state →
        ∀ (output : CoherentNamed), CCL.ProgressivePartialDivision.Ready numerator channel state output → False
    | .small _ => ∀ (future : CCL.ProgressiveCharts.BasedState channel.name.process
          report.1.next.state.source) {value : Gaussian},
        channel.name.process.Possible future.source value →
          RFAP.ConstructiveGaussian.Gaussian.normSq value < threshold := by
  refine ⟨report.1.provenance_eq, report.1.index_eq, ?_⟩
  cases report.2 with
  | ready result => exact result.output_eq
  | zero zero => exact fun _ _ ready => zero.no_ready ready
  | branchZero zero => exact fun _ path _ ready =>
      CCL.ProgressiveDivisionObstructions.ZeroCandidates.no_ready zero path ready
  | small small => exact fun future _value possible => small.candidates.at_future future possible

end CCL.AcquisitionAutomation.Division
