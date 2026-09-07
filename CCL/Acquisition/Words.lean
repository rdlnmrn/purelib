import CCL.Acquisition.Expressions

/-!
# Evidence-directed finite Legendre words

Reuse a cached provider or separation first. Nonreal rational provenance
automatically constructs and transports an all-row provider. Otherwise one
signed numerical inspection prepares either half-plane, or returns retained
near-boundary evidence. Nonzeroness of the input alone is not used as a
certificate for every intermediate word denominator. Real inputs and
unsupported symbolic provenance may remain inconclusive by this sufficient
test; this is not a decision procedure for each particular real word.
-/

namespace CCL.AcquisitionAutomation.Words

open CCL.FiniteAcquisition (Q Gaussian CoherentNamed Provenance)
open CCL.ProgressiveExactProvenance (RationalSidecar NamedEquivalent)
open CCL.Riemann.LegendreSeparatedPreparation (Separation)
open CCL.Riemann.LegendrePreparationClosure (Provider)
open CCL.Riemann.LegendrePositivityAcquisition (State)
abbrev Word := CCL.Riemann.LegendreSeparatedWords.Word

def denominatorComparison (matrix : CCL.Riemann.LegendreGaussManin.IntegralMatrix)
    {first second : CoherentNamed} (equivalent : NamedEquivalent first.name second.name) :
    NamedEquivalent
      (CCL.Riemann.LegendreModularMonodromy.fractionalDenominator matrix first).name
      (CCL.Riemann.LegendreModularMonodromy.fractionalDenominator matrix second).name := by
  have rows := CCL.Riemann.LegendreGaussManin.matrixAction_respects matrix
    (CCL.Riemann.LegendreFractionalAction.fractionalVector_respects equivalent)
  simpa only [CCL.Riemann.LegendreModularMonodromy.fractionalDenominator,
    CCL.Riemann.LegendreModularMonodromy.fractionalRow] using rows 0

def transportPreparation {first second : CoherentNamed}
    (prepared : CCL.Riemann.LegendreModularMonodromy.DenominatorPreparation second)
    (equivalent : NamedEquivalent first.name second.name) :
    CCL.Riemann.LegendreModularMonodromy.DenominatorPreparation first :=
  { prepared := prepared.prepared
    apart := prepared.apart
    equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans equivalent prepared.equivalent }

/-- Transport the provider, not a candidate bound, across an operational
identity. Approximate candidates need not equal the rational sidecar. -/
def transportProvider {first second : CoherentNamed} (provider : Provider second)
    (equivalent : NamedEquivalent first.name second.name) : Provider first :=
  fun matrix inverse => transportPreparation (provider matrix inverse)
    (denominatorComparison matrix equivalent)

def exactSeparation (value : Gaussian) (nonreal : value.im ≠ 0) :
    Separation (CCL.ProgressiveCoherence.CoherentNamed.exact value) :=
  Separation.ofAbsolute (CCL.ProgressiveCoherence.CoherentNamed.exact value).name.state
    |value.im| (abs_pos.mpr nonreal) (by
      intro candidate possible
      change candidate = value at possible
      subst candidate
      exact le_rfl)

def rationalProvider {channel : CoherentNamed} (sidecar : RationalSidecar channel)
    (nonreal : sidecar.value.im ≠ 0) : Provider channel :=
  transportProvider (CCL.Riemann.LegendreSeparatedPreparation.provider
    (exactSeparation sidecar.value nonreal)) sidecar.equivalent

/-- Unsupported provenance falls through to acquisition without asserting
that the function is real, zero, or unpreparable. -/
def inferredProvider {channel : CoherentNamed} : Option (Provenance channel) → Option (Provider channel)
  | some (.inl rational) => if nonreal : rational.value.im ≠ 0
      then some (rationalProvider rational nonreal) else none
  | _ => none

structure InputPayload.{u, v, w, x}
    (stateType : Type u) (provenanceType : Type v) (providerType : Type w) (separationType : Type x) where
  state : stateType
  provenance : Option provenanceType
  provider : Option providerType := none
  separation : Option separationType := none

def Input (tau : CoherentNamed) := InputPayload (State tau) (Provenance tau) (Provider tau) (Separation tau)

def start (input : Annotated) : Input input.channel :=
  { state := CCL.Riemann.LegendrePositivityAcquisition.initial input.channel
    provenance := input.provenance }

inductive Route where
  | cached | separation | rational | positive | negative | near
  deriving DecidableEq

structure Step {tau : CoherentNamed} (input : Input tau) where
  next : Input tau
  route : Route
  provenance_eq : next.provenance = input.provenance
  index_eq : next.state.retained.nextIndex = input.state.retained.nextIndex
  persists : ∀ {value : Gaussian}, tau.name.process.Possible next.state.retained.source value →
    tau.name.process.Possible input.state.retained.source value

def Step.unchanged {tau : CoherentNamed} (input : Input tau) (route : Route) : Step input :=
  ⟨input, route, rfl, rfl, fun possible => possible⟩

def Step.inspected {tau : CoherentNamed} (input : Input tau) (route : Route)
    {delta : Q} {positive : 0 < delta}
    (report : CCL.Riemann.LegendreSignedAcquisition.Report tau input.state delta positive) : Step input :=
  { next := { input with state := report.retained }
    route := route
    provenance_eq := rfl
    index_eq := report.nextIndex_eq
    persists := report.possible_at_start }

def Step.cache {tau : CoherentNamed} {input : Input tau} (step : Step input) (provider : Provider tau) :
    Step input := { step with next := { step.next with provider := some provider } }

inductive OutcomePayload.{u} (readyType : Type u) (nearType : Type) : Type u
  | ready (result : readyType)
  | near (certificate : nearType)

def Report {tau : CoherentNamed} (input : Input tau) (word : Word) (delta : Q) :=
  Sigma fun step : Step input => OutcomePayload (CCL.Riemann.LegendreSeparatedWords.Report tau word)
    (CCL.Riemann.LegendreSignedAcquisition.Near tau step.next.state delta)

def prepare {tau : CoherentNamed} {input : Input tau} (step : Step input)
    (provider : Provider tau) (word : Word) (delta : Q) : Report input word delta :=
  ⟨step.cache provider, .ready (CCL.Riemann.LegendreSeparatedWords.acquireWithProvider provider word)⟩

def numerical {tau : CoherentNamed} (input : Input tau) (word : Word) (delta : Q) (positive : 0 < delta) :
    Report input word delta :=
  let report := CCL.Riemann.LegendreSignedAcquisition.acquire tau input.state delta positive
  match report.2 with
  | .positive high _ => prepare (Step.inspected input .positive report)
      (CCL.Riemann.LegendreSeparatedPreparation.provider (Separation.ofPositive (report.enclosure high))) word delta
  | .negative _ upper => prepare (Step.inspected input .negative report)
      (CCL.Riemann.LegendreSeparatedPreparation.provider
        (Separation.ofNegative positive (report.negative upper))) word delta
  | .near bounds => ⟨Step.inspected input .near report, .near (report.near bounds)⟩

def acquire {tau : CoherentNamed} (input : Input tau) (word : Word) (delta : Q) (positive : 0 < delta) :
    Report input word delta :=
  match input.provider with
  | some provider => prepare (Step.unchanged input .cached) provider word delta
  | none => match input.separation with
    | some separation => prepare (Step.unchanged input .separation)
        (CCL.Riemann.LegendreSeparatedPreparation.provider separation) word delta
    | none => match inferredProvider input.provenance with
      | some provider => prepare (Step.unchanged input .rational) provider word delta
      | none => numerical input word delta positive

def Report.resume {tau : CoherentNamed} {input : Input tau} {word : Word} {delta : Q}
    (report : Report input word delta) (nextWord : Word) (nextDelta : Q) (positive : 0 < nextDelta) :
    Report report.1.next nextWord nextDelta := acquire report.1.next nextWord nextDelta positive

/-- Continue at the actual folded output, using its cached final provider.
This is distinct from evaluating another word at the original input. -/
def continueFrom {tau : CoherentNamed} {word : Word}
    (report : CCL.Riemann.LegendreSeparatedWords.Report tau word) : Input report.output :=
  { state := CCL.Riemann.LegendrePositivityAcquisition.initial report.output
    provenance := none
    provider := some report.folded.2 }

theorem Report.spec {tau : CoherentNamed} {input : Input tau} {word : Word} {delta : Q}
    (report : Report input word delta) :
    report.1.next.provenance = input.provenance ∧
    report.1.next.state.retained.nextIndex = input.state.retained.nextIndex ∧
    match report.2 with
    | .ready ready => Nonempty (NamedEquivalent ready.single.output.name ready.output.name)
    | .near _ => ∀ {value : Gaussian}, tau.name.process.Possible report.1.next.state.retained.source value →
        -delta < value.im ∧ value.im < delta := by
  refine ⟨report.1.provenance_eq, report.1.index_eq, ?_⟩
  cases report.2 with
  | ready ready => exact ⟨ready.equivalent_single⟩
  | near near => exact near.bounds

end CCL.AcquisitionAutomation.Words
