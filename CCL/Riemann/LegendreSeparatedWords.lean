import CCL.Riemann.LegendreSeparatedPreparation

/-!
# Automatically prepared words in either half-plane

The finite word fold consumes an unsigned separation provider. Its combined
denominator is reused by the single-matrix output instead of preparing it a
second time. Both outputs, the final provider, and reversal data remain
ordinary inputs to the established dual period-monodromy theorems.
-/

namespace CCL.Riemann.LegendreSeparatedWords

open CCL.Riemann.LegendreFractionalWords
open CCL.Riemann.LegendreModularMonodromy (Gaussian fractionalLinear)
open CCL.Riemann.LegendrePreparationClosure (Provider after mulInverse)
open CCL.Riemann.LegendreSeparatedPreparation (Separation)

abbrev Word := CCL.Knot.FiniteBraid.Word 3
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent

/-- Keep structure generation independent of the large evaluator indices,
as in the existing automatic-transport payloads. -/
structure ReportPayload.{u, v, w} (providerType : Type u) (foldedType : Type v) (singleType : Type w) where
  provider : providerType
  folded : foldedType
  single : singleType

def Report (tau : CoherentNamed) (word : Word) :=
  ReportPayload (Provider tau)
    (CCL.Riemann.LegendreGuaranteedFold.Prepared tau (periodBraidMatrices word))
    (CCL.Riemann.LegendreAutomaticTransport.Ready tau word)

/-- Reuse an already acquired all-row provider, including after an earlier
word. The combined preparation is not computed twice. -/
def acquireWithProvider {tau : CoherentNamed} (provider : Provider tau) (word : Word) : Report tau word :=
  let folded := CCL.Riemann.LegendreGuaranteedFold.prepare tau provider (periodBraidMatrices word)
    (CCL.Riemann.LegendreGuaranteedFold.periodInverses word)
  let matrix := matrixProduct (periodBraidMatrices word)
  let preparation := FoldPreparations.combined (periodBraidMatrices word) folded.1
  { provider := provider
    folded := folded
    single :=
      { matrix := matrix
        matrix_eq := matrixProduct_periodBraidMatrices word
        preparation := preparation
        output := fractionalLinear matrix tau preparation
        output_eq := rfl } }

/-- All local and combined preparations are generated from one unsigned
candidate gap. No sign or per-word denominator certificate is supplied. -/
def acquire {tau : CoherentNamed} (separation : Separation tau) (word : Word) : Report tau word :=
  acquireWithProvider (CCL.Riemann.LegendreSeparatedPreparation.provider separation) word

@[simp] theorem acquireWithProvider_reuses_provider {tau : CoherentNamed}
    (provider : Provider tau) (word : Word) : (acquireWithProvider provider word).provider = provider := rfl

@[simp] theorem acquireWithProvider_reuses_combined {tau : CoherentNamed}
    (provider : Provider tau) (word : Word) : (acquireWithProvider provider word).single.preparation =
      FoldPreparations.combined (periodBraidMatrices word) (acquireWithProvider provider word).folded.1 := rfl

@[simp] theorem acquire_reuses_combined {tau : CoherentNamed} (separation : Separation tau)
    (word : Word) : (acquire separation word).single.preparation =
      FoldPreparations.combined (periodBraidMatrices word) (acquire separation word).folded.1 := rfl

namespace Report

def output {tau : CoherentNamed} {word : Word} (report : Report tau word) : CoherentNamed :=
  foldAction tau (periodBraidMatrices word) report.folded.1

def equivalent_single {tau : CoherentNamed} {word : Word} (report : Report tau word) :
    NamedEquivalent report.single.output.name report.output.name :=
  report.single.equivalent_fold report.folded.1

/-- Compatibility with existing positive, automatic, and manual routes. -/
def respects_ready {tau : CoherentNamed} {word : Word} (report : Report tau word)
    (ready : CCL.Riemann.LegendreAutomaticTransport.Ready tau word) :
    NamedEquivalent report.output.name ready.output.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm report.equivalent_single)
    (report.single.respects ready)

def respects_braid {tau : CoherentNamed} {firstWord secondWord : Word}
    (first : Report tau firstWord) (second : Report tau secondWord)
    (relation : CCL.Knot.ArtinRelations.Equivalent firstWord secondWord) :
    NamedEquivalent first.output.name second.output.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm first.equivalent_single)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (first.single.respects_braid second.single relation) second.equivalent_single)

/-- Continue from the cached forward output/provider. The original forward
word is not rerun while constructing the inverse leg. -/
def prepareReversal {tau : CoherentNamed} {word : Word} (report : Report tau word) :
    FoldReversalPreparations (periodBraidMatrices word) (periodBraidMatrices word.inverse) tau :=
  let first := matrixProduct (periodBraidMatrices word)
  let second := matrixProduct (periodBraidMatrices word.inverse)
  let firstInverse := CCL.Riemann.LegendreGuaranteedFold.productInverse (periodBraidMatrices word)
    (CCL.Riemann.LegendreGuaranteedFold.periodInverses word)
  let secondInverse := CCL.Riemann.LegendreGuaranteedFold.productInverse
    (periodBraidMatrices word.inverse) (CCL.Riemann.LegendreGuaranteedFold.periodInverses word.inverse)
  let inner := FoldPreparations.combined (periodBraidMatrices word) report.folded.1
  { forward := report.folded.1
    reverse := (CCL.Riemann.LegendreGuaranteedFold.prepare report.output report.folded.2
      (periodBraidMatrices word.inverse)
      (CCL.Riemann.LegendreGuaranteedFold.periodInverses word.inverse)).1
    composition :=
      { inner := inner
        outer := after report.provider first firstInverse inner second secondInverse
        combined := report.provider (RFAP.ConstructiveFiniteMatrix.mul second first)
          (mulInverse secondInverse firstInverse) } }

def reversal {tau : CoherentNamed} {word : Word} (report : Report tau word) :
    NamedEquivalent
      (foldAction report.output (periodBraidMatrices word.inverse) report.prepareReversal.reverse).name
      tau.name := periodBraidWord_foldReversal word tau report.prepareReversal

/-- The arbitrary closed-path dual period equation needs separation, not an
extra sign claim. All period data and path hypotheses remain unchanged. -/
def transport {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : CCL.Riemann.LegendrePeriodMonodromy.NormalizedData frame)
    (path : CCL.Riemann.LegendrePaths.Path frame frame) (report : Report data.ratio path.word) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul (data.periods path 0) report.output).name
      (data.periods path 1).name := data.periodWord_productive_transport path report.folded.1

end Report

/-- Both signed outcomes support word evaluation. Only near-boundary
evidence is passed back without a preparation, and it remains inconclusive. -/
def acquireSigned {tau : CoherentNamed}
    {start : CCL.Riemann.LegendrePositivityAcquisition.State tau}
    {delta : CCL.Riemann.LegendreAutomaticPreparation.Q} {positive : 0 < delta}
    (report : CCL.Riemann.LegendreSignedAcquisition.Report tau start delta positive) (word : Word) :
    Sum (Report tau word) (CCL.Riemann.LegendreSignedAcquisition.Near tau report.retained delta) :=
  match report.2 with
  | .positive high _ => .inl (acquire (Separation.ofPositive (report.enclosure high)) word)
  | .negative _ upper => .inl (acquire (Separation.ofNegative positive (report.negative upper)) word)
  | .near bounds => .inr (report.near bounds)

end CCL.Riemann.LegendreSeparatedWords
