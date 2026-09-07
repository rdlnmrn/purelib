import CCL.Progressive.GapDivision
import CCL.Riemann.LegendreBoundedTransport

/-! # Exact word-denominator decisions with a finite candidate gap -/

namespace CCL.Riemann.LegendreGapTransport

open CCL.Riemann.LegendreAutomaticTransport (CoherentNamed Word State Ready)
open CCL.Riemann.LegendreModularMonodromy (fractionalDenominator)
open CCL.ProgressiveBoundedDivision (Q Inspection requestTarget_positive)

inductive OutcomePayload.{u} (readyType : Type u) (exclusion : Prop) : Type u
  | ready (result : readyType)
  | excluded (certificate : exclusion)

def Report (tau : CoherentNamed) (word : Word) (start : State tau word)
    (gap : Q) (positive : 0 < gap) :=
  Sigma fun inspection : Inspection (fractionalDenominator start.matrix tau)
      start.search (gap / 6) (requestTarget_positive positive) =>
    OutcomePayload (Ready tau word)
      (CCL.ProgressiveDivisionObstructions.ZeroCandidates
        (fractionalDenominator start.matrix tau) inspection.retained)

/-- Only the structural gap, not the selected outcome, is an input. The
ready output retains the ordinary transport and equivalence theorems. -/
def acquire (tau : CoherentNamed) (word : Word) (start : State tau word)
    (gap : Q) (positive : 0 < gap)
    (certificate : CCL.ProgressiveGapDivision.Gap
      (fractionalDenominator start.matrix tau) start.search gap) :
    Report tau word start gap positive :=
  let report := CCL.ProgressiveGapDivision.acquire start.search gap positive certificate
  ⟨report.1, match report.2 with
    | .prepared evidence => .ready (CCL.Riemann.LegendreAutomaticTransport.ready tau word
        { start with search := report.1.retained }
        (CCL.Riemann.LegendreDenominatorAcquisition.preparationAt start.matrix tau
          report.1.retained evidence))
    | .excluded zero => .excluded zero⟩

end CCL.Riemann.LegendreGapTransport
