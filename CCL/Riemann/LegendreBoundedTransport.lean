import CCL.Progressive.BoundedDivision
import CCL.Riemann.LegendreAutomaticTransport

/-!
# Requested-precision Legendre denominator decisions

Unlike fuel exhaustion, the small branch carries a persistent mathematical
upper bound on the retained denominator candidates. The ready branch is the
same cached public result used by automatic and manual word transport, with
its existing output equation, transport witness, and schedule independence.
-/

namespace CCL.Riemann.LegendreBoundedTransport

abbrev Q := RFAP.ConstructiveFraction.Rational
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev Word := CCL.Knot.FiniteBraid.Word 3
abbrev State := CCL.Riemann.LegendreAutomaticTransport.State
abbrev Ready := CCL.Riemann.LegendreAutomaticTransport.Ready

open CCL.ProgressiveBoundedDivision
open CCL.Riemann.LegendreModularMonodromy

/-- Both branches retain the actual cached requested-target inspection. -/
def Report (tau : CoherentNamed) (word : Word) (start : State tau word)
    (threshold : Q) (positive : 0 < threshold) :=
  Sigma fun inspection : Inspection (fractionalDenominator start.matrix tau)
      start.search (threshold / 6) (requestTarget_positive positive) =>
    Sum (Ready tau word)
      { _certificate : Small (fractionalDenominator start.matrix tau) inspection.retained threshold //
        CCL.ResidualDecision.SmallBall inspection.ball threshold }

/-- Reuse the already folded matrix and inspect its denominator at a
prescribed accuracy. The threshold is not a fuel or runtime limit. -/
def acquire (tau : CoherentNamed) (word : Word) (start : State tau word)
    (threshold : Q) (positive : 0 < threshold) : Report tau word start threshold positive :=
  let report := CCL.ProgressiveBoundedDivision.acquire start.search threshold positive
  ⟨report.inspection, match selected : report.outcome with
    | .inl evidence => .inl (CCL.Riemann.LegendreAutomaticTransport.ready tau word
        { start with search := report.inspection.retained }
        (CCL.Riemann.LegendreDenominatorAcquisition.preparationAt start.matrix tau
          report.inspection.retained evidence))
    | .inr small => .inr ⟨small, report.small_ball small selected⟩⟩

/-- Resume ordinary canonical retries from the new source, preserving the
cached matrix and the not-yet-consumed canonical request index. -/
def Report.retained {tau : CoherentNamed} {word : Word} {start : State tau word}
    {threshold : Q} {positive : 0 < threshold}
    (report : Report tau word start threshold positive) : State tau word :=
  { start with search := report.1.retained }

@[simp] theorem Report.matrix_eq {tau : CoherentNamed} {word : Word} {start : State tau word}
    {threshold : Q} {positive : 0 < threshold}
    (report : Report tau word start threshold positive) : report.retained.matrix = start.matrix := rfl

theorem Report.nextIndex_eq {tau : CoherentNamed} {word : Word} {start : State tau word}
    {threshold : Q} {positive : 0 < threshold}
    (report : Report tau word start threshold positive) :
    report.retained.search.nextIndex = start.search.nextIndex := report.1.index_eq

end CCL.Riemann.LegendreBoundedTransport
