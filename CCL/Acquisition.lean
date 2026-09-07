import CCL.Progressive.GapDivision
import CCL.Riemann.SquareRootDecisionLaws
import CCL.Riemann.LegendreSeparatedWords

/-!
# Finite certificate acquisition: public theorem interface

Three distinct contracts are exposed here, without a universal partiality
framework:

* `boundedDivision` makes one prescribed request and returns an ordinary
  cached quotient or whole-ball smallness with persistent candidate bounds.
* `gapDivision` turns smallness into exact branch exclusion under a proved
  zero-or-gap law. `signedGap` computes a sufficient canonical inspection
  budget from an unsigned imaginary gap.
* `exact` decides between an equivalent prepared presentation and operational
  zero for the two supported finite provenance classes. Its semantic iff
  and presentation-invariance laws do not apply to opaque inputs lacking
  this provenance, nor to the overlapping numerical small/apart verdicts.

`separatedWord` prepares an entire word in either half-plane and exposes
single/fold agreement, braid invariance, reversal, and the dual period law
through its retained report. Negative imaginary evidence is not global
non-certifiability. Precision and inspection counts below are not CPU-time,
allocation, certificate-size, or general-polynomial separation bounds.
-/

namespace CCL.FiniteAcquisition

abbrev Q := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev State := CCL.ProgressivePartialDivision.State

def State.initial (denominator : CoherentNamed) : State denominator :=
  CCL.ProgressivePartialDivision.State.initial denominator

/-- The original inspection and either a cached ordinary quotient or both
forms of smallness evidence. No additional refinement is hidden in a failed
branch, and the canonical retry index is preserved. -/
def BoundedResult (numerator denominator : CoherentNamed) (start : State denominator)
    (threshold : Q) (positive : 0 < threshold) :=
  Sigma fun report : CCL.ProgressiveBoundedDivision.Report denominator start threshold positive =>
    Sum (CCL.ProgressiveBoundedDivision.Quotient numerator denominator report.inspection.retained)
      { _small : CCL.ProgressiveBoundedDivision.Small denominator report.inspection.retained threshold //
        CCL.ResidualDecision.SmallBall report.inspection.ball threshold }

def boundedDivision (numerator : CoherentNamed) {denominator : CoherentNamed}
    (start : State denominator) (threshold : Q) (positive : 0 < threshold) :
    BoundedResult numerator denominator start threshold positive :=
  let report := CCL.ProgressiveBoundedDivision.acquire start threshold positive
  ⟨report, match selected : report.outcome with
    | .inl evidence => .inl
        (CCL.ProgressiveBoundedDivision.quotient numerator report.inspection.retained evidence)
    | .inr small => .inr ⟨small, report.small_ball small selected⟩⟩

/-- One-refinement provenance, requested precision, and operation-specific
soundness in one statement. Successful outputs carry the existing `Ready`
certificate, hence its automatic/manual output-compatibility laws. -/
theorem BoundedResult.spec {numerator denominator : CoherentNamed} {start : State denominator}
    {threshold : Q} {positive : 0 < threshold}
    (result : BoundedResult numerator denominator start threshold positive) :
    result.1.inspection.retained.source = denominator.name.process.refine start.source (threshold / 6)
        (CCL.ProgressiveBoundedDivision.requestTarget_positive positive) ∧
    result.1.inspection.retained.nextIndex = start.nextIndex ∧
    result.1.inspection.ball.radiusSq < threshold / 6 ∧
    match result.2 with
    | .inl ready => ready.output = CCL.ProgressivePartialDivision.readyName numerator denominator
        result.1.inspection.retained ready.valid.evidence
    | .inr _small => CCL.ResidualDecision.SmallBall result.1.inspection.ball threshold ∧
        ∀ (future : CCL.ProgressiveCharts.BasedState denominator.name.process
          result.1.inspection.retained.source) {value : Gaussian},
          denominator.name.process.Possible future.source value →
            RFAP.ConstructiveGaussian.Gaussian.normSq value < threshold := by
  refine ⟨result.1.inspection.source_eq, result.1.inspection.index_eq,
    result.1.inspection.accurate, ?_⟩
  cases result.2 with
  | inl ready => exact ready.valid.output_eq
  | inr small => exact ⟨small.property, fun future _value possible => small.val.at_future future possible⟩

def gapDivision {denominator : CoherentNamed} (start : State denominator)
    (gap : Q) (positive : 0 < gap) (certificate : CCL.ProgressiveGapDivision.Gap denominator start gap) :
    CCL.ProgressiveGapDivision.Report denominator start gap positive :=
  CCL.ProgressiveGapDivision.acquire start gap positive certificate

/-- Gap exclusion rules out every subsequent finite attempt on this
retained branch; it is not a reinterpretation of exhausted fuel. -/
theorem gapDivision_spec {denominator : CoherentNamed} (start : State denominator)
    (gap : Q) (positive : 0 < gap) (certificate : CCL.ProgressiveGapDivision.Gap denominator start gap) :
    let result := gapDivision start gap positive certificate
    match result.2 with
    | .prepared evidence => 0 < evidence.lowerSq
    | .excluded _ => ∀ (numerator : CoherentNamed) (fuel : Nat), ∃ final reachable,
        CCL.ProgressivePartialDivision.attempt numerator denominator result.1.retained fuel =
          .exhausted final reachable := by
  dsimp only
  cases (gapDivision start gap positive certificate).2 with
  | prepared evidence => exact evidence.positive
  | excluded zero => exact fun numerator fuel =>
      CCL.ProgressiveDivisionObstructions.ZeroCandidates.attempt_exhausts numerator _ zero fuel

def signedGap (tau : CoherentNamed) (start : CCL.Riemann.LegendrePositivityAcquisition.State tau)
    (delta : Q) (positive : 0 < delta) (gap : CCL.Riemann.LegendreSignedGap.Gap tau start delta) :
    CCL.Riemann.LegendreSignedGap.CanonicalReport tau start delta :=
  CCL.Riemann.LegendreSignedGap.canonical tau start delta positive gap

/-- Computed precision and refinement budget, plus success of the original
runner within one additional inspection or all-budget exclusion at the
retained negative endpoint. The sign is not an input. -/
theorem signedGap_spec (tau : CoherentNamed) (start : CCL.Riemann.LegendrePositivityAcquisition.State tau)
    (delta : Q) (positive : 0 < delta) (gap : CCL.Riemann.LegendreSignedGap.Gap tau start delta) :
    let result := signedGap tau start delta positive gap
    result.final = CCL.Riemann.LegendrePositivityAcquisition.advanceN start result.count ∧
    result.final.ball.radiusSq < delta ^ 2 / 16 ∧
    result.count ≤ Nat.log2 (RFAP.ConstructiveFraction.ceilNat (1 / (delta ^ 2 / 16))) + 2 ∧
    ((∃ certificate, CCL.Riemann.LegendrePositivityAcquisition.attempt tau start (result.count + 1) =
        .ready certificate) ∨
      (∀ fuel, CCL.Riemann.LegendrePositivityAcquisition.attempt tau result.final fuel =
        .exhausted (CCL.Riemann.LegendrePositivityAcquisition.advanceN result.final fuel))) := by
  let result := signedGap tau start delta positive gap
  refine ⟨result.final_eq, ?_, ?_, ?_⟩
  · rw [result.final_eq, result.count_eq]
    exact CCL.Riemann.LegendreSignedGap.canonical_accurate start delta positive
  · rw [result.count_eq]
    exact CCL.Riemann.LegendreSignedGap.canonicalCount_le start delta
  · cases result.outcome with
    | positive test =>
        let finished := result.finishPositive test
        exact .inl ⟨finished.val, finished.property⟩
    | negative certificate =>
        exact .inr (fun fuel => CCL.Riemann.LegendrePositivityObstructions.Nonpositive.attempt_exhausts
          result.final (CCL.Riemann.LegendrePositivityObstructions.nonpositive_of_negative
            positive certificate) fuel)

/-- A closed list of the supported finite provenance classes, not a
caller-supplied zero/prepared answer. Unsupported symbolic operations may
forget their sidecar but cannot construct one of these inputs without proof. -/
def Provenance (channel : CoherentNamed) :=
  Sum (CCL.ProgressiveExactProvenance.RationalSidecar channel)
    (CCL.Riemann.SquareRootProvenance.Sidecar channel)

def Provenance.rational {channel : CoherentNamed}
    (sidecar : CCL.ProgressiveExactProvenance.RationalSidecar channel) : Provenance channel := .inl sidecar

def Provenance.squareRoot {channel : CoherentNamed}
    (sidecar : CCL.Riemann.SquareRootProvenance.Sidecar channel) : Provenance channel := .inr sidecar

/-- Executable exact success-or-exclusion. A prepared result retains its
denominator, apartness, operational comparison, and productive quotient API. -/
def exact {channel : CoherentNamed} (provenance : Provenance channel) :
    CCL.ProgressiveExactProvenance.Decision channel :=
  match provenance with
  | .inl rational => rational.decide
  | .inr algebraic => algebraic.decide

/-- Exact obstruction completeness for supported provenance: zero means
there is no equivalent prepared presentation, not merely no certificate
found by one search. Both directions remain constructive. -/
theorem exact_complete {channel : CoherentNamed} (provenance : Provenance channel) :
    (CCL.ProgressiveExactProvenance.IsZero channel ↔ ¬ CCL.ProgressiveExactProvenance.IsPrepared channel) ∧
    (CCL.ProgressiveExactProvenance.IsPrepared channel ↔ ¬ CCL.ProgressiveExactProvenance.IsZero channel) :=
  ⟨(exact provenance).zero_iff_unpreparable, (exact provenance).prepared_iff_nonzero⟩

theorem exact_classifies {channel : CoherentNamed} (provenance : Provenance channel) :
    ((exact provenance).isPrepared = true ↔ CCL.ProgressiveExactProvenance.IsPrepared channel) ∧
    ((exact provenance).isPrepared = false ↔ CCL.ProgressiveExactProvenance.IsZero channel) :=
  ⟨(exact provenance).isPrepared_eq_true_iff, (exact provenance).isPrepared_eq_false_iff⟩

theorem exact_respects {first second : CoherentNamed}
    (left : Provenance first) (right : Provenance second)
    (equivalent : CCL.OperationalEquivalence.NamedEquivalent first.name second.name) :
    (exact left).isPrepared = (exact right).isPrepared := (exact left).respects (exact right) equivalent

/-- This comparison also covers independently prepared successful outputs
and equivalent numerator presentations. The preparations are reused. -/
def quotients_respect {first second firstNumerator secondNumerator : CoherentNamed}
    (left : CCL.ProgressiveExactProvenance.Prepared first)
    (right : CCL.ProgressiveExactProvenance.Prepared second)
    (denominators : CCL.OperationalEquivalence.NamedEquivalent first.name second.name)
    (numerators : CCL.OperationalEquivalence.NamedEquivalent firstNumerator.name secondNumerator.name) :
    CCL.OperationalEquivalence.NamedEquivalent
      (left.quotient firstNumerator).name (right.quotient secondNumerator).name :=
  left.quotient_respects_equivalent right denominators numerators

def separatedWord {tau : CoherentNamed}
    (separation : CCL.Riemann.LegendreSeparatedPreparation.Separation tau)
    (word : CCL.Knot.FiniteBraid.Word 3) : CCL.Riemann.LegendreSeparatedWords.Report tau word :=
  CCL.Riemann.LegendreSeparatedWords.acquire separation word

end CCL.FiniteAcquisition
