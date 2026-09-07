import CCL.Riemann.LegendrePositivityObstructions

/-!
# Quantitative signed completeness from an unsigned candidate gap

A persistent rational gap removes the near-boundary alternative without
supplying the sign. Both direct requested precision and a coefficient-bounded
canonical refinement schedule construct signed evidence. The canonical
positive result supplies a budget for the original positivity `attempt`.
-/

namespace CCL.Riemann.LegendreSignedGap

open CCL.Riemann.LegendrePositivityAcquisition

def Gap (tau : CoherentNamed) (state : State tau) (delta : Q) : Prop :=
  ∀ {value : Gaussian}, tau.name.process.Possible state.retained.source value →
    value.im ≤ -delta ∨ delta ≤ value.im

namespace Gap

theorem after {tau : CoherentNamed} {first last : State tau} {delta : Q}
    (gap : Gap tau first delta)
    (persists : ∀ {value : Gaussian}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value) : Gap tau last delta :=
  fun possible => gap (persists possible)

theorem advance {tau : CoherentNamed} {state : State tau} {delta : Q}
    (gap : Gap tau state delta) : Gap tau (CCL.Riemann.LegendrePositivityAcquisition.advance state) delta :=
  gap.after (fun possible => tau.name.process.refine_persists state.retained.source
    (CCL.ProgressiveSampling.refinementTarget state.retained.nextIndex)
    (CCL.ProgressiveSampling.refinementTarget_pos state.retained.nextIndex) possible)

theorem advanceN {tau : CoherentNamed} (state : State tau) {delta : Q}
    (gap : Gap tau state delta) (count : Nat) :
    Gap tau (CCL.Riemann.LegendrePositivityAcquisition.advanceN state count) delta := by
  induction count generalizing state with
  | zero => exact gap
  | succ count inductionHypothesis =>
      exact inductionHypothesis _ gap.advance

theorem incompatible_near {tau : CoherentNamed} {state : State tau} {delta : Q}
    (gap : Gap tau state delta)
    (near : CCL.Riemann.LegendreSignedAcquisition.Near tau state delta) : False := by
  let witness := tau.name.process.witness state.retained.source
  have bounds := near.bounds witness.property
  exact (gap witness.property).elim
    (not_le_of_gt bounds.1) (not_le_of_gt bounds.2)

end Gap

inductive Outcome (tau : CoherentNamed) (state : State tau) (delta : Q) : Type
  | positive (test : PositiveTest state.ball)
  | negative (certificate : CCL.Riemann.LegendreSignedAcquisition.Negative tau state delta)

/-- Remove only the alternative refuted by independent finite gap evidence. -/
def certify {tau : CoherentNamed} (state : State tau) (delta : Q) (positive : 0 < delta)
    (fine : state.ball.radiusSq < delta ^ 2 / 16) (gap : Gap tau state delta)
    (decision : CCL.SignedDecision.Decision state.ball delta) : Outcome tau state delta :=
  match decision with
  | .positive high _ => .positive (CCL.SignedDecision.positive_test positive fine high)
  | .negative _ upper => .negative
      { upper := by
          intro value possible
          apply upper
          rw [state.ball_eq]
          exact tau.name.process.possible_inside possible }
  | .near bounds => False.elim (Gap.incompatible_near gap
      { bounds := by
          intro value possible
          apply bounds
          rw [state.ball_eq]
          exact tau.name.process.possible_inside possible })

/-- Keep the requested-target report, its cached state, and the sharpened
two-way result. No sign is supplied by the caller. -/
def requested (tau : CoherentNamed) (start : State tau) (delta : Q) (positive : 0 < delta)
    (gap : Gap tau start delta) :
    Sigma fun report : CCL.Riemann.LegendreSignedAcquisition.Report tau start delta positive =>
      Outcome tau report.retained delta :=
  let report := CCL.Riemann.LegendreSignedAcquisition.acquire tau start delta positive
  ⟨report, certify report.retained delta positive report.1.accurate
    (Gap.after gap report.possible_at_start) report.2⟩

theorem advanceN_succ {tau : CoherentNamed} (state : State tau) (count : Nat) :
    advanceN state (count + 1) = advance (advanceN state count) := by
  induction count generalizing state with
  | zero => rfl
  | succ count inductionHypothesis =>
      exact inductionHypothesis (advance state)

theorem advanceN_nextIndex {tau : CoherentNamed} (state : State tau) (count : Nat) :
    (advanceN state count).retained.nextIndex = state.retained.nextIndex + count := by
  induction count generalizing state with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [advanceN, inductionHypothesis]
      change state.retained.nextIndex + 1 + count = state.retained.nextIndex + (count + 1)
      omega

theorem advanceN_accurate {tau : CoherentNamed} (state : State tau) (count : Nat) :
    (advanceN state (count + 1)).ball.radiusSq <
      CCL.ProgressiveSampling.refinementTarget (state.retained.nextIndex + count) := by
  rw [advanceN_succ]
  have accurate := tau.name.process.accurate (advanceN state count).retained.source
    (CCL.ProgressiveSampling.refinementTarget (advanceN state count).retained.nextIndex)
    (CCL.ProgressiveSampling.refinementTarget_pos (advanceN state count).retained.nextIndex)
  exact accurate.trans_le (le_of_eq (congrArg CCL.ProgressiveSampling.refinementTarget
    (advanceN_nextIndex state count)))

/-- A finite rational scan computes the number of canonical refinements.
The final extra unit performs the request at the selected small index. -/
def canonicalCount {tau : CoherentNamed} (state : State tau) (delta : Q) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow 1 state.retained.nextIndex (delta ^ 2 / 16) -
    state.retained.nextIndex + 1

theorem canonical_accurate {tau : CoherentNamed} (state : State tau)
    (delta : Q) (positive : 0 < delta) :
    (advanceN state (canonicalCount state delta)).ball.radiusSq < delta ^ 2 / 16 := by
  let index := CCL.FiniteGeometric.firstQuarterBelow 1 state.retained.nextIndex (delta ^ 2 / 16)
  have indexGe : state.retained.nextIndex ≤ index :=
    CCL.FiniteGeometric.firstQuarterBelow_ge _ _ _
  have indexEq : state.retained.nextIndex + (index - state.retained.nextIndex) = index := by omega
  have fine := advanceN_accurate state (index - state.retained.nextIndex)
  rw [indexEq] at fine
  exact fine.trans (CCL.FiniteGeometric.firstQuarterBelow_accurate 1 (by decide)
    state.retained.nextIndex (delta ^ 2 / 16) (CCL.SignedDecision.target_positive positive))

/-- Binary-length bound on the number of requested canonical refinements.
It is not a bound on the cost of each source refinement. -/
theorem canonicalCount_le {tau : CoherentNamed} (state : State tau) (delta : Q) :
    canonicalCount state delta ≤
      Nat.log2 (RFAP.ConstructiveFraction.ceilNat (1 / (delta ^ 2 / 16))) + 2 := by
  have bound := CCL.FiniteGeometric.firstQuarterBelow_le 1 state.retained.nextIndex (delta ^ 2 / 16)
  unfold canonicalCount
  omega

structure CanonicalReport (tau : CoherentNamed) (start : State tau) (delta : Q) where
  count : Nat
  count_eq : count = canonicalCount start delta
  final : State tau
  final_eq : final = advanceN start count
  outcome : Outcome tau final delta

def canonical (tau : CoherentNamed) (start : State tau) (delta : Q) (positive : 0 < delta)
    (gap : Gap tau start delta) : CanonicalReport tau start delta :=
  let count := canonicalCount start delta
  let final := advanceN start count
  let fine := canonical_accurate start delta positive
  { count := count
    count_eq := rfl
    final := final
    final_eq := rfl
    outcome := certify final delta positive fine (Gap.advanceN start gap count)
      (CCL.SignedDecision.decide final.ball delta positive fine) }

/-- The positive canonical result supplies an actual budget for the original
retryable positivity algorithm, which may stop earlier than the endpoint. -/
def CanonicalReport.finishPositive {tau : CoherentNamed} {start : State tau} {delta : Q}
    (report : CanonicalReport tau start delta) (test : PositiveTest report.final.ball) :
    { certificate : PositiveEnclosure tau //
      attempt tau start (report.count + 1) = .ready certificate } := by
  apply finishBy start report.count
  rw [← report.final_eq]
  exact test

def Outcome.isPositive {tau : CoherentNamed} {state : State tau} {delta : Q} :
    Outcome tau state delta → Bool
  | .positive _ => true
  | .negative _ => false

/-- The computed canonical budget either certifies success of the original
runner or supplies a persistent negative certificate at its endpoint. -/
def CanonicalReport.finish {tau : CoherentNamed} {start : State tau} {delta : Q}
    (report : CanonicalReport tau start delta) :
    Sum { certificate : PositiveEnclosure tau //
        attempt tau start (report.count + 1) = .ready certificate }
      (CCL.Riemann.LegendreSignedAcquisition.Negative tau report.final delta) :=
  match report.outcome with
  | .positive test => .inl (report.finishPositive test)
  | .negative certificate => .inr certificate

def Outcome.transport {tau : CoherentNamed} {state : State tau} {delta : Q}
    (outcome : Outcome tau state delta) (word : Word) :
    Sum (CCL.Riemann.LegendreAutomaticTransport.Ready tau word)
      (CCL.Riemann.LegendreSignedAcquisition.Negative tau state delta) :=
  match outcome with
  | .positive test => .inl
      (CCL.Riemann.LegendreAutomaticTransport.guaranteed (enclosure state test) word)
  | .negative certificate => .inr certificate

def Outcome.fold {tau : CoherentNamed} {state : State tau} {delta : Q}
    (outcome : Outcome tau state delta) (word : Word) :
    Sum (CCL.Riemann.LegendreGuaranteedFold.Prepared tau
        (CCL.Riemann.LegendreFractionalWords.periodBraidMatrices word))
      (CCL.Riemann.LegendreSignedAcquisition.Negative tau state delta) :=
  match outcome with
  | .positive test => .inl
      (CCL.Riemann.LegendreGuaranteedFold.prepareWord (enclosure state test) word)
  | .negative certificate => .inr certificate

end CCL.Riemann.LegendreSignedGap
