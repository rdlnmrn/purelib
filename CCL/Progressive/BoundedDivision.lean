import CCL.Progressive.PartialDivision

/-!
# Requested-precision denominator acquisition

One prescribed source refinement followed by the audited small-or-apart
decision returns either candidate apartness or a persistent squared-norm
upper bound. Smallness is relative to a supplied threshold, not a zero test.
The ordinary canonical retry index is preserved: this is a requested-target
refinement, not a falsely labelled canonical `Progress` transition.
-/

namespace CCL.ProgressiveBoundedDivision

abbrev Q := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev State := CCL.ProgressivePartialDivision.State
abbrev BasedState := CCL.ProgressiveCharts.BasedState
abbrev PossibleApart := CCL.ProgressiveCharts.PossibleApart

open RFAP.ConstructiveGaussian.Gaussian

/-- Cached data from exactly one prescribed source refinement. Keeping the
source equality separate from the ball equality avoids recomputing either
executable object in downstream tests. -/
structure Inspection (denominator : CoherentNamed) (start : State denominator)
    (target : Q) (positive : 0 < target) where
  retained : State denominator
  source_eq : retained.source = denominator.name.process.refine start.source target positive
  index_eq : retained.nextIndex = start.nextIndex
  ball : Ball
  ball_eq : ball = denominator.name.process.ball retained.source

def request {denominator : CoherentNamed} (start : State denominator)
    (target : Q) (positive : 0 < target) : Inspection denominator start target positive :=
  let source := denominator.name.process.refine start.source target positive
  let retained : State denominator :=
    { source := source
      nextIndex := start.nextIndex
      persists := fun possible => start.persists
        (denominator.name.process.refine_persists start.source target positive possible) }
  { retained := retained
    source_eq := rfl
    index_eq := rfl
    ball := denominator.name.process.ball source
    ball_eq := rfl }

namespace Inspection

theorem possible_at_start {denominator : CoherentNamed} {start : State denominator}
    {target : Q} {positive : 0 < target}
    (inspection : Inspection denominator start target positive)
    {value : Gaussian} (possible : denominator.name.process.Possible
      inspection.retained.source value) :
    denominator.name.process.Possible start.source value := by
  rw [inspection.source_eq] at possible
  exact denominator.name.process.refine_persists start.source target positive possible

theorem accurate {denominator : CoherentNamed} {start : State denominator}
    {target : Q} {positive : 0 < target}
    (inspection : Inspection denominator start target positive) :
    inspection.ball.radiusSq < target := by
  rw [inspection.ball_eq, inspection.source_eq]
  exact denominator.name.process.accurate start.source target positive

def evidence {denominator : CoherentNamed} {start : State denominator}
    {target : Q} {positive : 0 < target}
    (inspection : Inspection denominator start target positive)
    (apart : CCL.ArithmeticEnclosures.Ball.Apart inspection.ball) :
    PossibleApart (CCL.ProgressiveCharts.based denominator.name.process
      inspection.retained.source) := by
  apply CCL.ProgressiveCharts.possibleApartOfBall
  rw [← inspection.ball_eq]
  exact apart

end Inspection

/-- A bound on candidates at one retained source, hence also on every based
future candidate. It does not assert that later enclosing balls are nested. -/
structure Small (denominator : CoherentNamed) (state : State denominator) (threshold : Q) : Type where
  bound : ∀ {value : Gaussian}, denominator.name.process.Possible state.source value →
    normSq value < threshold

namespace Small

theorem at_future {denominator : CoherentNamed} {state : State denominator}
    {threshold : Q} (small : Small denominator state threshold)
    (future : BasedState denominator.name.process state.source)
    {value : Gaussian} (possible : denominator.name.process.Possible future.source value) :
    normSq value < threshold := small.bound (future.persists possible)

def after {denominator : CoherentNamed} {first last : State denominator}
    {threshold : Q} (small : Small denominator first threshold)
    (persists : ∀ {value : Gaussian}, denominator.name.process.Possible last.source value →
      denominator.name.process.Possible first.source value) : Small denominator last threshold :=
  ⟨fun possible => small.bound (persists possible)⟩

/-- A threshold-relative obstruction, using an explicit finite candidate.
Smaller positive lower bounds are not ruled out. -/
theorem incompatible_lower {denominator : CoherentNamed} {state : State denominator}
    {threshold : Q} (small : Small denominator state threshold)
    (apart : PossibleApart (CCL.ProgressiveCharts.based denominator.name.process state.source))
    (large : threshold ≤ apart.lowerSq) : False := by
  let initial := CCL.ProgressiveCharts.BasedState.initial denominator.name.process state.source
  let witness := denominator.name.process.witness state.source
  have lower := apart.lower initial witness.property
  exact (not_lt_of_ge (large.trans lower)) (small.bound witness.property)

end Small

theorem requestTarget_positive {threshold : Q} (positive : 0 < threshold) :
    0 < threshold / 6 := RFAP.ConstructiveFraction.div_pos_direct positive (by decide)

/-- Both outcomes share the exact cached inspection; only the successful
branch carries candidate apartness. There is no unresolved outcome. -/
structure Report (denominator : CoherentNamed) (start : State denominator)
    (threshold : Q) (positive : 0 < threshold) where
  inspection : Inspection denominator start (threshold / 6) (requestTarget_positive positive)
  outcome : Sum
    (PossibleApart (CCL.ProgressiveCharts.based denominator.name.process inspection.retained.source))
    (Small denominator inspection.retained threshold)
  small_ball : ∀ certificate, outcome = .inr certificate →
    CCL.ResidualDecision.SmallBall inspection.ball threshold

/-- Consume an already cached fine inspection without another refinement. -/
def classify {denominator : CoherentNamed} {start : State denominator}
    (threshold : Q) (positive : 0 < threshold)
    (inspection : Inspection denominator start (threshold / 6) (requestTarget_positive positive)) :
    Report denominator start threshold positive :=
  { inspection := inspection
    outcome := match CCL.ResidualDecision.decide inspection.ball threshold positive
        inspection.accurate with
      | .small certificate => .inr
          { bound := by
              intro value possible
              apply CCL.ResidualDecision.normSq_lt_of_contains certificate
              rw [inspection.ball_eq]
              exact denominator.name.process.possible_inside possible }
      | .apart certificate => .inl (inspection.evidence certificate)
    small_ball := by
      intro small equal
      cases decision : CCL.ResidualDecision.decide inspection.ball threshold positive
          inspection.accurate with
      | small certificate => exact certificate
      | apart certificate =>
          rw [decision] at equal
          cases equal }

/-- The inspected ball retains its original whole-ball certificate. Only
the separately stored candidate bound is propagated to later sources;
their displayed balls need not be nested inside this one. -/
theorem Report.small_bound {denominator : CoherentNamed} {start : State denominator}
    {threshold : Q} {positive : 0 < threshold}
    (report : Report denominator start threshold positive)
    {certificate : Small denominator report.inspection.retained threshold}
    (selected : report.outcome = .inr certificate)
    {value : Gaussian} (inside : report.inspection.ball.Contains value) : normSq value < threshold :=
  CCL.ResidualDecision.normSq_lt_of_contains (report.small_ball certificate selected) inside

/-- One prescribed refinement, then one finite rational decision. This
counts refinement calls, not the runtime of the underlying evaluator. -/
def acquire {denominator : CoherentNamed} (start : State denominator)
    (threshold : Q) (positive : 0 < threshold) : Report denominator start threshold positive :=
  classify threshold positive (request start (threshold / 6) (requestTarget_positive positive))

theorem classify_small {denominator : CoherentNamed} {start : State denominator}
    (threshold : Q) (positive : 0 < threshold)
    (inspection : Inspection denominator start (threshold / 6) (requestTarget_positive positive))
    (small : CCL.ResidualDecision.SmallBall inspection.ball threshold) :
    ∃ certificate, (classify threshold positive inspection).outcome = .inr certificate := by
  unfold classify
  dsimp only
  rw [CCL.ResidualDecision.decide, dif_pos small]
  exact ⟨_, rfl⟩

theorem classify_apart {denominator : CoherentNamed} {start : State denominator}
    (threshold : Q) (positive : 0 < threshold)
    (inspection : Inspection denominator start (threshold / 6) (requestTarget_positive positive))
    (notSmall : ¬ CCL.ResidualDecision.SmallBall inspection.ball threshold) :
    ∃ evidence, (classify threshold positive inspection).outcome = .inl evidence := by
  unfold classify
  dsimp only
  rw [CCL.ResidualDecision.decide, dif_neg notSmall]
  exact ⟨_, rfl⟩

@[simp] theorem acquire_source {denominator : CoherentNamed} (start : State denominator)
    (threshold : Q) (positive : 0 < threshold) :
    (acquire start threshold positive).inspection.retained.source =
      denominator.name.process.refine start.source (threshold / 6)
        (requestTarget_positive positive) := rfl

@[simp] theorem acquire_nextIndex {denominator : CoherentNamed} (start : State denominator)
    (threshold : Q) (positive : 0 < threshold) :
    (acquire start threshold positive).inspection.retained.nextIndex = start.nextIndex := rfl

/-- Ordinary cached productive quotient, constructed only from positive
evidence at the exact retained state. -/
structure Quotient (numerator denominator : CoherentNamed) (state : State denominator) where
  output : CoherentNamed
  valid : CCL.ProgressivePartialDivision.Ready numerator denominator state output

def quotient {denominator : CoherentNamed} (numerator : CoherentNamed)
    (state : State denominator)
    (evidence : PossibleApart (CCL.ProgressiveCharts.based denominator.name.process state.source)) :
    Quotient numerator denominator state :=
  { output := CCL.ProgressivePartialDivision.readyName numerator denominator state evidence
    valid := { evidence := evidence, output_eq := rfl } }

def Quotient.respects {numerator denominator : CoherentNamed} {state other : State denominator}
    (result : Quotient numerator denominator state) {output : CoherentNamed}
    (ready : CCL.ProgressivePartialDivision.Ready numerator denominator other output) :
    CCL.OperationalEquivalence.NamedEquivalent result.output.name output.name :=
  CCL.ProgressivePartialDivision.ready_respects result.valid ready

/-- Successful reports construct the ordinary quotient; small reports retain
their mathematical upper bound instead of manufacturing a division. -/
def Report.divide {denominator : CoherentNamed} {start : State denominator}
    {threshold : Q} {positive : 0 < threshold}
    (report : Report denominator start threshold positive) (numerator : CoherentNamed) :
    Sum (Quotient numerator denominator report.inspection.retained)
      (Small denominator report.inspection.retained threshold) :=
  match report.outcome with
  | .inl evidence => .inl (quotient numerator report.inspection.retained evidence)
  | .inr small => .inr small

end CCL.ProgressiveBoundedDivision
