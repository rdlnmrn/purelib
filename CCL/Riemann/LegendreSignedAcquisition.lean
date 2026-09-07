import CCL.Arithmetic.SignedDecision
import CCL.Progressive.BoundedDivision
import CCL.Riemann.LegendrePositivityAcquisition

/-!
# Bounded signed acquisition for Legendre input ratios

Requested-precision inspection always yields one of three mathematical
outcomes. The positive branch feeds the existing guaranteed word evaluators;
negative and near-boundary branches preserve their candidate evidence and
the exact state needed for subsequent work. A negative branch is not a
claim that all fractional transformations are undefined.
-/

namespace CCL.Riemann.LegendreSignedAcquisition

abbrev Q := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev State := CCL.Riemann.LegendrePositivityAcquisition.State
abbrev PositiveEnclosure := CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure
abbrev Word := CCL.Knot.FiniteBraid.Word 3

/-- Negative evidence refers to candidates, so its bound persists even when
future displayed balls are not contained in the inspected ball. -/
structure Negative (tau : CoherentNamed) (state : State tau) (delta : Q) : Type where
  upper : ∀ {value : Gaussian}, tau.name.process.Possible state.retained.source value →
    value.im ≤ -(delta / 4)

structure Near (tau : CoherentNamed) (state : State tau) (delta : Q) : Type where
  bounds : ∀ {value : Gaussian}, tau.name.process.Possible state.retained.source value →
    -delta < value.im ∧ value.im < delta

def Negative.after {tau : CoherentNamed} {first last : State tau} {delta : Q}
    (negative : Negative tau first delta)
    (persists : ∀ {value : Gaussian}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value) : Negative tau last delta :=
  ⟨fun possible => negative.upper (persists possible)⟩

def Near.after {tau : CoherentNamed} {first last : State tau} {delta : Q}
    (near : Near tau first delta)
    (persists : ∀ {value : Gaussian}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value) : Near tau last delta :=
  ⟨fun possible => near.bounds (persists possible)⟩

/-- Near-boundary evidence refutes a lower bound at this margin, not every
positive lower bound. The source equality makes the scope explicit. -/
theorem Near.incompatible_lower {tau : CoherentNamed} {state : State tau} {delta : Q}
    (near : Near tau state delta) (certificate : PositiveEnclosure tau)
    (source : certificate.state = state.retained.source)
    (large : delta ≤ certificate.lower) : False := by
  let witness := tau.name.process.witness state.retained.source
  have lower : certificate.lower ≤ witness.val.im := by
    apply certificate.inside_lower
    rw [source]
    exact tau.name.process.possible_inside witness.property
  exact (not_lt_of_ge (large.trans lower)) (near.bounds witness.property).2

/-- One cached requested-target inspection, with a whole-ball classification. -/
def Report (tau : CoherentNamed) (start : State tau) (delta : Q) (positive : 0 < delta) :=
  Sigma fun inspection : CCL.ProgressiveBoundedDivision.Inspection tau start.retained
      (delta ^ 2 / 16) (CCL.SignedDecision.target_positive positive) =>
    CCL.SignedDecision.Decision inspection.ball delta

def acquire (tau : CoherentNamed) (start : State tau) (delta : Q) (positive : 0 < delta) :
    Report tau start delta positive :=
  let inspection := CCL.ProgressiveBoundedDivision.request start.retained
    (delta ^ 2 / 16) (CCL.SignedDecision.target_positive positive)
  ⟨inspection, CCL.SignedDecision.decide inspection.ball delta positive inspection.accurate⟩

namespace Report

def retained {tau : CoherentNamed} {start : State tau} {delta : Q} {positive : 0 < delta}
    (report : Report tau start delta positive) : State tau :=
  { retained := report.1.retained
    ball := report.1.ball
    ball_eq := report.1.ball_eq }

theorem possible_at_start {tau : CoherentNamed} {start : State tau}
    {delta : Q} {positive : 0 < delta} (report : Report tau start delta positive)
    {value : Gaussian} (possible : tau.name.process.Possible report.retained.retained.source value) :
    tau.name.process.Possible start.retained.source value := report.1.possible_at_start possible

theorem nextIndex_eq {tau : CoherentNamed} {start : State tau}
    {delta : Q} {positive : 0 < delta} (report : Report tau start delta positive) :
    report.retained.retained.nextIndex = start.retained.nextIndex := report.1.index_eq

/-- The new positive test implies the original test and constructs precisely
the existing reusable enclosure, at the retained source. -/
def enclosure {tau : CoherentNamed} {start : State tau} {delta : Q} {positive : 0 < delta}
    (report : Report tau start delta positive) (high : delta / 2 < report.1.ball.center.im) :
    PositiveEnclosure tau :=
  CCL.Riemann.LegendrePositivityAcquisition.enclosure report.retained
    (CCL.SignedDecision.positive_test positive report.1.accurate high)

@[simp] theorem enclosure_source {tau : CoherentNamed} {start : State tau}
    {delta : Q} {positive : 0 < delta} (report : Report tau start delta positive)
    (high : delta / 2 < report.1.ball.center.im) :
    (report.enclosure high).state = report.retained.retained.source := rfl

def negative {tau : CoherentNamed} {start : State tau} {delta : Q} {positive : 0 < delta}
    (report : Report tau start delta positive)
    (upper : ∀ {value : Gaussian}, report.1.ball.Contains value → value.im ≤ -(delta / 4)) :
    Negative tau report.retained delta where
  upper := by
    intro value possible
    apply upper
    rw [report.1.ball_eq]
    exact tau.name.process.possible_inside possible

def near {tau : CoherentNamed} {start : State tau} {delta : Q} {positive : 0 < delta}
    (report : Report tau start delta positive)
    (bounds : ∀ {value : Gaussian}, report.1.ball.Contains value →
      -delta < value.im ∧ value.im < delta) : Near tau report.retained delta where
  bounds := by
    intro value possible
    apply bounds
    rw [report.1.ball_eq]
    exact tau.name.process.possible_inside possible

end Report

/-- Mathematical negative and tolerance-relative outcomes remain distinct.
This requested-accuracy API has no fuel-exhaustion constructor. -/
inductive OutcomePayload.{u} (readyType : Type u) (negativeType nearType : Type) : Type u
  | ready (result : readyType)
  | negative (certificate : negativeType)
  | near (certificate : nearType)

def Report.transport {tau : CoherentNamed} {start : State tau} {delta : Q} {positive : 0 < delta}
    (report : Report tau start delta positive) (word : Word) :
    OutcomePayload (CCL.Riemann.LegendreAutomaticTransport.Ready tau word)
      (Negative tau report.retained delta) (Near tau report.retained delta) :=
  match report.2 with
  | .positive high _ => .ready
      (CCL.Riemann.LegendreAutomaticTransport.guaranteed (report.enclosure high) word)
  | .negative _ upper => .negative (report.negative upper)
  | .near bounds => .near (report.near bounds)

def Report.fold {tau : CoherentNamed} {start : State tau} {delta : Q} {positive : 0 < delta}
    (report : Report tau start delta positive) (word : Word) :
    OutcomePayload (CCL.Riemann.LegendreGuaranteedFold.Prepared tau
        (CCL.Riemann.LegendreFractionalWords.periodBraidMatrices word))
      (Negative tau report.retained delta) (Near tau report.retained delta) :=
  match report.2 with
  | .positive high _ => .ready
      (CCL.Riemann.LegendreGuaranteedFold.prepareWord (report.enclosure high) word)
  | .negative _ upper => .negative (report.negative upper)
  | .near bounds => .near (report.near bounds)

end CCL.Riemann.LegendreSignedAcquisition
