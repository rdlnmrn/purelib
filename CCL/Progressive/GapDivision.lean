import CCL.Progressive.DivisionObstructions

/-!
# Exact finite division decisions from a candidate gap

The extra invariant supplies a positive rational exclusion zone for nonzero
candidates, without supplying the result of the decision. Requested-precision
smallness then forces zero; the other branch constructs ordinary apartness.
This candidate invariant is intentionally not asserted for arbitrary
approximate readings of an algebraic or operationally zero channel.
-/

namespace CCL.ProgressiveGapDivision

open CCL.ProgressivePartialDivision (CoherentNamed Gaussian State PossibleApart)
open CCL.ProgressiveBoundedDivision (Q Inspection Small requestTarget_positive)
open CCL.ProgressiveDivisionObstructions (ZeroCandidates)
open RFAP.ConstructiveGaussian.Gaussian

/-- An unsigned exclusion zone at one retained source. Different candidates
are not assumed in advance to choose the same side of the disjunction. -/
def Gap (denominator : CoherentNamed) (state : State denominator) (gap : Q) : Prop :=
  ∀ {value : Gaussian}, denominator.name.process.Possible state.source value →
    value = 0 ∨ gap ≤ normSq value

namespace Gap

theorem after {denominator : CoherentNamed} {first last : State denominator} {gap : Q}
    (certificate : Gap denominator first gap)
    (persists : ∀ {value : Gaussian}, denominator.name.process.Possible last.source value →
      denominator.name.process.Possible first.source value) : Gap denominator last gap :=
  fun possible => certificate (persists possible)

/-- The threshold-relative upper bound becomes exact negative evidence only
because the independent gap excludes the small nonzero alternative. -/
theorem zero_of_small {denominator : CoherentNamed} {state : State denominator} {gap : Q}
    (certificate : Gap denominator state gap) (small : Small denominator state gap) :
    ZeroCandidates denominator state :=
  fun possible => (certificate possible).resolve_right
    (not_le_of_gt (small.bound possible))

end Gap

inductive Outcome (denominator : CoherentNamed) (state : State denominator) : Type
  | prepared (evidence : PossibleApart
      (CCL.ProgressiveCharts.based denominator.name.process state.source))
  | excluded (zero : ZeroCandidates denominator state)

def Report (denominator : CoherentNamed) (start : State denominator)
    (gap : Q) (positive : 0 < gap) :=
  Sigma fun inspection : Inspection denominator start (gap / 6) (requestTarget_positive positive) =>
    Outcome denominator inspection.retained

/-- Total preparation-or-exclusion from finite gap information. There is no
small or exhausted branch, and the initial gap does not encode a chosen answer. -/
def acquire {denominator : CoherentNamed} (start : State denominator) (gap : Q)
    (positive : 0 < gap) (certificate : Gap denominator start gap) :
    Report denominator start gap positive :=
  let report := CCL.ProgressiveBoundedDivision.acquire start gap positive
  ⟨report.inspection, match report.outcome with
    | .inl evidence => .prepared evidence
    | .inr small => .excluded (Gap.zero_of_small
        (Gap.after certificate report.inspection.possible_at_start) small)⟩

def Outcome.isPrepared {denominator : CoherentNamed} {state : State denominator} :
    Outcome denominator state → Bool
  | .prepared _ => true
  | .excluded _ => false

/-- An exact exclusion rules out any later manually or automatically
supplied preparation on this branch, not just this particular detector. -/
theorem excluded_no_ready {numerator denominator : CoherentNamed}
    {first last : State denominator} (zero : ZeroCandidates denominator first)
    (path : CCL.ProgressivePartialDivision.Reachable first last) {output : CoherentNamed}
    (ready : CCL.ProgressivePartialDivision.Ready numerator denominator last output) : False :=
  CCL.ProgressiveDivisionObstructions.ZeroCandidates.no_ready zero path ready

end CCL.ProgressiveGapDivision
