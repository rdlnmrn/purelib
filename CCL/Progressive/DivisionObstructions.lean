import CCL.Progressive.BoundedDivision

/-!
# Persistent exact-zero obstructions to division

This is extra finite input evidence, not an automatic interpretation of an
unsuccessful numerical test. The invariant is scoped to the retained source
and candidates with provenance back to it. A later numerical ball need not
have radius zero for the obstruction to remain valid.
-/

namespace CCL.ProgressiveDivisionObstructions

open CCL.ProgressiveBoundedDivision (Q Inspection)
open CCL.ProgressivePartialDivision
open RFAP.ConstructiveGaussian.Gaussian

/-- Strong exact-zero candidate evidence at one retained source. This is
distinct from operational equivalence to zero with approximate candidates. -/
def ZeroCandidates (denominator : CoherentNamed) (state : State denominator) : Prop :=
  ∀ {value : Gaussian}, denominator.name.process.Possible state.source value → value = 0

namespace ZeroCandidates

theorem after {denominator : CoherentNamed} {first last : State denominator}
    (zero : ZeroCandidates denominator first)
    (persists : ∀ {value : Gaussian}, denominator.name.process.Possible last.source value →
      denominator.name.process.Possible first.source value) : ZeroCandidates denominator last :=
  fun possible => zero (persists possible)

theorem advance {denominator : CoherentNamed} {state : State denominator}
    (zero : ZeroCandidates denominator state) : ZeroCandidates denominator state.advance :=
  zero.after (fun possible => denominator.name.process.refine_persists state.source
    (CCL.ProgressiveSampling.refinementTarget state.nextIndex)
    (CCL.ProgressiveSampling.refinementTarget_pos state.nextIndex) possible)

theorem reachable {denominator : CoherentNamed} {first last : State denominator}
    (zero : ZeroCandidates denominator first) (path : Reachable first last) :
    ZeroCandidates denominator last := zero.after path.possible_persists

theorem incompatible {denominator : CoherentNamed} {state : State denominator}
    (zero : ZeroCandidates denominator state)
    (evidence : PossibleApart (CCL.ProgressiveCharts.based denominator.name.process state.source)) :
    False := by
  let witness := denominator.name.process.witness state.source
  have lower := evidence.lower
    (CCL.ProgressiveCharts.BasedState.initial denominator.name.process state.source)
    witness.property
  rw [zero witness.property, normSq_zero] at lower
  exact (not_lt_of_ge lower) evidence.positive

theorem not_separated {denominator : CoherentNamed} {state : State denominator}
    (zero : ZeroCandidates denominator state) :
    ¬ 2 * (denominator.name.process.ball state.source).radiusSq <
      normSq (denominator.name.process.ball state.source).center :=
  fun separated => zero.incompatible (evidenceOfSeparation state separated)

theorem no_ready {numerator denominator : CoherentNamed} {first last : State denominator}
    (zero : ZeroCandidates denominator first) (path : Reachable first last)
    {output : CoherentNamed} (ready : Ready numerator denominator last output) : False :=
  ZeroCandidates.incompatible (ZeroCandidates.reachable zero path) ready.evidence

/-- Every finite automatic run exhausts with a genuine reachability witness.
It never returns a quotient from this exact-zero refinement branch. -/
theorem attempt_exhausts {denominator : CoherentNamed} (numerator : CoherentNamed)
    (state : State denominator) (zero : ZeroCandidates denominator state) (fuel : Nat) :
    ∃ final reachable,
      attempt numerator denominator state fuel = .exhausted final reachable := by
  induction fuel generalizing state with
  | zero => exact ⟨state, .refl state, rfl⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨final, path, exhausted⟩ := inductionHypothesis state.advance zero.advance
      exact ⟨final, .tail (.refined state) path,
        attempt_succ_eq_exhausted_of_step_progressed numerator denominator state state.advance
          final fuel (.refined state) path
          (step_eq_progressed_of_not_separated numerator denominator state zero.not_separated)
          exhausted⟩

/-- Arbitrary requested-target refinement also preserves the obstruction;
no canonical-step assertion is needed. -/
theorem requested {denominator : CoherentNamed} {state : State denominator}
    (zero : ZeroCandidates denominator state) {target : Q} {positive : 0 < target}
    (inspection : Inspection denominator state target positive) :
    ZeroCandidates denominator inspection.retained := zero.after inspection.possible_at_start

end ZeroCandidates

end CCL.ProgressiveDivisionObstructions
