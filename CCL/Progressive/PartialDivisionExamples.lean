import CCL.Progressive.PartialDivisionOutput

/-!
# Executable examples for retryable division preflight

The delayed-one process intentionally begins with a ball too coarse for the
automatic apartness test.  Its first finite refinement changes to an exact
ball at one.  This witnesses the semantic distinction between progress,
budget exhaustion, and readiness without using a completed value or an
unbounded search.
-/

namespace CCL.ProgressivePartialDivisionExamples

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Coherent := CCL.ProgressiveCoherence.Coherent
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed

open RFAP.ConstructiveGaussian.Gaussian
open CCL.ProgressivePartialDivision

/-- A finite process for the exact rational one whose initial enclosure is
deliberately coarse and whose first refinement is exact. -/
def delayedOneProcess : Process where
  State := Bool
  ball state :=
    if state = true then
      { center := 1
        radiusSq := 0
        radiusSq_nonneg := le_rfl }
    else
      { center := 0
        radiusSq := 1
        radiusSq_nonneg := by decide }
  Possible _ candidate := candidate = 1
  witness _ := ⟨1, rfl⟩
  possible_inside := by
    intro state candidate equal
    subst candidate
    cases state <;> decide
  refine _ _ _ := true
  refine_persists := by
    intro state target positive candidate possible
    exact possible
  accurate := by
    intro state target positive
    exact positive
  centerBound := 1
  centerBound_nonneg := by decide
  center_bounded := by
    intro state
    cases state <;> decide

def delayedOneAllowance : Bool → Coordinate
  | false => 1
  | true => 0

/-- The delayed process is coherent: every possible reading is exactly one,
and the semantic allowance drops from one to zero at its first refinement. -/
def delayedOneCoherent : Coherent delayedOneProcess where
  allowance := delayedOneAllowance
  allowance_nonneg := by
    intro state
    cases state <;> decide
  ball_radius_le := by
    intro state
    cases state <;> decide
  possible_close := by
    intro leftState rightState leftValue rightValue leftEqual rightEqual
    subst leftValue
    subst rightValue
    cases leftState <;> cases rightState <;> decide
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact positive

/-- The named delayed-one channel starts at its deliberately coarse state. -/
def delayedOne : CoherentNamed where
  name := { process := delayedOneProcess, state := false }
  coherent := delayedOneCoherent

/-- The initial ball cannot pass centre separation, so automatic preflight
returns certified progress rather than a false domain verdict. -/
theorem delayedOne_first_step_progresses (numerator : CoherentNamed) :
    step numerator delayedOne (State.initial delayedOne) =
      .progressed (State.initial delayedOne).advance
        (.refined (State.initial delayedOne)) := by
  apply step_eq_progressed_of_not_separated
  decide

/-- After that retained refinement, the exact ball at one passes the rational
test and the next automatic call returns an ordinary total quotient. -/
theorem delayedOne_second_step_ready (numerator : CoherentNamed) :
    ∃ output : CoherentNamed, ∃ valid :
        Ready numerator delayedOne (State.initial delayedOne).advance output,
      step numerator delayedOne (State.initial delayedOne).advance =
        .ready output valid := by
  apply step_is_ready_of_separated
  decide

/-- Zero fuel exposes exhaustion at the unchanged retained state. -/
theorem delayedOne_zero_fuel_exhausted (numerator : CoherentNamed) :
    attempt numerator delayedOne (State.initial delayedOne) 0 =
      .exhausted (State.initial delayedOne)
        (.refl (State.initial delayedOne)) := rfl

/-- One unit of fuel performs the real refinement and then reports exhaustion
at the retained refined state; it does not discard that progress. -/
theorem delayedOne_one_fuel_exhausted (numerator : CoherentNamed) :
    attempt numerator delayedOne (State.initial delayedOne) 1 =
      .exhausted (State.initial delayedOne).advance
        (.tail (.refined (State.initial delayedOne))
          (.refl (State.initial delayedOne).advance)) := by
  rw [attempt, delayedOne_first_step_progresses]
  rfl

/-- Two units of fuel are enough for this explicit process: one performs the
refinement and the second observes the newly available certificate. -/
theorem delayedOne_two_fuel_ready (numerator : CoherentNamed) :
    ∃ output : CoherentNamed, ∃ valid :
        Ready numerator delayedOne (State.initial delayedOne).advance output,
      ∃ reachable : Reachable (State.initial delayedOne)
          (State.initial delayedOne).advance,
        attempt numerator delayedOne (State.initial delayedOne) 2 =
          .ready (State.initial delayedOne).advance reachable output valid := by
  rcases delayedOne_second_step_ready numerator with ⟨output, valid, ready⟩
  let reachable : Reachable (State.initial delayedOne)
      (State.initial delayedOne).advance :=
    .tail (.refined (State.initial delayedOne))
      (.refl (State.initial delayedOne).advance)
  have laterReady :
      attempt numerator delayedOne (State.initial delayedOne).advance 1 =
        .ready (State.initial delayedOne).advance
          (.refl (State.initial delayedOne).advance) output valid :=
    attempt_succ_eq_ready_of_step_ready numerator delayedOne
      (State.initial delayedOne).advance 0 output valid ready
  have result := attempt_succ_eq_ready_of_step_progressed
    numerator delayedOne (State.initial delayedOne)
    (State.initial delayedOne).advance (State.initial delayedOne).advance
    1 (.refined (State.initial delayedOne))
    (.refl (State.initial delayedOne).advance) output valid
    (delayedOne_first_step_progresses numerator) laterReady
  exact ⟨output, valid, reachable, result⟩

end CCL.ProgressivePartialDivisionExamples
