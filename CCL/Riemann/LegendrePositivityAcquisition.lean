import CCL.Riemann.LegendreGuaranteedFold

/-!
# Automatic discovery of the initial positive enclosure

A cached rational ball passes when its centre is above the real axis and its
squared radius is below the squared half-height. The soundness proof gives a
positive imaginary lower bound for every point in that ball. Failed tests
perform one canonical finite refinement; bounded runs retain their exact
state on exhaustion and never infer a negative positivity verdict.
-/

namespace CCL.Riemann.LegendrePositivityAcquisition

abbrev Q := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev PositiveEnclosure := CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure
abbrev Word := CCL.Knot.FiniteBraid.Word 3

/-- A sufficient, decidable rational test, with no square root calculation. -/
def PositiveTest (ball : Ball) : Prop :=
  0 < ball.center.im ∧ ball.radiusSq < (ball.center.im / 2) ^ 2

instance (ball : Ball) : Decidable (PositiveTest ball) :=
  inferInstanceAs (Decidable (0 < ball.center.im ∧ ball.radiusSq < (ball.center.im / 2) ^ 2))

theorem half_positive {ball : Ball} (test : PositiveTest ball) :
    0 < ball.center.im / 2 :=
  RFAP.ConstructiveFraction.div_pos_direct test.1 (by decide)

/-- Every rational reading in a passing ball has at least half the positive
centre height. This is whole-ball evidence, not just a centre observation. -/
theorem positiveTest_sound {ball : Ball} (test : PositiveTest ball)
    {value : Gaussian} (inside : ball.Contains value) :
    ball.center.im / 2 ≤ value.im := by
  change (value.re - ball.center.re) ^ 2 + (value.im - ball.center.im) ^ 2 ≤
    ball.radiusSq at inside
  have squareLe : (value.im - ball.center.im) ^ 2 ≤ ball.radiusSq :=
    (le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct (value.re - ball.center.re))).trans inside
  have lower := RFAP.ConstructiveFraction.neg_le_of_sq_le_sq_direct
    (half_positive test).le (squareLe.trans_lt test.2).le
  calc
    ball.center.im / 2 = -(ball.center.im / 2) + (ball.center.im / 2) * 2 := by ring1
    _ = -(ball.center.im / 2) + ball.center.im := by
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ (by decide : (2 : Q) ≠ 0)]
    _ ≤ (value.im - ball.center.im) + ball.center.im :=
      RFAP.ConstructiveFraction.add_le_add_right_direct lower ball.center.im
    _ = value.im := by ring1

/-- The retained source includes candidate provenance and the next canonical
request index. The displayed ball is cached instead of recomputed for tests. -/
structure StatePayload (sourceType : Type) (ballAt : sourceType → Ball) where
  retained : sourceType
  ball : Ball
  ball_eq : ball = ballAt retained

def State (tau : CoherentNamed) :=
  StatePayload (CCL.ProgressivePartialDivision.State tau)
    (fun retained => tau.name.process.ball retained.source)

def cache (tau : CoherentNamed) (retained : CCL.ProgressivePartialDivision.State tau) :
    State tau :=
  { retained := retained
    ball := tau.name.process.ball retained.source
    ball_eq := rfl }

def initial (tau : CoherentNamed) : State tau :=
  cache tau (CCL.ProgressivePartialDivision.State.initial tau)

def advance {tau : CoherentNamed} (state : State tau) : State tau :=
  cache tau state.retained.advance

/-- Every retained search candidate preserves its original input provenance. -/
theorem possible_at_initial {tau : CoherentNamed} (state : State tau)
    {value : Gaussian} (possible : tau.name.process.Possible state.retained.source value) :
    tau.name.process.Possible tau.name.state value := state.retained.persists possible

def enclosure {tau : CoherentNamed} (state : State tau)
    (test : PositiveTest state.ball) : PositiveEnclosure tau where
  state := state.retained.source
  lower := state.ball.center.im / 2
  positive := half_positive test
  inside_lower := by
    intro value inside
    rw [← state.ball_eq] at inside
    exact positiveTest_sound test inside

/-- One finite inspection either discovers the reusable positive enclosure
or refines the retained source once. No exclusion case is manufactured. -/
def inspect (tau : CoherentNamed) (state : State tau) :
    Sum (PositiveEnclosure tau) (State tau) :=
  if test : PositiveTest state.ball then .inl (enclosure state test)
  else .inr (advance state)

theorem inspect_of_positive {tau : CoherentNamed} (state : State tau)
    (test : PositiveTest state.ball) :
    inspect tau state = .inl (enclosure state test) := by
  rw [inspect, dif_pos test]

theorem inspect_of_unresolved {tau : CoherentNamed} (state : State tau)
    (unresolved : ¬ PositiveTest state.ball) :
    inspect tau state = .inr (advance state) := by
  rw [inspect, dif_neg unresolved]

def Result (tau : CoherentNamed) : Type :=
  CCL.Riemann.LegendreAutomaticTransport.ResultPayload.{0, 0}
    (PositiveEnclosure tau) (State tau)

/-- Bounded discovery reuses the same finite runner as single-matrix
acquisition. A caller can resume an exhausted result at exactly its state. -/
def attempt (tau : CoherentNamed) (state : State tau) (fuel : Nat) : Result tau :=
  CCL.Riemann.LegendreAutomaticTransport.runPayload (inspect tau) state fuel

@[simp] theorem attempt_zero (tau : CoherentNamed) (state : State tau) :
    attempt tau state 0 = .exhausted state := rfl

theorem attempt_add (tau : CoherentNamed) (state : State tau) (first second : Nat) :
    attempt tau state (first + second) =
      match attempt tau state first with
      | .ready certificate => .ready certificate
      | .exhausted retained => attempt tau retained second := by
  unfold Result
  have law := CCL.Riemann.LegendreAutomaticTransport.runPayload_add
    (inspect tau) state first second
  cases firstRun : CCL.Riemann.LegendreAutomaticTransport.runPayload (inspect tau) state first <;>
    simpa only [attempt, firstRun] using law

/-- A displayed passing state needs exactly one inspection to finish. -/
theorem attempt_one_of_positive {tau : CoherentNamed} (state : State tau)
    (test : PositiveTest state.ball) :
    attempt tau state 1 = .ready (enclosure state test) := by
  unfold attempt
  rw [CCL.Riemann.LegendreAutomaticTransport.runPayload, inspect_of_positive state test]

theorem attempt_succ_of_positive {tau : CoherentNamed} (state : State tau)
    (test : PositiveTest state.ball) (fuel : Nat) :
    attempt tau state (fuel + 1) = .ready (enclosure state test) := by
  unfold attempt
  rw [CCL.Riemann.LegendreAutomaticTransport.runPayload, inspect_of_positive state test]

theorem attempt_succ_of_unresolved {tau : CoherentNamed} (state : State tau)
    (unresolved : ¬ PositiveTest state.ball) (fuel : Nat) :
    attempt tau state (fuel + 1) = attempt tau (advance state) fuel := by
  unfold attempt
  rw [CCL.Riemann.LegendreAutomaticTransport.runPayload, inspect_of_unresolved state unresolved]

/-- A displayed finite schedule of canonical source refinements. -/
def advanceN {tau : CoherentNamed} (state : State tau) : Nat → State tau
  | 0 => state
  | count + 1 => advanceN (advance state) count

/-- A finite passing-state witness gives a certified sufficient budget.
The algorithm may stop earlier; no infinitary fairness assumption is used. -/
def finishBy {tau : CoherentNamed} (state : State tau) :
    (count : Nat) → PositiveTest (advanceN state count).ball →
      { certificate : PositiveEnclosure tau //
        attempt tau state (count + 1) = .ready certificate }
  | 0, test => ⟨enclosure state test, attempt_one_of_positive state test⟩
  | count + 1, test => by
      by_cases now : PositiveTest state.ball
      · exact ⟨enclosure state now, attempt_succ_of_positive state now (count + 1)⟩
      · let later := finishBy (advance state) count test
        exact ⟨later.val,
          (attempt_succ_of_unresolved state now (count + 1)).trans later.property⟩

/-- Discover positivity, then prepare the final matrix and productive output.
The caller supplies only the input, word, retained state, and finite budget. -/
def attemptTransport (tau : CoherentNamed) (word : Word) (state : State tau) (fuel : Nat) :
    CCL.Riemann.LegendreAutomaticTransport.ResultPayload
      (CCL.Riemann.LegendreAutomaticTransport.Ready tau word) (State tau) :=
  match attempt tau state fuel with
  | .ready positive => .ready (CCL.Riemann.LegendreAutomaticTransport.guaranteed positive word)
  | .exhausted retained => .exhausted retained

/-- The same discovered enclosure also prepares the entire dependent fold
and its final preparation provider, without further positivity searches. -/
def attemptFold (tau : CoherentNamed) (word : Word) (state : State tau) (fuel : Nat) :
    CCL.Riemann.LegendreAutomaticTransport.ResultPayload
      (CCL.Riemann.LegendreGuaranteedFold.Prepared tau
        (CCL.Riemann.LegendreFractionalWords.periodBraidMatrices word)) (State tau) :=
  match attempt tau state fuel with
  | .ready positive => .ready (CCL.Riemann.LegendreGuaranteedFold.prepareWord positive word)
  | .exhausted retained => .exhausted retained

end CCL.Riemann.LegendrePositivityAcquisition
