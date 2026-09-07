import CCL.Riemann.LegendreSignedAcquisition

/-!
# Persistent obstructions to upper-half-plane positivity

Nonpositive candidates refute positive enclosures only at the same source or
states with explicit provenance back to it. This does not refute arbitrary
fractional transformations, and does not assume nested enclosing balls.
-/

namespace CCL.Riemann.LegendrePositivityObstructions

open CCL.Riemann.LegendrePositivityAcquisition

def Nonpositive (tau : CoherentNamed) (state : State tau) : Prop :=
  ∀ {value : Gaussian}, tau.name.process.Possible state.retained.source value → value.im ≤ 0

namespace Nonpositive

theorem after {tau : CoherentNamed} {first last : State tau}
    (nonpositive : Nonpositive tau first)
    (persists : ∀ {value : Gaussian}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value) : Nonpositive tau last :=
  fun possible => nonpositive (persists possible)

theorem advance {tau : CoherentNamed} {state : State tau} (nonpositive : Nonpositive tau state) :
    Nonpositive tau (CCL.Riemann.LegendrePositivityAcquisition.advance state) :=
  nonpositive.after (fun possible => tau.name.process.refine_persists state.retained.source
    (CCL.ProgressiveSampling.refinementTarget state.retained.nextIndex)
    (CCL.ProgressiveSampling.refinementTarget_pos state.retained.nextIndex) possible)

theorem incompatible {tau : CoherentNamed} {state : State tau}
    (nonpositive : Nonpositive tau state) (certificate : PositiveEnclosure tau)
    (source : certificate.state = state.retained.source) : False := by
  let witness := tau.name.process.witness state.retained.source
  have lower : certificate.lower ≤ witness.val.im := by
    apply certificate.inside_lower
    rw [source]
    exact tau.name.process.possible_inside witness.property
  exact (not_lt_of_ge (nonpositive witness.property)) (certificate.positive.trans_le lower)

theorem incompatible_future {tau : CoherentNamed} {first last : State tau}
    (nonpositive : Nonpositive tau first)
    (persists : ∀ {value : Gaussian}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value)
    (certificate : PositiveEnclosure tau) (source : certificate.state = last.retained.source) :
    False := Nonpositive.incompatible (Nonpositive.after nonpositive persists) certificate source

theorem not_positiveTest {tau : CoherentNamed} {state : State tau}
    (nonpositive : Nonpositive tau state) : ¬ PositiveTest state.ball :=
  fun test => nonpositive.incompatible (enclosure state test) rfl

/-- A direct invariant proves exact exhaustion for every finite future
budget. This is stronger evidence than observing any number of failed tests. -/
theorem attempt_exhausts {tau : CoherentNamed} (state : State tau)
    (nonpositive : Nonpositive tau state) (fuel : Nat) :
    attempt tau state fuel = .exhausted (advanceN state fuel) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      rw [attempt_succ_of_unresolved state nonpositive.not_positiveTest fuel]
      exact inductionHypothesis (CCL.Riemann.LegendrePositivityAcquisition.advance state)
        nonpositive.advance

end Nonpositive

/-- The signed negative outcome supplies an actual obstruction to this
positivity requirement, while retaining the strictly negative margin. -/
theorem nonpositive_of_negative {tau : CoherentNamed} {state : State tau} {delta : Q}
    (positive : 0 < delta)
    (negative : CCL.Riemann.LegendreSignedAcquisition.Negative tau state delta) :
    Nonpositive tau state := by
  intro value possible
  have nonpositive : -(delta / 4) ≤ (0 : Q) := by
    simpa only [neg_zero] using RFAP.ConstructiveFraction.neg_le_neg_direct
      (CCL.SignedDecision.quarter_positive positive).le
  exact (negative.upper possible).trans nonpositive

end CCL.Riemann.LegendrePositivityObstructions
