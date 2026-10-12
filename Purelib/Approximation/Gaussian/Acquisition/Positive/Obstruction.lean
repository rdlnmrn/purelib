module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Acquisition.Positive.Enclosure
public import Purelib.Approximation.Gaussian.Acquisition.Positive.Search
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
import Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Approximation.Gaussian.Process.Sampling

import Purelib.Data.Rat.Fraction.Order
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Control.FiniteRunner.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Positive

open Purelib.Approximation.Gaussian.Acquisition.State

open Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

section
@[expose] public section

/-!
# Persistent obstructions to upper-half-plane positivity

Nonpositive candidates refute positive enclosures only at the same source or
states with explicit provenance back to it. This does not refute arbitrary
fractional transformations, and does not assume nested enclosing balls.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction

/-- Every possible candidate at the exact retained acquisition source has nonpositive imaginary coordinate. -/
def Nonpositive (tau : Coherent.CoherentNamed)
  (state : Approximation.Gaussian.Acquisition.State tau) : Prop :=
  ∀ {value : Canonical}, tau.name.process.Possible state.retained.source value → value.im ≤ 0

namespace Nonpositive

/-- Nonpositive candidate evidence persists along the supplied backwards candidate transport. -/
theorem after {tau :
  Coherent.CoherentNamed} {first last : Approximation.Gaussian.Acquisition.State tau}
    (nonpositive : Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive tau first)
    (persists : ∀ {value : Canonical}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value) :
        Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive tau last :=
  fun possible => nonpositive (persists possible)

/-- Canonical acquisition refinement preserves nonpositive candidate evidence. -/
theorem advance {tau :
  Coherent.CoherentNamed} {state : Approximation.Gaussian.Acquisition.State tau} (nonpositive :
  Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive tau state) :
    Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive tau (State.advance state) :=
  nonpositive.after (fun possible => tau.name.process.refine_persists state.retained.source
    (Gaussian.Process.Sampling.refinementTarget state.retained.nextIndex)
    (Gaussian.Process.Sampling.refinementTarget_pos state.retained.nextIndex) possible)

/-- Nonpositive candidate evidence contradicts a positive enclosure at the same retained source. -/
theorem incompatible {tau :
  Coherent.CoherentNamed} {state : Approximation.Gaussian.Acquisition.State tau}
    (nonpositive : Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive tau state) (certificate :
      Positive.Basic.PositiveEnclosure tau)
    (source : certificate.state = state.retained.source) : False := by
  let witness := tau.name.process.witness state.retained.source
  have lower : certificate.lower ≤ witness.val.im := by
    apply certificate.inside_lower
    rw [source]
    exact tau.name.process.possible_inside witness.property
  exact (not_lt_of_ge (nonpositive witness.property)) (certificate.positive.trans_le lower)

/-- A positive enclosure at a later source contradicts nonpositive candidates with explicit provenance back to the
original source. -/
theorem incompatible_future {tau :
  Coherent.CoherentNamed} {first last : Approximation.Gaussian.Acquisition.State tau}
    (nonpositive : Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive tau first)
    (persists : ∀ {value : Canonical}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value)
    (certificate : Positive.Basic.PositiveEnclosure tau) (source : certificate.state = last.retained.source) :
    False := Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive.incompatible
      (Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive.after nonpositive persists) certificate
      source

/-- Nonpositive candidates prevent the cached ball from passing its positivity test. -/
theorem not_positiveTest {tau :
  Coherent.CoherentNamed} {state : Approximation.Gaussian.Acquisition.State tau}
    (nonpositive : Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive tau state) : ¬
      Positive.PositiveTest state.ball :=
  fun test => nonpositive.incompatible (Enclosure.enclosure state test) rfl

/-- A direct invariant proves exact exhaustion for every finite future budget. This is stronger evidence than observing
any number of failed tests. -/
theorem attempt_exhausts {tau :
  Coherent.CoherentNamed} (state : Approximation.Gaussian.Acquisition.State tau)
    (nonpositive : Approximation.Gaussian.Acquisition.Positive.Obstruction.Nonpositive tau state) (fuel : Nat) :
    Search.attempt tau state fuel = .exhausted (Schedule.advanceN state fuel) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      rw [Search.attempt_succ_of_unresolved state nonpositive.not_positiveTest fuel]
      exact inductionHypothesis (State.advance state)
        nonpositive.advance

end Nonpositive
end Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction

end
