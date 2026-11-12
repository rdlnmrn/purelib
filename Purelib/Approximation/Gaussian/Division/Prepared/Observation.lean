module

public import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.Equivalence.Observation
public import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Based

/-! # Division preparation on an original retained observation state

The original channel and complete possible Reading remain inputs. Candidate
clearance is required only in that actual state. Its existing refinement
future and apartification supply productive division while preserving
candidate provenance to the unchanged input observation.
-/

public section

namespace Purelib.Approximation.Gaussian.Division.Prepared

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

variable {channel : CoherentNamed} (observed : Equivalence.Observation.Reading channel)
variable {floor : Rational} (positive : 0 < floor)
variable (lower : ∀ {candidate : Canonical}, channel.name.process.Possible observed.state candidate →
  floor ≤ Norm.Basic.normSq candidate)

/-- The exact observation's original refinement future has its supplied candidate floor at every actual state. -/
@[expose] def observationApart : Process.Apart.Possible.PossibleApart
    (Process.Based.based channel.name.process observed.state) where
  lowerSq := floor
  positive := positive
  lower := fun _ _ possible => lower (Process.Based.based_initial_persists _ _ possible)

/-- Prepare the original channel using clearance on this same retained possible observation state.

No observation, source process or original reading is acquired again. The
based future retains the input state and apartification refines that future;
the existing operational comparisons preserve the original named channel.
-/
def ofObservation : Division.Prepared channel :=
  let future := channel.based observed.state
  let evidence := observationApart observed positive lower
  { denominator := future.apartify evidence
    apart := ⟨Process.Apart.Preparation.apartifyApart evidence⟩
    equivalent := (channel.basedEquivalent observed.state).trans (future.apartifyEquivalent evidence) }

/-- The prepared presentation is the existing apartified future of the same exact retained observation state. -/
theorem ofObservation_denominator :
    (ofObservation observed positive lower).denominator =
      (channel.based observed.state).apartify (observationApart observed positive lower) := by
  unfold ofObservation
  rfl

/-- Every actual prepared candidate remains possible at the original supplied observation state.

Both refinement layers keep their actual source states. This statement does
not replace the original process or infer provenance from equal readings.
-/
theorem ofObservation_candidate {state : (ofObservation observed positive lower).denominator.name.process.State}
    {candidate : Canonical}
    (possible : (ofObservation observed positive lower).denominator.name.process.Possible state candidate) :
    channel.name.process.Possible observed.state candidate := by
  change (Process.Based.based channel.name.process observed.state).Possible state.source candidate at possible
  exact Process.Based.based_initial_persists _ _ possible

end Purelib.Approximation.Gaussian.Division.Prepared

end
