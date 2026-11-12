module

public import Purelib.RootIsolation.Track.Exclusion.Uniform
public import Purelib.RootIsolation.Track.Observation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform

/-! # Original refinement replies at a uniform-exclusion margin

The retained query uses the same coefficient-computed radius as the
uniform-exclusion operation. Its whole reply factory identifies the actual
refinement state without executing the callback during readback.
-/

public section

namespace Purelib.RootIsolation.Track.Exclusion.Uniform

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion
open Purelib.RootIsolation

/-- The original current-state query at the coefficient-computed uniform-exclusion radius.

The question retains the complete current winding state and the same positive
radius used by refinePastUniformMargin. It computes no track refinement.
-/
@[expose] def marginQuestion
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (lower : Fraction.Rational) (positive : 0 < lower) : Track.Observation.Question current :=
  Track.Observation.Question.ofCurrent current (Uniform.uniformExclusionRadius p ambient lower)
    (Uniform.uniformExclusionRadius_pos p ambient positive)

/-- The actual retained reply reads exactly the original uniform-margin refinement state.

The whole reply factory and original answer readback preserve the current
state, computed radius and actual callback result; no refinement executes
while proving the equality.
-/
theorem reply_state_eq
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (lower : Fraction.Rational) (positive : 0 < lower)
    (reply : Track.Observation.Reply track current)
    (factory : reply = Track.Observation.answer track current
      (marginQuestion current lower positive)) :
    reply.state = refinePastUniformMargin track current lower positive := by
  have actual := congrArg (fun value : Track.Observation.Reply track current => value.state)
    (factory.trans (Track.Observation.answer_eq track current
      (marginQuestion current lower positive)))
  exact actual

end Purelib.RootIsolation.Track.Exclusion.Uniform

end
