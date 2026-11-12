module

public import Purelib.RootIsolation.Track.Approximation.Process
public import Purelib.RootIsolation.Track.Observation
public import Purelib.Approximation.Gaussian.Process.Route.Request

/-!
# Original winding refinements as Gaussian source actions

The process accuracy conversion is the same one used by `toProcess`. Exact
track replies supply their original states; observed replies read that same
returned box once without calling the refiner again.
-/

public section

namespace Purelib.RootIsolation.Track.Approximation.Process

open Purelib.Approximation.Gaussian.Process (Route)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat
open Purelib.Data.Rat.Bounds

variable {p : CoefficientPolynomial} {ambient : Box}

/-- Lift the original exact track action through the same process accuracy conversion.

The original winding state and target-to-radius rule are unchanged. The
supplied action is invoked once at that converted radius, and its exact
returned state supplies the process reply without another refinement.
-/
def stateHandler {m : Type → Type} (track : WindingOneTrack p ambient) (refine : Observation.Handler m track) :
    Route.StateHandler m (toProcess track) :=
  fun before target positive =>
    refine before (AccuracyRadius.accuracyRadius target) (AccuracyRadius.accuracyRadius_pos positive)

/-- The pure original track action gives the exact original process refinement and its same state identity. -/
theorem stateHandler_pure (track : WindingOneTrack p ambient) (before : WindingOneState p ambient)
    (target : Fraction.Rational) (positive : 0 < target) :
    stateHandler (m := Id) track (fun state epsilon certificate => ⟨track.refine state epsilon certificate, rfl⟩)
      before target positive = ⟨(toProcess track).refine before target positive, rfl⟩ := (rfl)

/-- Observe the exact returned original winding state without repeating its refinement. -/
def handler {m : Type → Type} [Monad m] (track : WindingOneTrack p ambient)
    (refine : Observation.Handler m track) : Route.Handler m (toProcess track) :=
  fun before target positive => do
    let retained ← stateHandler track refine before target positive
    pure (Route.Refinement.ofState (.input : Route (toProcess track) (toProcess track))
      before target positive retained)

/-- The pure original track action reconstructs the complete original process refinement observation. -/
theorem handler_pure (track : WindingOneTrack p ambient) (before : WindingOneState p ambient)
    (target : Fraction.Rational) (positive : 0 < target) :
    handler (m := Id) track (fun state epsilon certificate => ⟨track.refine state epsilon certificate, rfl⟩)
      before target positive = (.input : Route (toProcess track) (toProcess track)).refine before target positive :=
  Route.Refinement.unique _ _

end Purelib.RootIsolation.Track.Approximation.Process

end
