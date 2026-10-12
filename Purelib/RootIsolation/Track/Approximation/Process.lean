module
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Box
public import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample

open Purelib.Approximation.Gaussian

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Winding-one tracks as progressive arithmetic processes

Paper I supplies independently shrinking rational boxes without asserting a
completed root.  This module exposes each such finite track directly through
the CCL-2 squared-error process interface.  The possibility predicate is
the current box predicate itself; no point is selected from an intersection.
-/

namespace Purelib.RootIsolation.Track.Approximation.Process

/-- Convert one Paper-I winding-one track into an arbitrarily accurate finite
ball process. -/
def toProcess {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) : Approximation.Gaussian.Process where
  State := State.WindingOne.Basic.WindingOneState p ambient
  ball state := Enclosure.Ball.ofBox state.box
  Possible state value := state.box.Contains value
  witness state := ⟨state.box.anchor, state.box.contains_anchor⟩
  possible_inside := by
    intro state value inside
    exact Enclosure.Ball.contains_ofBox inside
  refine state target positive :=
    track.refine state
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius target)
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius_pos positive)
  refine_persists := by
    intro state target positive value inside
    exact (track.nested state
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius target)
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius_pos positive)).contains
        inside
  accurate := by
    intro state target positive
    exact (track.accurate state
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius target)
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius_pos positive)).trans_lt
        (Data.Rat.Bounds.AccuracyRadius.accuracyRadius_sq_lt positive)
  centerBound := ambient.normSqBound
  centerBound_nonneg := ambient.normSqBound_nonneg
  center_bounded := by
    intro state
    exact ambient.normSq_le_normSqBound
      (state.refinesAmbient.contains state.box.contains_anchor)

/-- The process enclosure of a retained state is exactly the ball obtained from its original box. -/
@[simp] theorem toProcess_ball
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) (state : State.WindingOne.Basic.WindingOneState p ambient) :
    (toProcess track).ball state =
      Approximation.Gaussian.Enclosure.Ball.ofBox state.box := rfl
end Purelib.RootIsolation.Track.Approximation.Process

end
