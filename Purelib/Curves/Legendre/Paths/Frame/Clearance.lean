module

public import Purelib.Curves.Legendre.Paths.Frame
public import Purelib.Curves.Legendre.PicardFuchs.Clearance.Increment

/-! # Original Legendre frames from quantitative parameter clearance

The original frame factory constructs its labelled branch owners at the
actual retained parameter. Positive distance floors derive both required
singular-value exclusions. An admitted increment therefore constructs a
regular target frame without assuming one or asserting continuation of
an original geometric cycle.
-/

public section

namespace Purelib.Curves.Legendre.Paths.Frame

open Purelib
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data.Gaussian

/-- Construct the original labelled frame at a parameter with its two positive singular-value distance floors. -/
def ofClearance {parameter : Paths.Gaussian} (clearance : ParameterClearance parameter) : Paths.Frame parameter :=
  ofParameter parameter clearance.parameter_ne_zero (fun same =>
    clearance.parameter_sub_one_ne_zero (by rewrite [same]; rfl))

/-- An admitted original distance allocation constructs a regular frame at the identical shifted parameter.

The original source frame supplies exact positive distances through its
existing ParameterClearance.ofFrame factory. Both shifted exclusions are
derived before the original target frame constructor is executed once.
-/
def ofIncrement {parameter : Paths.Gaussian} (frame : Paths.Frame parameter) (increment : Paths.Gaussian)
    (admitted : Norm.Basic.normSq increment ≤ (ParameterClearance.ofFrame frame).incrementBound) :
    Paths.Frame (parameter + increment) :=
  let clearance := ParameterClearance.ofFrame frame
  let target := clearance.shifted increment admitted
  ofClearance target

/-- The whole target frame uses the original clearance-backed factory at the same exact admitted increment. -/
theorem ofIncrement_eq {parameter : Paths.Gaussian} (frame : Paths.Frame parameter) (increment : Paths.Gaussian)
    (admitted : Norm.Basic.normSq increment ≤ (ParameterClearance.ofFrame frame).incrementBound) :
    frame.ofIncrement increment admitted =
      ofClearance ((ParameterClearance.ofFrame frame).shifted increment admitted) := by
  rfl

end Purelib.Curves.Legendre.Paths.Frame

end
