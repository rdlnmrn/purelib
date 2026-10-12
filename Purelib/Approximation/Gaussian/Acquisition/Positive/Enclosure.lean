module
public import Purelib.Approximation.Gaussian.Acquisition.State
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

section
@[expose] public section

/-!
# Automatic discovery of the initial positive enclosure

A cached rational ball passes when its centre is above the real axis and its
squared radius is below the squared half-height. The soundness proof gives a
positive imaginary lower bound for every point in that ball. Failed tests
perform one canonical finite refinement; bounded runs retain their exact
state on exhaustion and never infer a negative positivity verdict.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Positive.Enclosure

/-- Construct a positive imaginary enclosure from a successful test of the cached acquisition ball.

The certificate retains the exact source state and uses half the cached center height as its positive lower bound. -/
def enclosure {tau : Coherent.CoherentNamed} (state
  : Approximation.Gaussian.Acquisition.State tau)
    (test : Positive.PositiveTest state.ball) : Positive.Basic.PositiveEnclosure tau where
  state := state.retained.source
  lower := state.ball.center.im / 2
  positive := Positive.half_positive test
  inside_lower := by
    intro value inside
    rw [← state.ball_eq] at inside
    exact Positive.positiveTest_sound test inside
end Purelib.Approximation.Gaussian.Acquisition.Positive.Enclosure

end
