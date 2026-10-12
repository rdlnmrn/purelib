module
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
public import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Process.Apart

section
@[expose] public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Approximation.Gaussian.Process.Apart.Based

/-- Turn a whole-ball apartness certificate at a base state into uniform candidate apartness throughout its rebased
future. -/
def possibleApartOfBall
    (process : Approximation.Gaussian.Process) (base : process.State)
    (certificate : Approximation.Gaussian.Enclosure.Ball.Apart
      (process.ball base)) : Possible.PossibleApart (Gaussian.Process.Based.based process base) where
  lowerSq := certificate.lowerSq
  positive := certificate.positive
  lower := by
    intro state value valuePossible
    exact certificate.lower
      (process.possible_inside (state.persists valuePossible))
end Purelib.Approximation.Gaussian.Process.Apart.Based

end
