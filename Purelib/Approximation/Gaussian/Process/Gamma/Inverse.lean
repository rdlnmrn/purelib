module
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
public import Purelib.Data.Gaussian.Constants
public import Purelib.Approximation.Gaussian.Process.Apart.Based
public import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Division
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian.Process.Based

open Purelib.Approximation.Gaussian

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

namespace Purelib.Approximation.Gaussian.Process.Gamma.Inverse

/-! ## Inverse normalization after retained unary padding -/

/-- Generic exact inverse chart based at an apart residual state. -/
def inverseOfApartProcess
    (residual : Approximation.Gaussian.Process) (base : residual.State)
    (certificate : Approximation.Gaussian.Enclosure.Ball.Apart
      (residual.ball base)) : Approximation.Gaussian.Process :=
  let candidateApart := Based.possibleApartOfBall residual base certificate
  let denominator := Preparation.apartify candidateApart
  Approximation.Gaussian.Process.div
    (Approximation.Gaussian.Process.exact Data.Gaussian.Basic.Canonical.gamma⁻¹)
    denominator (Preparation.apartifyApart candidateApart)

/-- Construct the initial state of the inverse gamma chart from the exact unit numerator and the apartness-prepared
retained residual state. -/
def inverseOfApartInitial
    (residual : Approximation.Gaussian.Process) (base : residual.State)
    (certificate : Approximation.Gaussian.Enclosure.Ball.Apart
      (residual.ball base)) :
    (inverseOfApartProcess residual base certificate).State :=
  let candidateApart := Based.possibleApartOfBall residual base certificate
  ((), Preparation.prepareApartState candidateApart (BasedState.initial residual base))
end Purelib.Approximation.Gaussian.Process.Gamma.Inverse

end
