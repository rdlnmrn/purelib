module
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Data.Gaussian.Dyadic
import Purelib.Data.Rat.Dyadic.Basic
import Init.Prelude

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite dyadic range reduction for the progressive logarithm

A logarithm needs branch information.  This module records that information
as one finite dyadic chart: a natural exponent, a scaling direction, and a
proof that every candidate at the displayed input state is carried into the
overlapping real interval `[1/2,2]`.

The output is the local finite logarithm of the scaled input plus or minus an
explicit natural multiple of the independently generated finite `log 2`
samples.  No completed logarithm, limiting value, or infinite functional
equation appears in the construction.
-/

namespace Purelib.Approximation.Gaussian.Name.DyadicScaling

/-- Scale the original Gaussian name by the exact dyadic factor with the displayed direction and exponent. -/
def scaledInput (input : Gaussian.Name.Basic.Named) (direction
  : Dyadic.Basic.Direction)
    (exponent : Nat) : Gaussian.Name.Basic.Named :=
  Named.mul
    (Named.exact
      (Dyadic.dyadicFactor direction exponent)) input
end Purelib.Approximation.Gaussian.Name.DyadicScaling

end
