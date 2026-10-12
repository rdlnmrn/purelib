module

public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.DyadicScaling
import Purelib.Data.Rat.Dyadic.Basic
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local

open Purelib.Approximation.Gaussian.Name

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

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Domain

set_option genInjectivity false in
/-- All data needed to select one finite branch-safe logarithm chart. -/
structure DyadicChart (input :
  Gaussian.Name.Basic.Named) where
  /-- The retained direction of dyadic input scaling. -/ direction : Dyadic.Basic.Direction
  /-- The finite power-of-two exponent used by the retained scaling. -/ exponent : Nat
  /-- The real local-logarithm chart certificate for the original name scaled by that exact direction and exponent. -/
    localChart : Domain.Chart
    (DyadicScaling.scaledInput input direction exponent)

constructive_injectivity DyadicChart

end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Domain

end
