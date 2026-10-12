module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Domain
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.DyadicScaling
import Purelib.Data.Rat.Dyadic.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

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

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Name

/-- The local finite logarithm stream at the exact rational input `2`. -/
def logTwo : Gaussian.Name.Basic.Named :=
  Local.Name.named
    (Named.exact ⟨2, 0⟩)
    (Chart.exact 2 (by decide) le_rfl)

/-- Signed finite correction coefficient. Downscaling gives `log(x / 2^n) + n log 2`; upscaling gives `log(2^n x) - n
log 2`. -/
def correctionCoefficient (direction :
  Dyadic.Basic.Direction)
    (exponent : Nat) : Data.Gaussian.Basic.Canonical :=
  match direction with
  | .down => ⟨(exponent : Fraction.Rational), 0⟩
  | .up => ⟨-(exponent : Fraction.Rational), 0⟩

/-- Multiply the exact signed dyadic exponent coefficient by the independently generated finite logarithm-of-two name.
-/
def correction (direction :
  Dyadic.Basic.Direction) (exponent : Nat) : Gaussian.Name.Basic.Named :=
  Named.mul
    (Named.exact
      (correctionCoefficient direction exponent))
        logTwo

/-- Global finite logarithm output from one explicit branch-safe dyadic chart. -/
def named (input :
  Gaussian.Name.Basic.Named) (chart : Domain.DyadicChart input) : Gaussian.Name.Basic.Named :=
  Named.add
    (Local.Name.named
      (DyadicScaling.scaledInput input chart.direction chart.exponent) chart.localChart)
    (correction chart.direction chart.exponent)
end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Name

end
