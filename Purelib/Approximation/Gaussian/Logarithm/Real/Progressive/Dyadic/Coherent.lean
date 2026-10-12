module
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Name
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.DyadicScaling
public import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Data.Rat.Dyadic.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Name
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction
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
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Coherent

/-- The finite `log 2` stream used by dyadic range correction is coherent. -/
def logTwoCoherent :
    Gaussian.Process.Coherence.Basic.Coherent Name.logTwo.process :=
  Coherent.localLogCoherent
    (Named.exact ⟨2, 0⟩)
    (Chart.exact 2 (by decide) le_rfl)

/-- Every signed natural multiple of the finite `log 2` stream is coherent. -/
def logCorrectionCoherent
    (direction : Dyadic.Basic.Direction) (exponent : Nat) :
    Gaussian.Process.Coherence.Basic.Coherent
      (Name.correction direction exponent).process :=
  Gaussian.Process.Coherence.Basic.Coherent.mul
    (Gaussian.Process.Coherence.Basic.Coherent.exact
      (Name.correctionCoefficient
        direction exponent))
    logTwoCoherent

/-- A dyadically range-reduced positive-real logarithm, including its finite correction term, is coherent. -/
def logRangeNamedCoherent (input :
  Gaussian.Name.Basic.Named)
    (chart : Domain.DyadicChart input) :
    Gaussian.Process.Coherence.Basic.Coherent
      (Name.named input chart).process :=
  Gaussian.Process.Coherence.Basic.Coherent.add
    (Coherent.localLogCoherent
      (DyadicScaling.scaledInput input chart.direction
        chart.exponent) chart.localChart)
    (logCorrectionCoherent chart.direction
      chart.exponent)
end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Coherent

end
