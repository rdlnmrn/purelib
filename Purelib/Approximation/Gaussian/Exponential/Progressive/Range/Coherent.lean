module
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
public import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Coherent
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.DyadicReduction
import Purelib.Approximation.Gaussian.Process.Coherence.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Arithmetic.Power

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

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent

/-- The total range-reduced and repeatedly squared exponential CCL transform has a finite coherence certificate for
every arithmetic input name. -/
def expNamedCoherent (input :
  Gaussian.Name.Basic.Named) :
    Gaussian.Process.Coherence.Basic.Coherent (Exponential.Progressive.Range.Name.named input).process := by
  apply Coherent.squareIterateCoherent
  exact Exponential.Progressive.Local.Coherent.localExpCoherent
    (DyadicReduction.scaledInput input)
    (DyadicReduction.scaledDomain input)

/-- Package the range-reduced productive exponential name with its retained finite coherence certificate. -/
def exp (input : Gaussian.Name.Basic.Named)
  : Coherent.CoherentNamed :=
  { name := Exponential.Progressive.Range.Name.named input
    coherent := expNamedCoherent input }
end Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent

end
