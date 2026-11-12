module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Power
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Congruence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Halving
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic
import Purelib.Approximation.Gaussian.Name.UnitDisk

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Addition

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Halving

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Arithmetic
open Purelib.Approximation.Gaussian.Name.Arithmetic.Power
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

open Purelib.Approximation

/-- For an arbitrary coherent progressive input, one additional finite input halving followed by one additional actual
output squaring preserves the restored local exponential name. -/
@[expose] def coherentDyadicExp_step (exponent : Nat) (input : CoherentNamed)
    (domain : UnitDisk input.name) :
    NamedEquivalent
      (Power.squareIterate (exponent + 1)
        (Local.Name.named (Dyadic.halfScaled input).name
          (Local.Halving.halfScaledUnitDisk input domain)))
      (Power.squareIterate exponent
        (Local.Name.named input.name domain)) := by
  let half := Dyadic.halfScaled input
  let halfDomain := Local.Halving.halfScaledUnitDisk input domain
  let sumDomain := Local.Halving.halfScaledSelfSumUnitDisk input domain
  let halfExp : CoherentNamed :=
    { name := Local.Name.named half.name halfDomain
      coherent := Local.Coherent.localExpCoherent half.name halfDomain }
  let sumInput :=
    CoherentNamed.add half half
  let sumExp : CoherentNamed :=
    { name := Local.Name.named sumInput.name sumDomain
      coherent := Local.Coherent.localExpCoherent sumInput.name sumDomain }
  let inputExp : CoherentNamed :=
    { name := Local.Name.named input.name domain
      coherent := Local.Coherent.localExpCoherent input.name domain }
  have localLaw := Local.Addition.Power.coherentLocalExp_add_after_squareIterate exponent
    half half halfDomain halfDomain sumDomain
  have sumToInput : NamedEquivalent sumExp.name inputExp.name :=
    Local.Congruence.localExpNamed_respects sumDomain domain
      (Dyadic.halfScaledSelfAdd_equivalent input)
  have restoredSumToInput := Congruence.squareIterate_respects exponent
    sumExp inputExp sumToInput
  dsimp only [half, halfDomain, sumDomain, sumInput, sumExp] at localLaw
  exact NamedEquivalent.trans
    (by
        simpa only [Power.squareIterate, sumExp, sumInput, half, CoherentNamed.add]
          using localLaw)
    restoredSumToInput

end

end Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Halving
