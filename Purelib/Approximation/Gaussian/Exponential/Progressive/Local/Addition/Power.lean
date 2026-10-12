module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Law
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Coherent
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Exact
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power
public import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Congruence
public import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Laws
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.UnitDisk

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Power

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Arithmetic
open Purelib.Approximation.Gaussian.Name.Arithmetic.Power
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent

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

/-- The arbitrary coherent-input local exponential addition law survives any common displayed number of actual CCL
squarings. -/
@[expose] def coherentLocalExp_add_after_squareIterate (exponent : Nat)
    (left right : Coherent.CoherentNamed)
    (leftDomain : Name.UnitDisk left.name)
    (rightDomain : Name.UnitDisk right.name)
    (sumDomain : Name.UnitDisk
      (Named.add
        left.name right.name)) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Power.squareIterate exponent
          (Name.named left.name leftDomain))
        (Power.squareIterate exponent
          (Name.named right.name rightDomain)))
      (Power.squareIterate exponent
        (Name.named
          (Named.add
            left.name right.name) sumDomain)) := by
  let leftExp : Coherent.CoherentNamed :=
    { name := Name.named left.name leftDomain
      coherent := Coherent.localExpCoherent left.name leftDomain }
  let rightExp : Coherent.CoherentNamed :=
    { name := Name.named right.name rightDomain
      coherent := Coherent.localExpCoherent right.name rightDomain }
  let sumInput := CoherentNamed.add
    left right
  let sumExp : Coherent.CoherentNamed :=
    { name := Name.named sumInput.name sumDomain
      coherent := Coherent.localExpCoherent sumInput.name sumDomain }
  let productExp :=
    CoherentNamed.mul leftExp rightExp
  exact NamedEquivalent.trans
    (Laws.squareIterate_mul_equivalent exponent leftExp rightExp)
    (Congruence.squareIterate_respects exponent productExp sumExp
      (Law.coherentLocalExp_add_named_equivalent left right
        leftDomain rightDomain sumDomain))

/-- The exact local exponential addition law survives any common displayed number of actual CCL squarings.

This specializes the arbitrary coherent law to displayed rational operands. -/
@[expose] def exactLocalExp_add_after_squareIterate (exponent : Nat)
    {x y : Data.Gaussian.Basic.Canonical}
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1)
    (sumUnit : Data.Gaussian.Norm.Basic.normSq (x + y) ≤ 1) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Power.squareIterate exponent
          (Exact.exactLocalExpNamed x xUnit))
        (Power.squareIterate exponent
          (Exact.exactLocalExpNamed y yUnit)))
      (Power.squareIterate exponent
        (Exact.exactLocalExpNamed (x + y) sumUnit)) := by
  let leftExp : Coherent.CoherentNamed :=
    CoherentNamed.ofApproximation
      (Exact.exactLocalExpApproximation x xUnit)
  let rightExp : Coherent.CoherentNamed :=
    CoherentNamed.ofApproximation
      (Exact.exactLocalExpApproximation y yUnit)
  let sumExp : Coherent.CoherentNamed :=
    CoherentNamed.ofApproximation
      (Exact.exactLocalExpApproximation (x + y) sumUnit)
  let productExp :=
    CoherentNamed.mul leftExp rightExp
  exact NamedEquivalent.trans
    (Laws.squareIterate_mul_equivalent exponent leftExp rightExp)
    (Congruence.squareIterate_respects exponent productExp sumExp
      (Exact.localExp_add_actual_named_equivalent xUnit yUnit sumUnit))

/-- One additional dyadic range-reduction step is exactly compensated by one actual output squaring, after any fixed
finite squaring tail. -/
@[expose] def exactLocalExp_doubling_after_squareIterate (exponent : Nat)
    (value : Data.Gaussian.Basic.Canonical) (unit : Data.Gaussian.Norm.Basic.normSq value ≤ 1)
    (doubleUnit : Data.Gaussian.Norm.Basic.normSq (value + value) ≤ 1) :
    Gaussian.Equivalence.NamedEquivalent
      (Power.squareIterate (exponent + 1)
        (Exact.exactLocalExpNamed value unit))
      (Power.squareIterate exponent
      (Exact.exactLocalExpNamed (value + value) doubleUnit)) :=
  Approximation.Gaussian.Exponential.Progressive.Local.Addition.Power.exactLocalExp_add_after_squareIterate exponent
    unit unit doubleUnit

end

end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Power
