module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic
public import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Data.Gaussian.Dyadic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name (UnitDisk)

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

open Purelib.Data.Gaussian

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

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Halving

/-- Every possible reading after one coherent halving has quadrance at most one quarter when the original input lies in
the unit disk. -/
theorem halfScaled_possible_quarter (input :
  Coherent.CoherentNamed)
    (domain : UnitDisk input.name)
    {value : Data.Gaussian.Basic.Canonical}
    (possible : (Dyadic.halfScaled input).name.process.Possible
      (Dyadic.halfScaled input).name.state value) :
    Data.Gaussian.Norm.Basic.normSq value ≤ 1 / 4 := by
  rcases possible with ⟨scaleValue, sourceValue,
    scalePossible, sourcePossible, rfl⟩
  change scaleValue = Dyadic.dyadicHalf at scalePossible
  subst scaleValue
  rw [Data.Gaussian.Norm.Basic.normSq_mul, Dyadic.normSq_dyadicHalf]
  calc
    (1 / 4 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq sourceValue ≤ (1 / 4 : Fraction.Rational) * 1
      :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (domain.possible_unit sourcePossible) (by decide)
    _ = 1 / 4 := Fraction.Field.mul_one_direct _

/-- Halving preserves the local unit-disk contract. -/
theorem halfScaledUnitDisk (input :
  Coherent.CoherentNamed)
    (domain : UnitDisk input.name) :
    UnitDisk (Dyadic.halfScaled input).name where
  possible_unit := by
    intro value possible
    exact (halfScaled_possible_quarter input domain
      possible).trans (by decide)

/-- The sum of two independently refined half-scaled readings remains in the unit disk. The proof uses their separate
quarter-quadrance bounds and does not identify the two readings. -/
theorem halfScaledSelfSumUnitDisk (input :
  Coherent.CoherentNamed)
    (domain : UnitDisk input.name) :
    UnitDisk
      (Named.add
        (Dyadic.halfScaled input).name (Dyadic.halfScaled input).name) where
  possible_unit := by
    intro value possible
    rcases possible with ⟨leftValue, rightValue,
      leftPossible, rightPossible, rfl⟩
    calc
      Data.Gaussian.Norm.Basic.normSq (leftValue + rightValue) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq leftValue + Data.Gaussian.Norm.Basic.normSq rightValue)
            :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * ((1 / 4 : Fraction.Rational) + 1 / 4) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add
            (halfScaled_possible_quarter input domain
              leftPossible)
            (halfScaled_possible_quarter input domain
              rightPossible))
          (by decide)
      _ = 1 := by decide

/-- Every finite halving chain preserves a supplied unit-disk certificate. -/
theorem halfIterateUnitDisk : (extra : Nat)
  → (input : Coherent.CoherentNamed) →
    UnitDisk input.name →
      UnitDisk (Dyadic.halfIterate extra input).name
  | 0, _input, domain => domain
  | extra + 1, input, domain =>
      halfScaledUnitDisk (Dyadic.halfIterate extra input)
        (halfIterateUnitDisk extra input domain)
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Halving

end
