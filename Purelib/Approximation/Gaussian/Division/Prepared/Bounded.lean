module
public import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
public import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Denominator preparation survives fractional composition

A preparation provider for all invertible integral matrices can be carried
through a prepared fractional action. An outer denominator is represented as
the quotient of the combined and inner denominators. Both are already apart;
one retained base state supplies a uniform upper bound for the divisor.
-/

namespace Purelib.Approximation.Gaussian.Division.Prepared.Bounded

/-- Restrict an already prepared denominator to its retained initial state. This supplies both lower and upper bounds
for all later possible readings. -/
def basedPreparation {denominator :
  Coherent.CoherentNamed}
    (preparation : Prepared.DenominatorPreparation denominator) : Prepared.DenominatorPreparation denominator where
  prepared := preparation.prepared.based preparation.prepared.name.state
  apart := { certificate :=
    { lowerSq := preparation.apart.certificate.lowerSq
      positive := preparation.apart.certificate.positive
      lower := by
        intro state value inside
        exact preparation.apart.certificate.lower state.source inside } }
  equivalent := NamedEquivalent.trans preparation.equivalent
    (preparation.prepared.basedEquivalent preparation.prepared.name.state)

/-- The positive uniform squared-norm bound obtained from the prepared denominator's initial coherence allowance and
center bound. -/
def divisorUpper {denominator : Coherent.CoherentNamed}
    (preparation : Prepared.DenominatorPreparation denominator) : Fraction.Rational :=
  2 * (preparation.prepared.coherent.allowance preparation.prepared.name.state +
    preparation.prepared.name.process.centerBound) + 1

/-- The retained uniform divisor bound is strictly positive. -/
theorem divisorUpper_positive {denominator :
  Coherent.CoherentNamed}
    (preparation : Prepared.DenominatorPreparation denominator) : 0 <
      divisorUpper preparation := by
  have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 2)
    (add_nonneg (preparation.prepared.coherent.allowance_nonneg preparation.prepared.name.state)
      preparation.prepared.name.process.centerBound_nonneg)
  exact lt_of_lt_of_le (by decide : (0 : Fraction.Rational) < 1)
    (le_add_of_nonneg_left nonnegative)

/-- Every possible reading in the based prepared denominator has squared norm at most the retained divisor bound. -/
theorem divisor_bounded {denominator :
  Coherent.CoherentNamed}
    (preparation : Prepared.DenominatorPreparation denominator)
    (state : (basedPreparation
      preparation).prepared.name.process.State)
    {value : Data.Gaussian.Basic.Canonical}
    (possible : (basedPreparation
      preparation).prepared.name.process.Possible state value) :
    Data.Gaussian.Norm.Basic.normSq value ≤ divisorUpper
      preparation :=
  (Gaussian.Process.Coherence.Basic.Coherent.possible_normSq_le preparation.prepared.coherent
    (state.persists possible)).trans (le_add_of_nonneg_right (by decide : (0 : Fraction.Rational) ≤ 1))
end Purelib.Approximation.Gaussian.Division.Prepared.Bounded

end
