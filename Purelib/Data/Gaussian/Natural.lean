module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

section
public section

/-!
# Natural Gaussian embeddings and repeated coefficients

The original real natural embedding and finite repeated addition retain
the supplied count and coefficient.
-/

namespace Purelib.Data.Gaussian.Natural

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Nat.Positive

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.Fraction.Cast

/-- Embed a supplied natural as a real canonical Gaussian rational. -/
@[expose] def naturalGaussian (value : Nat) : Canonical :=
  ⟨value, 0⟩

/-- The Gaussian image of a retained positive natural degree is nonzero. -/
theorem naturalGaussian_ne_zero (degree : RootDegree) :
    Natural.naturalGaussian degree.value ≠ 0 := by
  intro equal
  have realEqual := congrArg Gaussian.Basic.re equal
  change (degree.value : Rational) = 0 at realEqual
  have naturalZero : degree.value = 0 := by
    exact Compatibility.natCast_injective_direct realEqual
  exact (Nat.ne_of_gt degree.positive) naturalZero

/-- Add one retained Gaussian coefficient repeatedly for a supplied natural count.

Zero repetitions give zero; each successor adds the original coefficient to the
preceding finite sum. -/
@[expose] def repeatedCoefficient (coefficient : Canonical) : Nat → Canonical
  | 0 => 0
  | count + 1 => coefficient + Purelib.Data.Gaussian.Natural.repeatedCoefficient coefficient count

/-- The Gaussian image of a successor natural is one plus the image of its predecessor.

The real coordinate preserves the original successor addition, and the imaginary coordinate stays zero. -/
theorem naturalGaussian_succ (count : Nat) :
    Natural.naturalGaussian (count + 1) = 1 + Natural.naturalGaussian count := by
  apply Gaussian.Basic.ext
  · change ((count + 1 : Nat) : Rational) = 1 + (count : Rational)
    rw [NatCast.add, Nat.cast_one]
    exact Field.add_comm _ _
  · change (0 : Rational) = 0 + 0
    ring1

/-- Repeated finite addition equals multiplication by the Gaussian image of the
repetition count. -/
theorem repeatedCoefficient_eq (coefficient : Canonical) :
    (count : Nat) →
      Natural.repeatedCoefficient coefficient count =
        Natural.naturalGaussian count * coefficient
  | 0 => by
      exact (Gaussian.Basic.zero_mul coefficient).symm
  | count + 1 => by
      rw [Natural.repeatedCoefficient, Purelib.Data.Gaussian.Natural.repeatedCoefficient_eq,
        Natural.naturalGaussian_succ]
      calc
        coefficient + Natural.naturalGaussian count * coefficient =
            1 * coefficient + Natural.naturalGaussian count * coefficient := by
          rw [Gaussian.Basic.one_mul]
        _ = (1 + Natural.naturalGaussian count) * coefficient :=
          (Gaussian.Basic.right_distrib
            1 (Natural.naturalGaussian count) coefficient).symm
end Purelib.Data.Gaussian.Natural

end
