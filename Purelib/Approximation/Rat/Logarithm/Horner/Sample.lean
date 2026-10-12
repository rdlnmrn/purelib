module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rat.Logarithm.Horner.Basic
public import Purelib.Approximation.Rat.Logarithm.Reduction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rat.Logarithm

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace Purelib.Approximation.Rat.Logarithm.Horner.Sample

/-- Twice the rational reduced logarithm argument. -/
def outputFactor (x : Fraction.Rational) : Fraction.Rational :=
  2 * Reduction.reducedArgument x

/-- On the interval from one half to two, the logarithm output factor has square at most one. -/
theorem outputFactor_sq_le_one {x : Fraction.Rational} (halfLe
  : 1 / 2 ≤ x)
    (leTwo : x ≤ 2) :
    outputFactor x ^ 2 ≤ 1 := by
  calc
    outputFactor x ^ 2 = 4 * Reduction.squaredArgument x := by
      rw [outputFactor, Reduction.squaredArgument]
      ring1
    _ ≤ 4 * (1 / 9 : Fraction.Rational) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Reduction.squaredArgument_le_ninth halfLe leTwo) (by decide)
    _ ≤ 1 := by decide

/-- Compute a canonical rational finite logarithm sample.

The sample multiplies the reduced output factor by the displayed finite Horner value starting at coefficient index one.
-/
def sampleCoordinate (x : Fraction.Rational) (index : Nat) :
  Fraction.Rational :=
  Fraction.Basic.canonical
    (outputFactor x * Horner.Basic.horner (Reduction.squaredArgument x) 1
      index)

/-- The canonical logarithm sample equals its displayed output factor times the finite Horner value. -/
theorem sampleCoordinate_eq (x : Fraction.Rational) (index :
  Nat) :
    sampleCoordinate x index =
      outputFactor x * Horner.Basic.horner (Reduction.squaredArgument x) 1
        index :=
  Fraction.Basic.canonical_eq _
end Purelib.Approximation.Rat.Logarithm.Horner.Sample

end
