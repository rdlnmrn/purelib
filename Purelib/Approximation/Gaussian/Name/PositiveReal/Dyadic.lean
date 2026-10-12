module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.PositiveReal.Basic
public import Purelib.Approximation.Gaussian.Name.PositiveReal.Preparation
import Purelib.Data.Rat.Dyadic.Basic
public import Purelib.Data.Rat.Dyadic.Normalization
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.PositiveReal

open Purelib.Data.Rat

open Purelib.Data.Rat.Dyadic

section
@[expose] public section

/-!
# Automatic positive-real charting for a CCL logarithm

The input certificate supplies a displayed positive rational lower bound for
the real coordinate of every candidate at the current finite state.  One
explicit refinement makes the current ball small relative to that bound.
The rational real coordinate of the refined ball centre is then normalized
by a bounded dyadic scan, and every explicitly possible candidate at the
refined state is proved to land in the overlapping local logarithm chart.
The geometric ball may of course contain irrelevant non-real points; the
separate positive-real certificate excludes those from the process semantics.

This is branch data and finite error accounting only.  It neither selects a
point common to all refinements nor asserts a completed logarithm.  Its
purpose is to make positive-real logarithm an automatic CCL-to-CCL operator
on this certified domain: chart preparation, local logarithm, the finite
`log 2` correction, and every correction addition remain arithmetic CCL
names.
-/

namespace Purelib.Approximation.Gaussian.Name.PositiveReal.Dyadic

/-- Compute the bounded dyadic normalization of the positive real coordinate of the refined center.

The original positive-real name supplies the center positivity certificate used by the finite normalization scan. -/
def centerNormalization {input :
  Gaussian.Name.Basic.Named} (positive : Approximation.Gaussian.Name.PositiveReal input) :
    Data.Rat.Dyadic.Normalization (Preparation.refinedCenter positive).re :=
  Normalization.normalize (Preparation.refinedCenter positive).re
    (Preparation.refinedCenter_pos positive)

/-- The dyadic normalization factor scales the retained refinement slack to at most one quarter. -/
theorem scaledSlack_le_quarter {input :
  Gaussian.Name.Basic.Named} (positive : Approximation.Gaussian.Name.PositiveReal input) :
    Dyadic.Basic.factor
          (centerNormalization positive).direction
          (centerNormalization positive).exponent *
        Preparation.refinementSlack positive ≤ 1 / 4 := by
  let normalization := centerNormalization positive
  let scalar := Dyadic.Basic.factor
    normalization.direction normalization.exponent
  have scalarPositive : 0 < scalar :=
    Dyadic.Basic.factor_pos _ _
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := (8 : Fraction.Rational))
  · calc
      (scalar * Preparation.refinementSlack positive) * 8 =
          scalar * (Preparation.refinementSlack positive * 8) := by ring1
      _ = scalar * (positive.lower / 2) := by
        rw [Preparation.refinementSlack_mul_eight]
      _ ≤ scalar * (Preparation.refinedCenter positive).re :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Preparation.half_lower_le_refinedCenter positive) scalarPositive.le
      _ = Dyadic.Basic.normalized
          (Preparation.refinedCenter positive).re normalization.direction
            normalization.exponent :=
        (Dyadic.Basic.normalized_eq_factor_mul _ _ _).symm
      _ ≤ 3 / 2 := normalization.upper
      _ ≤ 2 := by decide
      _ = (1 / 4 : Fraction.Rational) * 8 := by decide
  · decide
end Purelib.Approximation.Gaussian.Name.PositiveReal.Dyadic

end
