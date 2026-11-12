module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Data.Gaussian.Norm.Nonzero

/-! ## Uniform moves between robust unit-parameter frames -/

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A canonical Gaussian with squared norm one is nonzero. -/
theorem nonzero_of_normSq_eq_one {parameter : Basic.Canonical}
    (unit : Norm.Basic.normSq parameter = 1) : parameter ≠ 0 := by
  intro zero
  rw [zero, Norm.Basic.normSq_zero] at unit
  exact (by decide : (0 : Fraction.Rational) ≠ 1) unit
end Purelib.Data.Gaussian.Norm.Nonzero

end

public section

namespace Purelib.Data.Gaussian.Norm.Nonzero

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- Compute a real Gaussian whose positive coordinate is capped by one and the supplied quadrance budget.

For a positive budget the returned value is nonzero. Its coordinate is at
most one, so squaring it does not exceed that same budget. No square root
or independently selected rational witness enters the construction.
-/
@[expose] def boundedReal (bound : Rational) : Canonical :=
  ⟨min 1 bound, 0⟩

/-- The computed real Gaussian has exactly the square of its retained real coordinate as quadrance. -/
theorem boundedReal_normSq (bound : Rational) :
    Norm.Basic.normSq (boundedReal bound) = (min 1 bound) ^ 2 := by
  change (min 1 bound) ^ 2 + (0 : Rational) ^ 2 = (min 1 bound) ^ 2
  ring1

/-- A positive quadrance budget produces a nonzero value of the same exact Gaussian type. -/
theorem boundedReal_nonzero (bound : Rational) (positive : 0 < bound) : boundedReal bound ≠ 0 := by
  have coordinatePositive : (0 : Rational) < min 1 bound :=
    Order.Basic.lt_min (by decide +kernel) positive
  intro zero
  have coordinate := congrArg Canonical.re zero
  change min (1 : Rational) bound = 0 at coordinate
  exact coordinatePositive.ne coordinate.symm

/-- The actual computed nonzero Gaussian pays its original positive quadrance budget. -/
theorem boundedReal_normSq_le (bound : Rational) (positive : 0 < bound) :
    Norm.Basic.normSq (boundedReal bound) ≤ bound := by
  have coordinatePositive : (0 : Rational) < min 1 bound :=
    Order.Basic.lt_min (by decide +kernel) positive
  have squared : (min (1 : Rational) bound) ^ 2 ≤ min 1 bound := by
    calc
      _ = min (1 : Rational) bound * min 1 bound := by ring1
      _ ≤ min (1 : Rational) bound * 1 :=
        Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Order.Basic.min_le_left 1 bound) coordinatePositive.le
      _ = min (1 : Rational) bound := Field.mul_one_direct _
  exact (boundedReal_normSq bound).trans_le (squared.trans (Order.Basic.min_le_right 1 bound))

end Purelib.Data.Gaussian.Norm.Nonzero

end
