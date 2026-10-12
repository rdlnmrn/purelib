module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.NatCast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

namespace Purelib.Data.Rat.Dyadic.Grid

/- Keep the large denominator in its canonical denominator-one form.  The
ordinary `Nat.cast` supplied by the minimal constructive ring instance is
definitionally unary, so evaluating `(1048576 : Purelib.Data.Rat.Fraction.Compatibility.Rational)` would recurse more
than a
million times before any grid calculation starts. -/
open Purelib.Data.Rat
/-- Compute the rational fine-grid spacing one over 1048576 using the integer cast constructor. -/
def fineUnit : Fraction.Rational :=
  1 / Fraction.Cast.fromInt 1048576

/-- The fine-grid spacing equals the rational literal one over 1048576. -/
theorem secondFineUnit_eq_div : fineUnit = (1 / 1048576 :
  Fraction.Rational) := by
  unfold fineUnit
  change
    1 / Fraction.Cast.fromInt 1048576 =
      1 / ((1048576 : Nat) : Fraction.Rational)
  rw [Fraction.Cast.natCast_eq_fromInt]
  congr 2

/-- The rational fine-grid spacing is nonnegative. -/
public theorem fineUnitNonnegative : (0 : Fraction.Rational) ≤ fineUnit
  := by
  rw [secondFineUnit_eq_div]
  exact
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.NatCast.natCast_pos_direct 1 (by omega))
        (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega))).le

/-- A matching cross product expresses a positive-denominator rational fraction as a multiple of the fine-grid unit.

The denominator must be positive and the cross product uses the same numerator and scale. Cancellation identifies the
original fraction with the scale times one over 1048576. -/
public theorem scaledFine (numerator scale : Fraction.Rational) (denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (cross : numerator * 1048576 = scale * denominator) :
    numerator / denominator = scale * fineUnit := by
  rw [secondFineUnit_eq_div]
  calc
    numerator / denominator = scale / 1048576 :=
      Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Order.NatCast.natCast_pos_direct denominator denominatorPositive).ne'
        (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne' cross
    _ = scale * (1 / 1048576) := by
      simp only [Fraction.Field.div_eq_mul_inv_direct,
        _root_.one_mul, -eq_self, -iff_self]
      rfl

/-- The fine-grid unit equals 1048576 times its square. -/
private theorem fineUnit_eq_scaled_square :
    fineUnit = 1048576 * fineUnit ^ 2 := by
  rw [secondFineUnit_eq_div]
  rw [pow_two]
  calc
    (1 / 1048576 : Fraction.Rational) = 1 * (1 / 1048576) := by ring1
    _ = ((1 / 1048576 : Fraction.Rational) * 1048576) * (1 / 1048576) :=
      congrArg (fun value : Fraction.Rational => value * (1 / 1048576))
        (Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne').symm
    _ = 1048576 * ((1 / 1048576 : Fraction.Rational) * (1 / 1048576)) := by ring1

/-- One thirty-second equals 32768 fine-grid units. -/
public theorem oneThirtySecondFine :
    (1 / 32 : Fraction.Rational) = 32768 * fineUnit :=
  scaledFine 1 32768 32 (by omega) (by ring1)

/-- One eighth equals 131072 fine-grid units. -/
public theorem oneEighthFine :
    (1 / 8 : Fraction.Rational) = 131072 * fineUnit :=
  scaledFine 1 131072 8 (by omega) (by ring1)

/-- The rational value 1011 over 4096 equals 258816 fine-grid units. -/
public theorem variationFine :
    (1011 / 4096 : Fraction.Rational) = 258816 * fineUnit :=
  scaledFine 1011 258816 4096 (by omega) (by ring1)

end Purelib.Data.Rat.Dyadic.Grid

end

section
@[expose] public section

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

namespace Purelib.Data.Rat.Dyadic.Grid

/-! ## Depth-three radicand grid -/

/- Canonical direct construction avoids the minimal ring instance's unary
`Nat.cast` loop when executable quartic data initialize this denominator. -/
open Purelib.Data.Rat
/-- Compute the rational grid spacing one over 1048576 using the integer cast constructor. -/
def GridFineUnit : Fraction.Rational :=
  1 / Fraction.Cast.fromInt 1048576

/-- The retained grid spacing equals the rational literal one over 1048576. -/
theorem GridFineUnit_eq_div :
    GridFineUnit = (1 / 1048576 : Fraction.Rational) := by
  unfold GridFineUnit
  change
    1 / Fraction.Cast.fromInt 1048576 =
      1 / ((1048576 : Nat) : Fraction.Rational)
  rw [Fraction.Cast.natCast_eq_fromInt]
  congr 2

/-- The retained rational grid spacing is nonnegative. -/
theorem GridFineUnitNonnegative : (0 : Fraction.Rational) ≤ GridFineUnit
  := by
  rw [GridFineUnit_eq_div]
  exact
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.NatCast.natCast_pos_direct 1 (by omega))
        (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega))).le

/-- A matching cross product expresses a positive-denominator rational fraction as a multiple of the retained grid unit.

The supplied positive denominator and matching numerator-scale equation identify the original fraction with the retained
one-over-1048576 grid scale. -/
theorem scaledQuarticGrid (numerator scale : Fraction.Rational) (denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (cross : numerator * 1048576 = scale * denominator) :
    numerator / denominator = scale * GridFineUnit := by
  rw [GridFineUnit_eq_div]
  calc
    numerator / denominator = scale / 1048576 :=
      Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Order.NatCast.natCast_pos_direct denominator denominatorPositive).ne'
        (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne' cross
    _ = scale * (1 / 1048576) := by
      simp only [Fraction.Field.div_eq_mul_inv_direct,
        _root_.one_mul, -eq_self, -iff_self]
      rfl

/-- The retained grid unit equals 1048576 times its square. -/
theorem GridFineUnit_eq_scaled_square :
    GridFineUnit = 1048576 * GridFineUnit ^ 2 := by
  rw [GridFineUnit_eq_div]
  rw [pow_two]
  calc
    (1 / 1048576 : Fraction.Rational) = 1 * (1 / 1048576) := by ring1
    _ = ((1 / 1048576 : Fraction.Rational) * 1048576) * (1 / 1048576) :=
      congrArg (fun value : Fraction.Rational => value * (1 / 1048576))
        (Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne').symm
    _ = 1048576 * ((1 / 1048576 : Fraction.Rational) * (1 / 1048576)) := by ring1

/-- One sixty-fourth equals 16384 retained grid units. -/
theorem oneSixtyFourthQuarticGridFine :
    (1 / 64 : Fraction.Rational) = 16384 * GridFineUnit :=
  scaledQuarticGrid 1 16384 64 (by omega) (by ring1)
end Purelib.Data.Rat.Dyadic.Grid

end

section
@[expose] public section

/-!
# Analytic and grid data for the fifth prepared quartic connector cell
-/

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedFifthCell

open Purelib.Data.Rat in
/-- One over 2048 equals 512 retained grid units. -/
private theorem oneTwoThousandFortyEighthQuarticGridFine :
    (1 / 2048 : Fraction.Rational) = 512 * Dyadic.Grid.GridFineUnit :=
  Dyadic.Grid.scaledQuarticGrid 1 512 2048 (by omega) (by ring1)
end Purelib.Examples.Riemann.ExplicitQuarticPreparedFifthCell

end

section
@[expose] public section

/-!
# Analytic and grid data for the fourth prepared quartic connector cell
-/

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedFourthCell

open Purelib.Data.Rat in
/-- One over 512 equals 2048 retained grid units. -/
private theorem oneFiveHundredTwelfthQuarticGridFine :
    (1 / 512 : Fraction.Rational) = 2048 * Dyadic.Grid.GridFineUnit :=
  Dyadic.Grid.scaledQuarticGrid 1 2048 512 (by omega) (by ring1)
end Purelib.Examples.Riemann.ExplicitQuarticPreparedFourthCell

end

section
@[expose] public section

/-!
# Analytic and grid data for the seventh prepared quartic connector cell
-/

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSeventhCell

open Purelib.Data.Rat in
/-- One over 512 equals 2048 retained grid units. -/
private theorem oneFiveHundredTwelfthQuarticGridFine :
    (1 / 512 : Fraction.Rational) = 2048 * Dyadic.Grid.GridFineUnit :=
  Dyadic.Grid.scaledQuarticGrid 1 2048 512 (by omega) (by ring1)
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSeventhCell

end

section
@[expose] public section

/-!
# Analytic and grid data for the sixth prepared quartic connector cell
-/

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSixthCell

open Purelib.Data.Rat in
/-- One over 2048 equals 512 retained grid units. -/
private theorem oneTwoThousandFortyEighthQuarticGridFine :
    (1 / 2048 : Fraction.Rational) = 512 * Dyadic.Grid.GridFineUnit :=
  Dyadic.Grid.scaledQuarticGrid 1 512 2048 (by omega) (by ring1)
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSixthCell

end
