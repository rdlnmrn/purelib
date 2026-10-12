module

import Purelib.Data.Rat.Fraction.Constants
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# A finite redundant output decision for CCL arithmetic

The canonical comparison at squared norm `2` is not stable under finite
enclosures.  This module gives the arithmetic transducer a separate finite
decision.  A sufficiently accurate ball whose centre has squared norm at
least one is either wholly in the next-unary region or wholly safe for one
of the eight sector representatives.

The constants are intentionally rational and square-root-free.  Safe-sector
coverage extends through squared norm `13/6`; the unary test starts below
that bound, at `32/15` plus the displayed error.  Their positive overlap is
the finite reason the controller cannot stall at squared norm `2`.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Sector.Budget

/-- The common positive slack used by the two output branches. -/
def allowance : Fraction.Rational :=
  13 / 6 - (16 / 15) * 2

/-- The common redundant-output slack is strictly positive. -/
theorem allowance_pos : 0 <
  allowance := by
  unfold allowance
  rw [Purelib.Data.Rat.Fraction.Constants.scaledTwo]
  decide

/-- Adding the scaled sector bound to the common slack gives one half. -/
theorem allowance_sector_identity :
    allowance + (16 / 15) * (7 / 16) = (1 / 2 :
      Fraction.Rational) := by
  unfold allowance
  rw [Purelib.Data.Rat.Fraction.Constants.scaledTwo,
    Purelib.Data.Rat.Fraction.Constants.scaledSectorBound]
  decide

/-- The unary threshold plus the common slack equals thirteen sixths. -/
theorem unaryThreshold_add_allowance :
    (16 / 15 : Fraction.Rational) * 2 + allowance = 13 / 6 := by
  unfold allowance
  ring1

/-- A uniform squared-error request small enough for either branch. -/
def uniformRadiusSq : Fraction.Rational :=
  allowance / 16

/-- The uniform redundant-output squared-radius request is strictly positive. -/
theorem uniformRadiusSq_pos : 0 <
  uniformRadiusSq :=
  Fraction.Order.Field.div_pos_direct allowance_pos (by decide)

/-- A squared radius below the uniform request remains below the slack after scaling by sixteen. -/
theorem scaled_radius_lt_allowance {radiusSq :
  Fraction.Rational}
    (small : radiusSq < uniformRadiusSq) :
    16 * radiusSq < allowance := by
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide : (0 : Fraction.Rational) < 16) small
  calc
    16 * radiusSq < 16 * uniformRadiusSq := scaled
    _ = allowance := by
      unfold uniformRadiusSq
      calc
        16 * (allowance / 16) =
          (allowance / 16) * 16 :=
          Fraction.Field.mul_comm _ _
        _ = allowance :=
          Fraction.Field.div_mul_cancel_of_ne allowance 16
            (by decide)
end Purelib.Approximation.Gaussian.Enclosure.Sector.Budget

end
