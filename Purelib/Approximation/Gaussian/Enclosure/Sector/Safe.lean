module
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Sector.Eight.Margin
public import Purelib.Geometry.Rational.Sector.Eight.Safe
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Data.ComplexContinuedFraction.Encoding (Sector)

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Sector

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat

open Purelib.Geometry.Rational.Sector.Eight

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

namespace Purelib.Approximation.Gaussian.Enclosure.Sector.Safe

/-- A finite inequality certifying that the entire ball lies in one overlapping safe sector. -/
def SafeBall (sector :
  Sector) (ball :
  Ball) : Prop :=
  16 * ball.radiusSq +
      (16 / 15) * Data.Gaussian.Norm.Basic.normSq (ball.center - sector.rep) < 1 / 2

/-- Decide the whole-ball sufficient sector test by exact rational comparison. -/
instance safeBallDecidable (sector :
  Sector)
  (ball : Ball) :
    Decidable (SafeBall sector ball) := by
  unfold SafeBall
  infer_instance

/-- Every reading admitted by a ball passing the sufficient sector test lies in that same safe sector. -/
theorem safe_of_contains {sector :
  Sector}
  {ball : Ball} {value : Data.Gaussian.Basic.Canonical}
    (certificate : SafeBall sector ball) (inside : ball.Contains value) :
    Geometry.Rational.Sector.Eight.Safe sector value := by
  have difference :
      value - sector.rep =
        (value - ball.center) + (ball.center - sector.rep) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  have weighted := Weighted.normSq_add_le_weighted
    (value - ball.center) (ball.center - sector.rep)
  unfold Geometry.Rational.Sector.Eight.Safe
  rw [difference]
  exact weighted.trans_lt
    (lt_of_le_of_lt
      (add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          inside (by decide)) le_rfl)
      certificate)

/-- Every uniformly fine ball centred in the enlarged band has a finite safe sector certificate, selected by the
original eight-row table at its rational centre. -/
theorem safeBall_of_extendedBand {ball :
    Ball}
    (band : Margin.ExtendedBand ball.center)
    (small : ball.radiusSq < Budget.uniformRadiusSq) :
    SafeBall (Sector.select
      ball.center) ball := by
  have scaledRadius := Budget.scaled_radius_lt_allowance small
  have residual :=
    Margin.extendedBand_residual_le_seven_sixteenths
      band
  unfold SafeBall
  have scaledResidual :
      (16 / 15) *
          Data.Gaussian.Norm.Basic.normSq (ball.center -
            (Sector.select ball.center).rep) ≤
        (16 / 15) * (7 / 16) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      residual (by decide)
  calc
    16 * ball.radiusSq +
        (16 / 15) *
          Data.Gaussian.Norm.Basic.normSq (ball.center -
            (Sector.select ball.center).rep) <
        Budget.allowance + (16 / 15) * (7 / 16) :=
      calc
        16 * ball.radiusSq +
            (16 / 15) *
              Data.Gaussian.Norm.Basic.normSq (ball.center -
                (Sector.select ball.center).rep) <
            Budget.allowance +
              (16 / 15) *
                Data.Gaussian.Norm.Basic.normSq (ball.center -
                  (Sector.select ball.center).rep) :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct
            scaledRadius _
        _ ≤ Budget.allowance + (16 / 15) * (7 / 16) :=
          add_le_add_right scaledResidual Budget.allowance
    _ = 1 / 2 := Budget.allowance_sector_identity
end Purelib.Approximation.Gaussian.Enclosure.Sector.Safe

end
