module
import Purelib.Data.List.Append
import Purelib.Data.Nat.Subtraction
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

section
open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Encoding.Cylinder.Basic
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Geometry.Projective.Line.Basic
public section

/-!
# Rational diameter content of finite CCL cylinders

The quantity here is explicitly a geometric squared-diameter budget, not a
probability mass.  Every statement concerns a supplied finite block list and
supplied finite realization certificates.
-/

namespace Purelib.Approximation.CCL.Cylinder

/-- Canonical rational squared-chordal spread of a completed-block prefix. -/
@[expose] def cylinderSpread (blocks : List Block) : Fraction.Rational :=
  (1 / 2 : Fraction.Rational) ^ blocks.length

/-- The canonical squared-chordal spread of a finite completed-block prefix is nonnegative. -/
theorem cylinderSpread_nonneg (blocks : List Block) :
    0 ≤ cylinderSpread blocks :=
  Arithmetic.pow_nonneg_direct (by decide) blocks.length

/-- The canonical squared-chordal spread of a finite completed-block prefix is at most one. -/
theorem cylinderSpread_le_one (blocks : List Block) :
    cylinderSpread blocks ≤ 1 :=
  Dyadic.half_pow_le_one blocks.length

/-- Enclose all realized pairwise squared distances between zero and the canonical finite prefix spread. -/
@[expose] def cylinderDistanceBound (blocks : List Block) :
    Interval where
  lower := 0
  upper := cylinderSpread blocks
  valid := cylinderSpread_nonneg blocks

/-- The width of the retained rational distance enclosure is exactly the canonical prefix spread. -/
theorem cylinderDistanceBound_width (blocks : List Block) :
    (cylinderDistanceBound blocks).width = cylinderSpread blocks
      := by
  dsimp only [Interval.width, cylinderDistanceBound]
  ring1

/-- Every two supplied realizations of the finite prefix have squared chordal distance inside its rational diameter
enclosure. -/
theorem realized_distance_mem
    {blocks : List Block} {left right : Line.GaussianLine}
    (leftRealizes : Realizes blocks left)
    (rightRealizes : Realizes blocks right) :
    (cylinderDistanceBound blocks).Contains
      (Chordal.Basic.chordalSq left right) :=
  ⟨Chordal.Basic.chordalSq_nonneg left right,
    Realizes.chordalSq_le_half_pow
      leftRealizes rightRealizes⟩

/-- Adding still more completed blocks preserves a met diameter request. -/
theorem cylinderSpread_lt_of_requiredBlockCount_le
    {blocks : List Block} {target : Fraction.Rational} (positive : 0 < target)
    (enough : Dyadic.requiredBlockCount target ≤ blocks.length) :
    cylinderSpread blocks < target := by
  let extra := blocks.length - Dyadic.requiredBlockCount target
  have lengthEqual : blocks.length = Dyadic.requiredBlockCount target + extra :=
    (Data.Nat.Subtraction.add_sub_of_le enough).symm
  rw [cylinderSpread, lengthEqual, pow_add]
  have extraPowerLeOne : (1 / 2 : Fraction.Rational) ^ extra ≤ 1 := by
    have powerBound := Arithmetic.pow_le_pow_direct
      (by decide : (0 : Fraction.Rational) ≤ 1 / 2)
      (by decide : (1 / 2 : Fraction.Rational) ≤ 1) extra
    simpa only [one_pow] using powerBound
  have prefixNonnegative :
      0 ≤ (1 / 2 : Fraction.Rational) ^ Dyadic.requiredBlockCount target :=
    Arithmetic.pow_nonneg_direct (by decide) _
  calc
    (1 / 2 : Fraction.Rational) ^ Dyadic.requiredBlockCount target *
          (1 / 2 : Fraction.Rational) ^ extra ≤
        (1 / 2 : Fraction.Rational) ^ Dyadic.requiredBlockCount target * 1 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        extraPowerLeOne prefixNonnegative
    _ = (1 / 2 : Fraction.Rational) ^ Dyadic.requiredBlockCount target := by ring1
    _ < target := Dyadic.requiredBlockCount_spread_lt positive

/-- Requested-length finite CCL realizations are pairwise below the rational squared-chordal target, without selecting a
projective point. -/
theorem realized_distance_lt_requested
    {blocks : List Block} {target : Fraction.Rational} (positive : 0 < target)
    (enough : Dyadic.requiredBlockCount target ≤ blocks.length)
    {left right : Line.GaussianLine}
    (leftRealizes : Realizes blocks left)
    (rightRealizes : Realizes blocks right) :
    Chordal.Basic.chordalSq left right < target :=
  (Realizes.chordalSq_le_half_pow
    leftRealizes rightRealizes).trans_lt
      (cylinderSpread_lt_of_requiredBlockCount_le positive enough)

end Purelib.Approximation.CCL.Cylinder

end

section
public section

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

namespace Purelib.Approximation.CCL.Cylinder

/-- Appending completed-block prefixes multiplies their canonical squared-chordal spreads. -/
theorem cylinderSpread_append (stem suffix : List Block) :
    cylinderSpread (stem ++ suffix) =
      cylinderSpread stem * cylinderSpread suffix := by
  dsimp only [cylinderSpread]
  rw [Data.List.Append.length_append, pow_add]

/-- Adding completed blocks cannot increase geometric spread. -/
theorem cylinderSpread_le_of_append (stem suffix : List Block) :
    cylinderSpread (stem ++ suffix) ≤ cylinderSpread stem := by
  rw [cylinderSpread_append]
  have suffixLeOne : cylinderSpread suffix ≤ 1 := by
    have powerBound := Arithmetic.pow_le_pow_direct
      (by decide : (0 : Fraction.Rational) ≤ 1 / 2)
      (by decide : (1 / 2 : Fraction.Rational) ≤ 1) suffix.length
    simpa only [cylinderSpread, one_pow] using powerBound
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct
    suffixLeOne (cylinderSpread_nonneg stem)
  simpa only [mul_one] using scaled
end Purelib.Approximation.CCL.Cylinder

end

section
public section

/-!
# Concentration of squared-sensitive probes inside one finite CCL cylinder

For a probe satisfying a squared-separation sensitivity estimate, CCL's
`2^-k` squared-chordal cylinder contraction gives a `factor * 2^-k` second
moment bound directly.  This is the natural rate for nonconstant Lipschitz
observables and avoids selecting a square root.

Every statement concerns an explicitly supplied finite distribution and
finite realization traces.  No measure on an infinite cylinder is formed.
-/

namespace Purelib.Approximation.CCL.Cylinder

/-- Meeting the computed block count makes the sensitivity-scaled cylinder spread strictly smaller than the variance
target. -/
theorem scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
    {blocks : List Block} (target factor : Fraction.Rational)
    (targetPositive : 0 < target) (factorPositive : 0 < factor)
    (enough : Budget.requiredSquaredVarianceBlockCount target factor ≤
      blocks.length) :
    factor * cylinderSpread blocks < target := by
  have quotientPositive : 0 < target / factor :=
    Field.div_pos_direct targetPositive factorPositive
  have spreadSmall : cylinderSpread blocks < target / factor :=
    cylinderSpread_lt_of_requiredBlockCount_le quotientPositive enough
  calc
    factor * cylinderSpread blocks < factor * (target / factor) :=
      Arithmetic.mul_lt_mul_of_pos_left_direct
        factorPositive spreadSmall
    _ = target := by
      calc
        factor * (target / factor) = (target / factor) * factor :=
          Fraction.Field.mul_comm _ _
        _ = target := Fraction.Field.div_mul_cancel_of_ne
          target factor factorPositive.ne'
end Purelib.Approximation.CCL.Cylinder

end
