module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.NatCast
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Rounding.Nearest

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Nearest rational grid coordinates

The common denominator is one more than the floor of the reciprocal half-radius. Nearest
rounding retains its upward half-integer tie convention and its exact coordinate error
bounds.
-/

public section

namespace Purelib.Approximation.Rational.Grid.Basic

open Purelib
open Purelib.Algebra
open Purelib.Data.Rat
open Purelib.Data.Rat.Rounding
open Purelib.Data

/-- Common grid denominator for a positive radius, using the half-mesh guarantee supplied by
nearest-integer rounding. -/
@[expose] def gridDenominator (radius : Fraction.Rational) : Nat :=
  (Floor.floor
    (Fraction.Arithmetic.normalizedDiv (1 / 2 : Fraction.Rational) radius)).toNat + 1

/-- The computed nearest-rounding grid denominator is a positive natural number. -/
theorem gridDenominator_pos (radius : Fraction.Rational) :
    0 < gridDenominator radius := by
  exact Nat.zero_lt_succ _

/-- Half the grid mesh is strictly smaller than the requested positive radius. -/
theorem half_reciprocal_gridDenominator_lt {radius : Fraction.Rational}
    (positive : 0 < radius) :
    (1 / 2 : Fraction.Rational) / (gridDenominator radius : Fraction.Rational) < radius := by
  let reciprocal := (1 / 2 : Fraction.Rational) / radius
  have reciprocalNonnegative : (0 : Fraction.Rational) ≤ reciprocal :=
    (Fraction.Order.Field.div_pos_direct (by decide) positive).le
  have floorNonnegative :
      0 ≤ Floor.floor reciprocal := by
    exact (Floor.intCast_le_iff_floor 0 reciprocal).mp
      reciprocalNonnegative
  have denominatorCast :
      (gridDenominator radius : Fraction.Rational) =
        ((Floor.floor reciprocal + 1 : Int) :
          Fraction.Rational) := by
    unfold gridDenominator
    simp only [Fraction.Arithmetic.normalizedDiv_eq]
    dsimp only [reciprocal]
    have retainedFloor : ((Floor.floor reciprocal).toNat : Int) = Floor.floor reciprocal := by
      cases value : Floor.floor reciprocal with
      | ofNat value => rfl
      | negSucc value => simp only [value] at floorNonnegative; cases floorNonnegative
    rw [NatCast.add, Nat.cast_one, ← Int.cast_natCast,
      retainedFloor, Fraction.Cast.intCast_add_direct, Int.cast_one]
  have reciprocalStrict :
      reciprocal < (gridDenominator radius : Fraction.Rational) := by
    rw [denominatorCast]
    exact Rounding.Floor.lt_intCast_floor_add_one reciprocal
  have denominatorPositive :
      (0 : Fraction.Rational) < (gridDenominator radius : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (gridDenominator_pos radius)
  apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).mpr
  have scaled :=
    (Fraction.Order.Field.div_lt_iff_pos positive).mp reciprocalStrict
  calc
    (1 / 2 : Fraction.Rational) <
        (gridDenominator radius : Fraction.Rational) * radius := scaled
    _ = radius * (gridDenominator radius : Fraction.Rational) := by ring1

/-- The computed denominator is the least positive natural denominator whose half-mesh is
strictly smaller than the requested radius. -/
theorem gridDenominator_minimal {radius : Fraction.Rational} (radiusPositive : 0 < radius)
    {candidate : Nat} (candidatePositive : 0 < candidate)
    (mesh : (1 / 2 : Fraction.Rational) / (candidate : Fraction.Rational) < radius) :
    gridDenominator radius ≤ candidate := by
  let reciprocal := (1 / 2 : Fraction.Rational) / radius
  have candidateCastPositive : (0 : Fraction.Rational) < (candidate : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct candidatePositive
  have halfLtScaled :=
    (Fraction.Order.Field.div_lt_iff_pos candidateCastPositive).mp mesh
  have reciprocalLtCandidate : reciprocal < (candidate : Fraction.Rational) := by
    apply (Fraction.Order.Field.div_lt_iff_pos radiusPositive).mpr
    calc
      (1 / 2 : Fraction.Rational) < radius * (candidate : Fraction.Rational) := halfLtScaled
      _ = (candidate : Fraction.Rational) * radius := by ring1
  have reciprocalNonnegative : (0 : Fraction.Rational) ≤ reciprocal :=
    (Fraction.Order.Field.div_pos_direct (by decide) radiusPositive).le
  have floorNonnegative :
      0 ≤ Floor.floor reciprocal :=
    (Floor.intCast_le_iff_floor 0 reciprocal).mp
      reciprocalNonnegative
  have floorLtCandidateInt :
      Floor.floor reciprocal < (candidate : Int) := by
    apply Int.Order.lt_of_not_le
    intro candidateLeFloor
    have candidateLeReciprocal :=
      (Floor.intCast_le_iff_floor
        (candidate : Int) reciprocal).mpr candidateLeFloor
    have castIdentity : ((candidate : Int) : Fraction.Rational) =
        (candidate : Fraction.Rational) := by rw [Int.cast_natCast]
    rw [castIdentity] at candidateLeReciprocal
    exact (not_lt_of_ge candidateLeReciprocal) reciprocalLtCandidate
  have floorLtCandidate :
      (Floor.floor reciprocal).toNat < candidate := by
    have retainedFloor : ((Floor.floor reciprocal).toNat : Int) = Floor.floor reciprocal := by
      cases value : Floor.floor reciprocal with
      | ofNat value => rfl
      | negSucc value => simp only [value] at floorNonnegative; cases floorNonnegative
    apply Int.Order.natCast_lt_iff.mp
    rewrite [retainedFloor]
    exact floorLtCandidateInt
  unfold gridDenominator
  simp only [Fraction.Arithmetic.normalizedDiv_eq]
  dsimp only [reciprocal] at floorLtCandidate
  exact Nat.succ_le_of_lt floorLtCandidate

/-- The nearest grid coordinate to a displayed rational center, with half-integer ties sent
upward. -/
@[expose] def gridCoordinate (center : Fraction.Rational) (denominator : Nat) : Fraction.Rational :=
  Fraction.Arithmetic.normalizedDiv
    (Nearest.nearestCoordinate
      (Fraction.Arithmetic.normalizedMul
        (denominator : Fraction.Rational) center) : Int)
    (denominator : Fraction.Rational)

/-- Nearest rounding places the grid coordinate strictly above the lower half-mesh endpoint
and weakly below the upper endpoint. -/
theorem gridCoordinate_bounds (center : Fraction.Rational) {denominator : Nat}
    (positive : 0 < denominator) :
    center - (1 / 2 : Fraction.Rational) / denominator <
        gridCoordinate center denominator ∧
      gridCoordinate center denominator ≤
        center + (1 / 2 : Fraction.Rational) / denominator := by
  simp only [gridCoordinate, Fraction.Arithmetic.normalizedDiv_eq,
    Fraction.Arithmetic.normalizedMul_eq]
  have denominatorPositive : (0 : Fraction.Rational) < (denominator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct positive
  let scaledCenter := (denominator : Fraction.Rational) * center
  let selected := Nearest.nearestCoordinate scaledCenter
  have error := Nearest.nearestCoordinate_error_bounds scaledCenter
  have halfCancel :
      ((1 / 2 : Fraction.Rational) / (denominator : Fraction.Rational)) *
          (denominator : Fraction.Rational) = 1 / 2 :=
    Algebra.Field.ExplicitField.div_mul_cancel _ (ne_of_gt denominatorPositive)
  constructor
  · apply (Fraction.Order.Field.lt_div_iff_pos
      denominatorPositive).mpr
    have translated := Fraction.Order.Arithmetic.add_lt_add_right_direct
      error.2 ((selected : Fraction.Rational) - 1 / 2)
    calc
      (center - (1 / 2 : Fraction.Rational) / denominator) * denominator =
          scaledCenter - 1 / 2 := by
        rw [sub_mul, halfCancel]
        dsimp only [scaledCenter]
        ring1
      _ = (scaledCenter - (selected : Fraction.Rational)) +
          ((selected : Fraction.Rational) - 1 / 2) := by ring1
      _ < (1 / 2 : Fraction.Rational) +
          ((selected : Fraction.Rational) - 1 / 2) := translated
      _ = (selected : Fraction.Rational) := by ring1
  · apply (Fraction.Order.Field.div_le_iff_pos
      denominatorPositive).mpr
    have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
      error.1 ((selected : Fraction.Rational) + 1 / 2)
    calc
      (selected : Fraction.Rational) =
          -(1 / 2 : Fraction.Rational) +
            ((selected : Fraction.Rational) + 1 / 2) := by ring1
      _ ≤ (scaledCenter - (selected : Fraction.Rational)) +
          ((selected : Fraction.Rational) + 1 / 2) := translated
      _ = (center + (1 / 2 : Fraction.Rational) / denominator) * denominator := by
        rw [add_mul, halfCancel]
        dsimp only [scaledCenter]
        ring1

end Purelib.Approximation.Rational.Grid.Basic
