module

public import Purelib.Approximation.Rational.Grid.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Squared rational grid error

The original nearest-coordinate bounds give a squared error bounded by the squared
half-mesh for every positive natural denominator.
-/

public section

namespace Purelib.Approximation.Rational.Grid.Bounds

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt
open Purelib.Geometry.Rational

/-- Squared coordinate error of nearest rounding to a positive natural grid. -/
theorem gridCoordinate_offset_sq_le (center : Fraction.Rational) {denominator : Nat}
    (positive : 0 < denominator) :
    (Grid.Basic.gridCoordinate center denominator - center) ^ 2 ≤
      ((1 / 2 : Fraction.Rational) / denominator) ^ 2 := by
  let halfMesh := (1 / 2 : Fraction.Rational) / denominator
  have bounds := Grid.Basic.gridCoordinate_bounds center positive
  have lower : -halfMesh ≤
      Grid.Basic.gridCoordinate center denominator - center := by
    calc
      -halfMesh = (center - halfMesh) - center := by ring1
      _ ≤ Grid.Basic.gridCoordinate center denominator - center :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct bounds.1.le center
  have upper :
      Grid.Basic.gridCoordinate center denominator - center ≤
        halfMesh := by
    calc
      Grid.Basic.gridCoordinate center denominator - center ≤
          (center + halfMesh) - center :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct bounds.2 center
      _ = halfMesh := by ring1
  have squareBound := Box.sq_le_endpoint_max lower upper
  dsimp only [halfMesh] at squareBound ⊢
  rw [show (-((1 / 2 : Fraction.Rational) / denominator)) ^ 2 =
      ((1 / 2 : Fraction.Rational) / denominator) ^ 2 by ring1,
    Fraction.Order.Basic.max_self] at squareBound
  exact squareBound

end Purelib.Approximation.Rational.Grid.Bounds
