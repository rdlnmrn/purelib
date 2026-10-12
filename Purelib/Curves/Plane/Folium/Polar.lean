module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Coordinates.Polar.Squared
-- The displayed public scalar polynomial retains these numeral and negation parents.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

/-!
# The folium equation in squared polar coordinates

Retained Cartesian squares and their spread/quadrance witnesses express the
folium equation as a finite scalar polar polynomial. The supplied nonzero
radial quadrance justifies cancelling the two retained quadrance factors.
-/

namespace Purelib.Curves.Plane.Folium.Polar.RationalPolarCatalogue

open Purelib.Algebra.Field
open Purelib.Geometry.Coordinates.Polar
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

variable {K : Type*} [ExplicitField K]

/-- The folium equation implies the displayed rational polar polynomial when radial quadrance is nonzero.

The squared-coordinate witnesses and nonzero quadrance justify cancelling the two quadrance factors after the finite
polynomial calculation. -/
public theorem folium_rational_polar
    (x y spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : Squared.RationalPolarCatalogue.PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (foliumEquation : x ^ 3 + y ^ 3 + 3 * x * y = 0) :
    (2 * spread - 1) ^ 2 * (spread ^ 2 - spread + 1) ^ 2 * Q ^ 2 -
        18 * spread * (1 - spread) *
          (1 - 3 * spread + 3 * spread ^ 2) * Q +
        81 * spread ^ 2 * (1 - spread) ^ 2 = 0 := by
  have squareCoordinates :=
    Squared.polar_coordinate_squares
      (x ^ 2) (y ^ 2) spread Q coordinates
  have productSquare :
      (x * y) ^ 2 = spread * (1 - spread) * Q ^ 2 := by
    calc
      (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring1
      _ = spread * (1 - spread) * Q ^ 2 := by
        rw [squareCoordinates.1, squareCoordinates.2]
        ring1
  have sumSquare : (x + y) ^ 2 = Q + 2 * (x * y) := by
    rw [coordinates.1]
    ring1
  have factoredFolium :
      (x + y) * (Q - x * y) + 3 * x * y = 0 := by
    calc
      (x + y) * (Q - x * y) + 3 * x * y =
          x ^ 3 + y ^ 3 + 3 * x * y := by
        rw [coordinates.1]
        ring1
      _ = 0 := foliumEquation
  have factorEquality :
      (x + y) * (Q - x * y) = -(3 * x * y) := by
    calc
      (x + y) * (Q - x * y) =
          ((x + y) * (Q - x * y) + 3 * x * y) +
            -(3 * x * y) := by ring1
      _ = -(3 * x * y) := by rw [factoredFolium]; ring1
  have squaredFactor :
      (x + y) ^ 2 * (Q - x * y) ^ 2 = (3 * x * y) ^ 2 := by
    calc
      (x + y) ^ 2 * (Q - x * y) ^ 2 =
          ((x + y) * (Q - x * y)) ^ 2 := by ring1
      _ = (-(3 * x * y)) ^ 2 := by rw [factorEquality]
      _ = (3 * x * y) ^ 2 := by ring1
  let linearResidual : K :=
    2 * spread * (1 - spread) * (x * y) +
      Q * (1 - 3 * spread * (1 - spread)) -
      9 * spread * (1 - spread)
  have scaledLinear : Q ^ 2 * linearResidual = 0 := by
    calc
      Q ^ 2 * linearResidual =
          Q ^ 3 - 3 * Q *
              (spread * (1 - spread) * Q ^ 2) +
            2 * (x * y) * (spread * (1 - spread) * Q ^ 2) -
            9 * (spread * (1 - spread) * Q ^ 2) := by
        dsimp only [linearResidual]
        ring1
      _ = Q ^ 3 - 3 * Q * (x * y) ^ 2 +
            2 * (x * y) * (x * y) ^ 2 - 9 * (x * y) ^ 2 := by
        rw [productSquare]
      _ =
          (Q + 2 * (x * y)) * (Q - x * y) ^ 2 -
            (3 * x * y) ^ 2 := by ring1
      _ = (x + y) ^ 2 * (Q - x * y) ^ 2 -
            (3 * x * y) ^ 2 := by rw [sumSquare]
      _ = 0 := by rw [squaredFactor]; ring1
  have onceCancelled : Q * linearResidual = 0 := by
    apply ExplicitField.eq_zero_of_mul_eq_zero_left QNonzero
    calc
      Q * (Q * linearResidual) = Q ^ 2 * linearResidual := by ring1
      _ = 0 := scaledLinear
  have linearZero : linearResidual = 0 :=
    ExplicitField.eq_zero_of_mul_eq_zero_left QNonzero onceCancelled
  have centeredEquality :
      Q * (1 - 3 * spread * (1 - spread)) -
          9 * spread * (1 - spread) =
        -(2 * spread * (1 - spread) * (x * y)) := by
    calc
      Q * (1 - 3 * spread * (1 - spread)) -
          9 * spread * (1 - spread) =
        linearResidual + -(2 * spread * (1 - spread) * (x * y)) := by
          dsimp only [linearResidual]
          ring1
      _ = -(2 * spread * (1 - spread) * (x * y)) := by
        rw [linearZero]
        ring1
  calc
    (2 * spread - 1) ^ 2 * (spread ^ 2 - spread + 1) ^ 2 * Q ^ 2 -
          18 * spread * (1 - spread) *
            (1 - 3 * spread + 3 * spread ^ 2) * Q +
          81 * spread ^ 2 * (1 - spread) ^ 2 =
        (Q * (1 - 3 * spread * (1 - spread)) -
            9 * spread * (1 - spread)) ^ 2 -
          4 * spread ^ 2 * (1 - spread) ^ 2 * (x * y) ^ 2 := by
      rw [productSquare]
      ring1
    _ = (Q * (1 - 3 * spread * (1 - spread)) -
            9 * spread * (1 - spread)) ^ 2 -
          (2 * spread * (1 - spread) * (x * y)) ^ 2 := by ring1
    _ = (-(2 * spread * (1 - spread) * (x * y))) ^ 2 -
          (2 * spread * (1 - spread) * (x * y)) ^ 2 := by
      rw [centeredEquality]
    _ = 0 := by ring1

end Purelib.Curves.Plane.Folium.Polar.RationalPolarCatalogue
