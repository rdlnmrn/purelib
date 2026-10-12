module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.PositiveMul
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace Purelib.Geometry.Plane.Sector.Rational.Type

section

/-- The affine point obtained by scaling the displacement from the base point.

The definition accepts any rational scale; preservation of sector type requires a positive scale. -/
def rayRepresentative (base point : Geometry.Plane.Point
  Fraction.Rational) (scale : Fraction.Rational) :
    Geometry.Plane.Point Fraction.Rational :=
  Affine.affineCombination (1 - scale) base scale point

/-- The scalar whose sign defines the book's acute/obtuse sector type. -/
def sectorTypeScalar
    (base first second : Geometry.Plane.Point Fraction.Rational) : Fraction.Rational :=
  Quadrance.quadrance base first + Quadrance.quadrance base second - Quadrance.quadrance first second

/-- Changing the displayed point on either ray by positive scaling multiplies the type scalar by the product of those
scales. -/
theorem sectorTypeScalar_rayRepresentative
    (base first second : Geometry.Plane.Point Fraction.Rational) (firstScale secondScale : Fraction.Rational) :
    sectorTypeScalar base
        (rayRepresentative base first firstScale)
        (rayRepresentative base second secondScale) =
      firstScale * secondScale * sectorTypeScalar base first second := by
  unfold sectorTypeScalar rayRepresentative Quadrance.quadrance
    Affine.affineCombination
  ring1

/-- Exercise 20.2: the acute and obtuse tests do not depend on which positive representative point is chosen on either
bounding ray. -/
theorem exercise_20_2
    (base first second : Geometry.Plane.Point Fraction.Rational)
    (firstScale secondScale : Fraction.Rational)
    (firstScalePositive : 0 < firstScale)
    (secondScalePositive : 0 < secondScale) :
    (0 ≤ sectorTypeScalar base
        (rayRepresentative base first firstScale)
        (rayRepresentative base second secondScale) ↔
      0 ≤ sectorTypeScalar base first second) ∧
    (sectorTypeScalar base
        (rayRepresentative base first firstScale)
        (rayRepresentative base second secondScale) ≤ 0 ↔
      sectorTypeScalar base first second ≤ 0) := by
  have productPositive : 0 < firstScale * secondScale :=
    Fraction.Order.Arithmetic.mul_pos_direct firstScalePositive
      secondScalePositive
  constructor
  · rw [sectorTypeScalar_rayRepresentative]
    exact Fraction.Order.PositiveMul.nonnegative_mul_iff_of_positive _ _ productPositive
  · rw [sectorTypeScalar_rayRepresentative]
    exact Fraction.Order.PositiveMul.nonpositive_mul_iff_of_positive _ _ productPositive
end
end Purelib.Geometry.Plane.Sector.Rational.Type

end
