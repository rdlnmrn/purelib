module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Exercise 16.8: rational polar form

A Cartesian point is used as a finite Gaussian pair.  Multiplication and
scaling are explicit coordinate operations; no completed complex carrier is
introduced.  The unit-circle parameter is recovered by the finite quotient
`y / (1+x)`, and the chord through `-1` has the displayed equation
`lambda*x-y+lambda=0`.

The multiplication theorem uses the same `turnComposition` operation as
Exercise 9.2.  Its premise `1-lambda₁*lambda₂ != 0` is essential: when it
vanishes, the product unit point is the excluded point `[-1,0]`, so the finite
chart has no resulting parameter.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- Multiplication of finite Gaussian coordinate pairs. -/
def gaussianMul (left right : Plane.Point K) :
  Plane.Point K :=
  ⟨left.x * right.x - left.y * right.y,
    left.x * right.y + left.y * right.x⟩

/-- Scalar multiplication of a finite Gaussian coordinate pair. -/
def gaussianScale (scalar : K) (point : Plane.Point K) :
  Plane.Point K :=
  ⟨scalar * point.x, scalar * point.y⟩

/-- The Gaussian pair corresponding to `1+i*lambda`. -/
def onePlusIParameter (parameter : K) : Plane.Point K :=
  ⟨1, parameter⟩

/-- Squaring `1+i*lambda` gives the numerator printed in Exercise 16.8. -/
theorem gaussianSquare_onePlusIParameter (parameter : K) :
    gaussianMul (onePlusIParameter parameter)
        (onePlusIParameter parameter) =
      (⟨1 - parameter ^ 2, 2 * parameter⟩ : Plane.Point K) := by
  apply Plane.Point.ext <;> unfold gaussianMul
    onePlusIParameter <;>
    dsimp only <;> ring1

/-- Gaussian multiplication commutes with two displayed scalar factors. -/
theorem gaussianMul_scale_scale
    (leftScalar rightScalar : K) (left right : Plane.Point K) :
    gaussianMul (gaussianScale leftScalar left)
        (gaussianScale rightScalar right) =
      gaussianScale (leftScalar * rightScalar)
        (gaussianMul left right) := by
  apply Plane.Point.ext <;> unfold gaussianMul
    gaussianScale <;>
    dsimp only <;> ring1

/-- Two successive Gaussian scalings multiply their scalar factors. -/
theorem gaussianScale_scale (first second : K) (point :
  Plane.Point K) :
    gaussianScale first (gaussianScale second point) =
      gaussianScale (first * second) point := by
  apply Plane.Point.ext <;> unfold gaussianScale <;> dsimp only <;> ring1

/-- The product of two Gaussian squares is the square of the product. -/
theorem gaussianMul_squares (left right : Plane.Point K) :
    gaussianMul (gaussianMul left left)
      (gaussianMul right right) =
      gaussianMul (gaussianMul left right)
        (gaussianMul left right) := by
  apply Plane.Point.ext <;> unfold gaussianMul <;> dsimp only <;> ring1

/-- Multiplying `1+i*left` and `1+i*right` exposes the numerator and denominator of the rational turn-composition
parameter. -/
theorem gaussianMul_onePlusIParameter (left right : K) :
    gaussianMul (onePlusIParameter left)
      (onePlusIParameter right) =
      (⟨1 - left * right, left + right⟩ : Plane.Point K) := by
  apply Plane.Point.ext <;> unfold gaussianMul
    onePlusIParameter <;>
    dsimp only <;> ring1
end

end Purelib.Curves.Plane.Conic

end
