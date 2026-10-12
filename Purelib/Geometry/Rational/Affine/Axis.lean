module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
public import Purelib.Data.Gaussian.Cast.Imaginary
public import Purelib.Data.Gaussian.Components.Basic
public import Purelib.Data.Gaussian.Constants
public import Purelib.Geometry.Rational.Affine

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Cast

open Purelib.Data.Rat

open Purelib.Geometry.Rational

section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.SylvesterBezout

end Purelib.Polynomial.Elimination.SylvesterBezout

section
namespace Purelib.Geometry.Rational.Affine.Axis

open _root_.Purelib.Polynomial.Elimination.SylvesterBezout
/-- Conjugating the reflection across the vertical axis through the real coordinate recovers the original point. -/
public theorem verticalReflection (x y :
  Fraction.Rational) :
    Data.Gaussian.Basic.conj
      (2 * Path.ofCoordinate x -
        Components.Basic.point x y) =
      Components.Basic.point x y := by
  rw [show (2 : Data.Gaussian.Basic.Canonical) *
      Path.ofCoordinate x =
    Path.ofCoordinate x +
      Path.ofCoordinate x by ring1]
  apply Data.Gaussian.Basic.ext
  · simp only [Data.Gaussian.Basic.conj,
      Path.ofCoordinate,
      Components.Basic.point,
      Basic.add_re,
      Basic.sub_re]
    ring1
  · simp only [Data.Gaussian.Basic.conj,
      Path.ofCoordinate,
      Components.Basic.point,
      Basic.add_im,
      Basic.sub_im]
    ring1
end Purelib.Geometry.Rational.Affine.Axis
end

namespace Purelib.Geometry.Rational.Affine.Axis

/-- The downward unit Gaussian direction with coordinates zero and minus one. -/
def negativeVerticalDirection : Data.Gaussian.Basic.Canonical := ⟨0, -1⟩

/-- The downward affine line through a real base has coordinates given by the base and negated parameter. -/
@[simp] theorem line_negativeVertical (y x : Fraction.Rational) :
    Affine.line
      (Winding.verticalBase y) negativeVerticalDirection x =
      Components.Basic.point y (-x) := by
  apply Data.Gaussian.Basic.ext
  · change y + (x * 0 - 0 * -1) = y
    ring1
  · change 0 + (x * -1 + 0 * 0) = -x
    ring1

/-- Multiplication by the imaginary unit rotates the point with coordinates y and minus x to the point with coordinates
x and y. -/
@[simp] theorem quarterTurn_horizontalPoint (x y : Fraction.Rational) :
    Components.Basic.point y (-x) * Constants.imaginaryUnit =
      Components.Basic.point x y := by
  apply Data.Gaussian.Basic.ext
  · change y * 0 - -x * 1 = x
    ring1
  · change y * 1 + -x * 0 = y
    ring1
end Purelib.Geometry.Rational.Affine.Axis

end

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.Geometry.Rational.Affine.Axis

/-- The horizontal affine line at height y has Cartesian coordinates t and y. -/
@[simp] theorem line_horizontal (y t : Fraction.Rational) :
    Affine.line (Imaginary.horizontalBase y) Constants.horizontalDirection t = Components.Basic.point t y := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [Affine.line, Imaginary.horizontalBase, Constants.horizontalDirection, Components.Basic.point,
      Basic.add_re,
      Basic.add_im, Basic.mul_re, Basic.mul_im, Cast.ofCoordinate_re, Cast.ofCoordinate_im] <;>
    ring1

/-- The vertical affine line at real coordinate x has Cartesian coordinates x and t. -/
@[simp] theorem line_vertical (x t : Fraction.Rational) :
    Affine.line (Winding.verticalBase x) Constants.imaginaryUnit t = Components.Basic.point x t := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [Affine.line, Winding.verticalBase, Constants.imaginaryUnit, Components.Basic.point, Basic.add_re,
      Basic.add_im, Basic.mul_re, Basic.mul_im, Cast.ofCoordinate_re, Cast.ofCoordinate_im] <;>
    ring1
end Purelib.Geometry.Rational.Affine.Axis

end
