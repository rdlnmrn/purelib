module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Exact squared-norm bounds for the original cap power coordinate -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical sub_zero)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Box.Square.Centered

variable {genus : Nat}

/-- The original identity-or-square cap coordinate decreases squared norm on the unit disk.

The actual curve's original reciprocal origin order chooses its same
power coordinate. The squared branch uses only the explicit nonnegative
unit quadrance bound; no root or sheet coordinate is selected.
-/
theorem point_normSq_le (curve : HyperellipticCurve genus) (parameter : Canonical)
    (unitBound : Norm.Basic.normSq parameter ≤ 1) :
    Norm.Basic.normSq (point curve parameter) ≤ Norm.Basic.normSq parameter := by
  rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
  · rewrite [point, degree, regular, pow_one]
    exact Fraction.Order.Basic.le_refl _
  · rewrite [point, degree, branch, Norm.Power.normSq_pow, pow_two]
    have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct unitBound
      (Norm.Basic.normSq_nonneg parameter)
    exact bounded.trans_eq (Fraction.Field.mul_one_direct _)

/-- The same original cap power lies in a displayed symmetric square when the parameter quadrance pays its radius.

Both actual degree parities consume the same coordinate norm estimate.
The explicit nonnegative radius and squared-radius bound supply both
signed coordinate inequalities in the original finite rational box.
-/
theorem point_in_square (curve : HyperellipticCurve genus) (parameter : Canonical)
    (unitBound : Norm.Basic.normSq parameter ≤ 1) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius)
    (radiusBound : Norm.Basic.normSq parameter ≤ radius ^ 2) :
    (Box.symmetric radius nonnegative).Contains (point curve parameter) := by
  have centered := centeredBox_contains_of_normSq_sub_le
    (center := (0 : Canonical)) (value := point curve parameter) nonnegative (by
    rewrite [sub_zero]
    exact (point_normSq_le curve parameter unitBound).trans radiusBound)
  change (0 - radius ≤ (point curve parameter).re ∧ (point curve parameter).re ≤ 0 + radius ∧
    0 - radius ≤ (point curve parameter).im ∧ (point curve parameter).im ≤ 0 + radius) at centered
  rewrite [show (0 : Fraction.Rational) - radius = -radius by ring1, Fraction.Field.zero_add] at centered
  exact centered

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

end
