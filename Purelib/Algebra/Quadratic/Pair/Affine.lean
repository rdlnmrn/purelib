module

public import Purelib.Algebra.Quadratic.Pair.Basic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Tactic.Ring

/-!
# Affine rows in the original quadratic pair ring

The scalar and generator coordinates of an affine row are read directly from
the original pair operations. Over canonical rationals, a nonzero integral
row cannot vanish at a pair with nonzero generator coordinate.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair

open Purelib.Data.Rat.Fraction

variable {K : Type} {parameter : K}

/-- Apply the scalar affine row to an original pair in its unchanged square parameter. -/
@[expose] def affine [CommRing K] (constant coefficient : K) (value : Pair K parameter) : Pair K parameter :=
  scalar constant + scalar coefficient * value

/-- Read the affine row's unit coefficient from the original scalar coefficients and pair. -/
theorem affine_re [CommRing K] (constant coefficient : K) (value : Pair K parameter) :
    (affine constant coefficient value).re = constant + coefficient * value.re := by
  simp only [affine, add_re, scalar_re, scalar_im, mul_re]
  ring1

/-- Read the affine row's generator coefficient as the original row coefficient times the original generator field. -/
theorem affine_im [CommRing K] (constant coefficient : K) (value : Pair K parameter) :
    (affine constant coefficient value).im = coefficient * value.im := by
  simp only [affine, add_im, scalar_im, scalar_re, mul_im]
  ring1

/-- A nonzero integer has a nonzero canonical rational cast. -/
private theorem integer_nonzero (value : Int) (nonzero : value ≠ 0) : (value : Rational) ≠ 0 := by
  intro zero
  exact nonzero (Cast.Order.intCast_injective_direct (left := value) (right := 0) zero)

/-- Every nonzero integral affine row is nonzero at an original rational pair with nonzero generator coordinate. -/
theorem affine_ne_zero_integer {parameter : Rational} (value : Pair Rational parameter)
    (generator_ne : value.im ≠ 0) (constant coefficient : Int)
    (row_ne : constant ≠ 0 ∨ coefficient ≠ 0) :
    affine (constant : Rational) (coefficient : Rational) value ≠ 0 := by
  by_cases coefficient_zero : coefficient = 0
  · have constant_ne : constant ≠ 0 := by
      cases row_ne with
      | inl nonzero => exact nonzero
      | inr nonzero => exact False.elim (nonzero coefficient_zero)
    have coefficient_cast : (coefficient : Rational) = 0 := by
      rewrite [coefficient_zero]
      rfl
    intro zero
    have real := congrArg Pair.re zero
    rewrite [affine_re, coefficient_cast, Field.zero_mul_direct, _root_.add_zero] at real
    exact integer_nonzero constant constant_ne real
  · have product_ne := Field.mul_ne_zero_direct (integer_nonzero coefficient coefficient_zero) generator_ne
    intro zero
    have imaginary := congrArg Pair.im zero
    rewrite [affine_im] at imaginary
    exact product_ne imaginary

end Purelib.Algebra.Quadratic.Pair

end
