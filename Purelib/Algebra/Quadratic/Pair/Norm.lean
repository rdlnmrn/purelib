module

public import Purelib.Algebra.Quadratic.Pair.Basic
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Norm and conjugate inversion for the original quadratic pair

The norm uses the original square parameter: the generator squares to its
negative. Conjugate multiplication gives a scalar norm, and a nonzero norm
supplies explicit inverse coordinates. Nonsquareness of the negative parameter
ensures every nonzero pair has nonzero norm.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair

open Purelib.Algebra.Field (ExplicitField)

variable {K : Type*} {radialSquare : K}

/-- Compute the scalar norm using the original pair's retained square parameter. -/
@[expose] def norm [Mul K] [Add K] (value : Pair K radialSquare) : K :=
  value.re * value.re + radialSquare * value.im * value.im

/-- Norm preserves multiplication over the original scalar ring and square parameter. -/
theorem norm_mul [CommRing K] (left right : Pair K radialSquare) :
    (left * right).norm = left.norm * right.norm := by
  change norm (multiply left right) = norm left * norm right
  unfold norm multiply
  ring1

/-- Conjugating a pair preserves its scalar norm. -/
theorem norm_conjugate [CommRing K] (value : Pair K radialSquare) : value.conjugate.norm = value.norm := by
  unfold norm conjugate
  ring1

/-- A pair multiplied by its original algebraic conjugate gives the scalar pair of its norm. -/
theorem product_conjugate [CommRing K] (value : Pair K radialSquare) :
    value * value.conjugate = scalar value.norm := by
  apply Pair.ext
  · change value.re * value.re - radialSquare * value.im * -value.im = value.norm
    unfold norm
    ring1
  · change value.re * -value.im + value.im * value.re = 0
    ring1

/-- Scaling both coordinates multiplies the norm by the square of the same scalar. -/
theorem norm_scale [CommRing K] (factor : K) (value : Pair K radialSquare) :
    (scale factor value).norm = factor * factor * value.norm := by
  unfold scale norm
  ring1

/-- A nonsquare negative parameter makes norm zero equivalent to both original coordinates being zero.

A nonzero second coordinate would turn a zero norm into a scalar square root
of the negative parameter. With second coordinate zero, nonzero-product laws
force the first coordinate to vanish as well. -/
theorem norm_eq_zero_iff [ExplicitField K] [DecidableEq K]
    (nonsquare : ∀ candidate : K, candidate * candidate ≠ -radialSquare)
    (value : Pair K radialSquare) : value.norm = 0 ↔ value = 0 := by
  constructor
  · intro vanishes
    by_cases imaginaryZero : value.im = 0
    · have realSquareZero : value.re * value.re = 0 := by
        calc
          value.re * value.re = value.norm := by
            unfold norm
            rewrite [imaginaryZero, mul_zero, add_zero]
            rfl
          _ = 0 := vanishes
      by_cases realZero : value.re = 0
      · exact Pair.ext realZero imaginaryZero
      · exact False.elim (ExplicitField.mul_ne_zero realZero realZero realSquareZero)
    · have squarePlusZero : (value.re / value.im) * (value.re / value.im) + radialSquare = 0 := by
        apply ExplicitField.eq_zero_of_mul_eq_zero_left (ExplicitField.mul_ne_zero imaginaryZero imaginaryZero)
        calc
          (value.im * value.im) * ((value.re / value.im) * (value.re / value.im) + radialSquare) =
              ((value.re / value.im) * value.im) * ((value.re / value.im) * value.im) +
                radialSquare * value.im * value.im := by ring1
          _ = value.norm := by
            rewrite [ExplicitField.div_mul_cancel value.re imaginaryZero]
            rfl
          _ = 0 := vanishes
      have squareEquation : (value.re / value.im) * (value.re / value.im) = -radialSquare := by
        calc
          (value.re / value.im) * (value.re / value.im) =
              ((value.re / value.im) * (value.re / value.im) + radialSquare) - radialSquare := by ring1
          _ = -radialSquare := by rewrite [squarePlusZero]; ring1
      exact False.elim (nonsquare (value.re / value.im) squareEquation)
  · intro zero
    cases zero
    change (0 : K) * 0 + radialSquare * 0 * 0 = 0
    rewrite [mul_zero, mul_zero, add_zero]
    rfl

/-- Every nonzero pair has nonzero norm when its negative square parameter is nonsquare. -/
theorem norm_ne_zero [ExplicitField K] [DecidableEq K]
    (nonsquare : ∀ candidate : K, candidate * candidate ≠ -radialSquare)
    {value : Pair K radialSquare} (nonzero : value ≠ 0) : value.norm ≠ 0 :=
  fun vanishes => nonzero ((norm_eq_zero_iff nonsquare value).mp vanishes)

/-- Compute conjugate-scaled inverse coordinates using the same original norm. -/
@[expose] def inverse [ExplicitField K] (value : Pair K radialSquare) : Pair K radialSquare :=
  scale value.norm⁻¹ value.conjugate

/-- A pair with supplied nonzero norm multiplied by its explicit inverse gives the unit pair. -/
theorem mul_inverse [ExplicitField K] (value : Pair K radialSquare) (nonzero : value.norm ≠ 0) :
    value * value.inverse = 1 := by
  apply Pair.ext
  · change value.re * (value.norm⁻¹ * value.re) -
        radialSquare * value.im * (value.norm⁻¹ * -value.im) = 1
    calc
      value.re * (value.norm⁻¹ * value.re) - radialSquare * value.im * (value.norm⁻¹ * -value.im) =
          value.norm * value.norm⁻¹ := by unfold norm; ring1
      _ = 1 := ExplicitField.mul_inv_cancel value.norm nonzero
  · change value.re * (value.norm⁻¹ * -value.im) + value.im * (value.norm⁻¹ * value.re) = 0
    ring1

/-- The same explicit inverse multiplied by its original pair gives the unit pair. -/
theorem inverse_mul [ExplicitField K] (value : Pair K radialSquare) (nonzero : value.norm ≠ 0) :
    value.inverse * value = 1 :=
  (_root_.mul_comm value.inverse value).trans (value.mul_inverse nonzero)

end Purelib.Algebra.Quadratic.Pair

end
