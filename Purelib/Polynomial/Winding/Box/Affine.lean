module
import Purelib.Algebra.Group.Negation
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Sign.Jump
import Purelib.Data.Rat.Sign.Variation
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Dense.Gaussian.Linear.Affine
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Translated
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.Constants.RawLinear
import Purelib.Polynomial.Dense.Rational.Linear.Translated
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Linear.Translated
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Product

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

/-!
# Winding of translated affine coordinates

The retained Gaussian linear table is read on the four oriented sides of a
rational rectangle. Direct coordinate signs compute each original finite
Cauchy index; the four indices assemble its displayed box winding.
-/

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

namespace Purelib.Polynomial.Winding.Box.Affine

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

public section

/-- The translated coordinate has doubled winding zero along the positively oriented bottom side of a positive centered
square.

The original oriented edge retains its coordinate and raw constant tables. The stated strict bounds determine their
endpoint signs and the finite signed-remainder index. -/
private theorem translated_bottom_winding
    (c : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.horizontalEdge
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) (c.im - r)
      (c.re - r) (c.re + r)).doubledWinding = 0 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Dense.Gaussian.Path.Box.Translated.translated_horizontal_real,
      Dense.Gaussian.Path.Box.Translated.translated_horizontal_imag]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Rational.Linear.Translated.affineVariable c.re)
    (Dense.Rational.Constants.RawLinear.rawConstant (c.im - r - c.im)) (c.re - r) (c.re + r) = 0
  have negativeNonzero : c.im - r - c.im ≠ 0 := by
    have equality : c.im - r - c.im = -r := by ring1
    rw [equality]
    intro negativeZero
    have positiveZero := congrArg Neg.neg negativeZero
    rewrite [_root_.neg_neg, _root_.neg_zero] at positiveZero
    exact positive.ne' positiveZero
  rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
    Dense.Rational.SignedRemainder.Linear.Translated.signedChain_rawConstant_affineVariable negativeNonzero,
    Dense.Rational.Constants.RawLinear.rawConstant_normalize negativeNonzero]
  simp only [Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Dense.Rational.Constants.RawLinear.rawConstant_eval, Dense.Rational.Linear.Translated.affineVariable_eval,
      DensePolynomial.eval_neg, DensePolynomial.eval_constant,
    Data.Rat.Sign.Variation.variation2]
  have imaginaryValue : c.im - r - c.im = -r := by ring1
  have startValue : c.re - r - c.re = -r := by ring1
  have stopValue : c.re + r - c.re = r := by ring1
  rw [imaginaryValue, startValue, stopValue]
  simp only [_root_.neg_neg]
  rw [Data.Rat.Sign.Jump.signJump_self, Data.Rat.Sign.Jump.signJump_self]
  have opposite : (-r) * r < 0 := by
    have negative := Fraction.Order.Arithmetic.neg_lt_neg_direct positive
    rewrite [_root_.neg_zero] at negative
    exact Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct negative positive
  rw [Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg opposite]
  rfl

/-- The translated coordinate has doubled winding zero along the positively oriented top side of a positive centered
square.

The original oriented edge retains its coordinate and raw constant tables. The stated strict bounds determine their
endpoint signs and the finite signed-remainder index. -/
private theorem translated_top_winding
    (c : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.horizontalEdge
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) (c.im + r)
      (c.re + r) (c.re - r)).doubledWinding = 0 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Dense.Gaussian.Path.Box.Translated.translated_horizontal_real,
      Dense.Gaussian.Path.Box.Translated.translated_horizontal_imag]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Rational.Linear.Translated.affineVariable c.re)
    (Dense.Rational.Constants.RawLinear.rawConstant (c.im + r - c.im)) (c.re + r) (c.re - r) = 0
  have nonzero : c.im + r - c.im ≠ 0 := by
    have equality : c.im + r - c.im = r := by ring1
    rw [equality]
    exact positive.ne'
  rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
    Dense.Rational.SignedRemainder.Linear.Translated.signedChain_rawConstant_affineVariable nonzero,
    Dense.Rational.Constants.RawLinear.rawConstant_normalize nonzero]
  simp only [Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Dense.Rational.Constants.RawLinear.rawConstant_eval, Dense.Rational.Linear.Translated.affineVariable_eval,
      DensePolynomial.eval_neg, DensePolynomial.eval_constant,
    Data.Rat.Sign.Variation.variation2]
  have imaginaryValue : c.im + r - c.im = r := by ring1
  have startValue : c.re + r - c.re = r := by ring1
  have stopValue : c.re - r - c.re = -r := by ring1
  rw [imaginaryValue, startValue, stopValue]
  rw [Data.Rat.Sign.Jump.signJump_self, Data.Rat.Sign.Jump.signJump_self]
  have opposite : r * (-r) < 0 := by
    have negative := Fraction.Order.Arithmetic.neg_lt_neg_direct positive
    rewrite [_root_.neg_zero] at negative
    exact Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct positive negative
  rw [Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg opposite]
  rfl

/-- The translated coordinate has doubled winding two along the positively oriented right side of a positive centered
square.

The original oriented edge retains its coordinate and raw constant tables. The stated strict bounds determine their
endpoint signs and the finite signed-remainder index. -/
private theorem translated_right_winding
    (c : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.verticalEdge
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) (c.re + r)
      (c.im - r) (c.im + r)).doubledWinding = 2 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Dense.Gaussian.Path.Box.Translated.translated_vertical_real,
      Dense.Gaussian.Path.Box.Translated.translated_vertical_imag]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Rational.Constants.RawLinear.rawConstant (c.re + r -
    c.re))
    (Dense.Rational.Linear.Translated.affineVariable c.im) (c.im - r) (c.im + r) = 2
  have nonzero : c.re + r - c.re ≠ 0 := by
    have equality : c.re + r - c.re = r := by ring1
    rw [equality]
    exact positive.ne'
  rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
    Dense.Rational.SignedRemainder.Linear.Translated.signedChain_affineVariable_rawConstant nonzero]
  simp only [Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Dense.Rational.Constants.RawLinear.rawConstant_eval, Dense.Rational.Linear.Translated.affineVariable_eval,
      Data.Rat.Sign.Variation.variation2]
  have realValue : c.re + r - c.re = r := by ring1
  have startValue : c.im - r - c.im = -r := by ring1
  have stopValue : c.im + r - c.im = r := by ring1
  rw [realValue, startValue, stopValue]
  rw [Data.Rat.Sign.Jump.signJump_self]
  have opposite : (-r) * r < 0 := by
    have negative := Fraction.Order.Arithmetic.neg_lt_neg_direct positive
    rewrite [_root_.neg_zero] at negative
    exact Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct negative positive
  rw [Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg opposite]
  rfl

/-- The translated coordinate has doubled winding two along the positively oriented left side of a positive centered
square.

The original oriented edge retains its coordinate and raw constant tables. The stated strict bounds determine their
endpoint signs and the finite signed-remainder index. -/
private theorem translated_left_winding
    (c : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.verticalEdge
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) (c.re - r)
      (c.im + r) (c.im - r)).doubledWinding = 2 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Dense.Gaussian.Path.Box.Translated.translated_vertical_real,
      Dense.Gaussian.Path.Box.Translated.translated_vertical_imag]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Rational.Constants.RawLinear.rawConstant (c.re - r -
    c.re))
    (Dense.Rational.Linear.Translated.affineVariable c.im) (c.im + r) (c.im - r) = 2
  have nonzero : c.re - r - c.re ≠ 0 := by
    have equality : c.re - r - c.re = -r := by ring1
    rw [equality]
    intro negativeZero
    have positiveZero := congrArg Neg.neg negativeZero
    rewrite [_root_.neg_neg, _root_.neg_zero] at positiveZero
    exact positive.ne' positiveZero
  rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
    Dense.Rational.SignedRemainder.Linear.Translated.signedChain_affineVariable_rawConstant nonzero]
  simp only [Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Dense.Rational.Constants.RawLinear.rawConstant_eval, Dense.Rational.Linear.Translated.affineVariable_eval,
      Data.Rat.Sign.Variation.variation2]
  have realValue : c.re - r - c.re = -r := by ring1
  have startValue : c.im + r - c.im = r := by ring1
  have stopValue : c.im - r - c.im = -r := by ring1
  rw [realValue, startValue, stopValue]
  rw [Data.Rat.Sign.Jump.signJump_self]
  have opposite : r * (-r) < 0 := by
    have negative := Fraction.Order.Arithmetic.neg_lt_neg_direct positive
    rewrite [_root_.neg_zero] at negative
    exact Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct positive negative
  rw [Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg opposite]
  rfl

/-- The translated coordinate has doubled winding zero along the positively oriented bottom box side under the stated
strict coordinate bounds.

The original oriented edge retains its coordinate and raw constant tables. The stated strict bounds determine their
endpoint signs and the finite signed-remainder index. -/
private theorem translated_bottom_winding_box
    (c : Gaussian.Basic.Canonical) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.horizontalEdge
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) box.yLower
      box.xLower box.xUpper).doubledWinding = 0 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Dense.Gaussian.Path.Box.Translated.translated_horizontal_real,
      Dense.Gaussian.Path.Box.Translated.translated_horizontal_imag]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Rational.Linear.Translated.affineVariable c.re)
    (Dense.Rational.Constants.RawLinear.rawConstant (box.yLower - c.im)) box.xLower box.xUpper = 0
  have imaginaryNonzero : box.yLower - c.im ≠ 0 :=
    (Fraction.Order.Arithmetic.sub_neg_direct below).ne
  rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
    Dense.Rational.SignedRemainder.Linear.Translated.signedChain_rawConstant_affineVariable imaginaryNonzero,
    Dense.Rational.Constants.RawLinear.rawConstant_normalize imaginaryNonzero]
  simp only [Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Dense.Rational.Constants.RawLinear.rawConstant_eval, Dense.Rational.Linear.Translated.affineVariable_eval,
      DensePolynomial.eval_neg, DensePolynomial.eval_constant,
    Data.Rat.Sign.Variation.variation2]
  have qNegative : box.yLower - c.im < 0 :=
    Fraction.Order.Arithmetic.sub_neg_direct below
  have negQPositive : 0 < -(box.yLower - c.im) := by
    have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct qNegative
    rewrite [_root_.neg_zero] at reversed
    exact reversed
  have leftNegative : box.xLower - c.re < 0 :=
    Fraction.Order.Arithmetic.sub_neg_direct left
  have rightPositive : 0 < box.xUpper - c.re :=
    Fraction.Order.Arithmetic.sub_pos_direct right
  rw [Data.Rat.Sign.Jump.signJump_eq_zero_of_mul_pos
      (Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
        qNegative leftNegative),
    Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg
      (Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct
        leftNegative negQPositive),
    Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg
      (Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct
        qNegative rightPositive),
    Data.Rat.Sign.Jump.signJump_eq_zero_of_mul_pos
      (Fraction.Order.Arithmetic.mul_pos_direct rightPositive negQPositive)]
  rfl

/-- The translated coordinate has doubled winding zero along the positively oriented top box side under the stated
strict coordinate bounds.

The original oriented edge retains its coordinate and raw constant tables. The stated strict bounds determine their
endpoint signs and the finite signed-remainder index. -/
private theorem translated_top_winding_box
    (c : Gaussian.Basic.Canonical) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (above : c.im < box.yUpper) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.horizontalEdge
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) box.yUpper
      box.xUpper box.xLower).doubledWinding = 0 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Dense.Gaussian.Path.Box.Translated.translated_horizontal_real,
      Dense.Gaussian.Path.Box.Translated.translated_horizontal_imag]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Rational.Linear.Translated.affineVariable c.re)
    (Dense.Rational.Constants.RawLinear.rawConstant (box.yUpper - c.im)) box.xUpper box.xLower = 0
  have imaginaryNonzero : box.yUpper - c.im ≠ 0 :=
    (Fraction.Order.Arithmetic.sub_pos_direct above).ne'
  rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
    Dense.Rational.SignedRemainder.Linear.Translated.signedChain_rawConstant_affineVariable imaginaryNonzero,
    Dense.Rational.Constants.RawLinear.rawConstant_normalize imaginaryNonzero]
  simp only [Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Dense.Rational.Constants.RawLinear.rawConstant_eval, Dense.Rational.Linear.Translated.affineVariable_eval,
      DensePolynomial.eval_neg, DensePolynomial.eval_constant,
    Data.Rat.Sign.Variation.variation2]
  have qPositive : 0 < box.yUpper - c.im :=
    Fraction.Order.Arithmetic.sub_pos_direct above
  have negQNegative : -(box.yUpper - c.im) < 0 := by
    have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct qPositive
    rewrite [_root_.neg_zero] at reversed
    exact reversed
  have leftNegative : box.xLower - c.re < 0 :=
    Fraction.Order.Arithmetic.sub_neg_direct left
  have rightPositive : 0 < box.xUpper - c.re :=
    Fraction.Order.Arithmetic.sub_pos_direct right
  rw [Data.Rat.Sign.Jump.signJump_eq_zero_of_mul_pos
      (Fraction.Order.Arithmetic.mul_pos_direct qPositive rightPositive),
    Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg
      (Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
        rightPositive negQNegative),
    Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg
      (Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
        qPositive leftNegative),
    Data.Rat.Sign.Jump.signJump_eq_zero_of_mul_pos
      (Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
        leftNegative negQNegative)]
  rfl

/-- The translated coordinate has doubled winding two along the positively oriented right box side under the stated
strict coordinate bounds.

The original oriented edge retains its coordinate and raw constant tables. The stated strict bounds determine their
endpoint signs and the finite signed-remainder index. -/
private theorem translated_right_winding_box
    (c : Gaussian.Basic.Canonical) {box : Box}
    (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.verticalEdge
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) box.xUpper
      box.yLower box.yUpper).doubledWinding = 2 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Dense.Gaussian.Path.Box.Translated.translated_vertical_real,
      Dense.Gaussian.Path.Box.Translated.translated_vertical_imag]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Rational.Constants.RawLinear.rawConstant (box.xUpper
    - c.re))
    (Dense.Rational.Linear.Translated.affineVariable c.im) box.yLower box.yUpper = 2
  have realNonzero : box.xUpper - c.re ≠ 0 :=
    (Fraction.Order.Arithmetic.sub_pos_direct right).ne'
  rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
    Dense.Rational.SignedRemainder.Linear.Translated.signedChain_affineVariable_rawConstant realNonzero]
  simp only [Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Dense.Rational.Constants.RawLinear.rawConstant_eval, Dense.Rational.Linear.Translated.affineVariable_eval,
      Data.Rat.Sign.Variation.variation2]
  have realPositive : 0 < box.xUpper - c.re :=
    Fraction.Order.Arithmetic.sub_pos_direct right
  have lowerNegative : box.yLower - c.im < 0 :=
    Fraction.Order.Arithmetic.sub_neg_direct below
  have upperPositive : 0 < box.yUpper - c.im :=
    Fraction.Order.Arithmetic.sub_pos_direct above
  rw [Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg
      (Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct
        lowerNegative realPositive),
    Data.Rat.Sign.Jump.signJump_eq_zero_of_mul_pos
      (Fraction.Order.Arithmetic.mul_pos_direct upperPositive realPositive)]
  rfl

/-- The translated coordinate has doubled winding two along the positively oriented left box side under the stated
strict coordinate bounds.

The original oriented edge retains its coordinate and raw constant tables. The stated strict bounds determine their
endpoint signs and the finite signed-remainder index. -/
private theorem translated_left_winding_box
    (c : Gaussian.Basic.Canonical) {box : Box}
    (left : box.xLower < c.re)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.verticalEdge
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) box.xLower
      box.yUpper box.yLower).doubledWinding = 2 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Dense.Gaussian.Path.Box.Translated.translated_vertical_real,
      Dense.Gaussian.Path.Box.Translated.translated_vertical_imag]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Rational.Constants.RawLinear.rawConstant (box.xLower
    - c.re))
    (Dense.Rational.Linear.Translated.affineVariable c.im) box.yUpper box.yLower = 2
  have realNonzero : box.xLower - c.re ≠ 0 :=
    (Fraction.Order.Arithmetic.sub_neg_direct left).ne
  rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
    Dense.Rational.SignedRemainder.Linear.Translated.signedChain_affineVariable_rawConstant realNonzero]
  simp only [Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Dense.Rational.Constants.RawLinear.rawConstant_eval, Dense.Rational.Linear.Translated.affineVariable_eval,
      Data.Rat.Sign.Variation.variation2]
  have realNegative : box.xLower - c.re < 0 :=
    Fraction.Order.Arithmetic.sub_neg_direct left
  have lowerNegative : box.yLower - c.im < 0 :=
    Fraction.Order.Arithmetic.sub_neg_direct below
  have upperPositive : 0 < box.yUpper - c.im :=
    Fraction.Order.Arithmetic.sub_pos_direct above
  rw [Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg
      (Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
        upperPositive realNegative),
    Data.Rat.Sign.Jump.signJump_eq_zero_of_mul_pos
      (Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
        lowerNegative realNegative)]
  rfl

/-- Direct finite Cauchy-index normalization for a translated coordinate on any proper rational rectangle whose strict
interior contains its center.

The same displayed rectangle and affine coefficient inputs determine the four oriented edge indices. The original finite
product and boundary certificates preserve those readings. -/
theorem quadrupledBoxWinding_translatedCoordinate
    (c : Gaussian.Basic.Canonical) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Linear.Translated.translatedCoordinate c) box = 4 :=
      by
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq,
    translated_bottom_winding_box c left right below,
    translated_right_winding_box c right below above,
    translated_top_winding_box c left right above,
    translated_left_winding_box c left below above]
  rfl

/-- The translated coordinate has raw winding four on every positive square centered at its zero.

The same displayed rectangle and affine coefficient inputs determine the four oriented edge indices. The original finite
product and boundary certificates preserve those readings. -/
theorem quadrupledBoxWinding_translatedCoordinate_centeredSquare
    (c : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Linear.Translated.translatedCoordinate c)
      (Box.Square.Centered.Affine.centeredSquare c r positive.le) = 4 := by
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
  dsimp only [Box.Square.Centered.Affine.centeredSquare]
  rw [translated_bottom_winding c positive,
    translated_right_winding c positive,
    translated_top_winding c positive,
    translated_left_winding c positive]
  ring1

/-- A nonzero slope preserves winding four on every rational rectangle whose strict interior contains the affine zero.

The same displayed rectangle and affine coefficient inputs determine the four oriented edge indices. The original finite
product and boundary certificates preserve those readings. -/
theorem quadrupledBoxWinding_affineCoordinate
    {s : Gaussian.Basic.Canonical} (slopeNonzero : s ≠ 0) (c : Gaussian.Basic.Canonical) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Linear.Affine.affineCoordinate s c) box = 4 := by
  have proper : box.Proper :=
    ⟨left.trans right, below.trans above⟩
  have product :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      (Dense.Gaussian.Constants.gaussianConstant s) (Dense.Gaussian.Linear.Translated.translatedCoordinate c) box
        proper
      (Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance slopeNonzero box)
      (Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearanceBox c left right below above)
  rw [Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant slopeNonzero,
    quadrupledBoxWinding_translatedCoordinate c left right below above]
    at product
  exact product

/-- A nonzero slope preserves the raw winding-four normalization.

The same displayed rectangle and affine coefficient inputs determine the four oriented edge indices. The original finite
product and boundary certificates preserve those readings. -/
theorem quadrupledBoxWinding_affineCoordinate_centeredSquare
    {s : Gaussian.Basic.Canonical} (slopeNonzero : s ≠ 0) (c : Gaussian.Basic.Canonical)
    {r : Fraction.Rational} (positive : 0 < r) :
    Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Linear.Affine.affineCoordinate s c)
      (Box.Square.Centered.Affine.centeredSquare c r positive.le) = 4 := by
  have product :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      (Dense.Gaussian.Constants.gaussianConstant s) (Dense.Gaussian.Linear.Translated.translatedCoordinate c)
      (Box.Square.Centered.Affine.centeredSquare c r positive.le) (Box.Square.Centered.centeredSquare_proper c positive)
      (Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance slopeNonzero _)
      (Clearance.Box.Boundary.Translated.translatedCoordinate_boundaryClearance c positive)
  rw [Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant slopeNonzero,
    quadrupledBoxWinding_translatedCoordinate_centeredSquare c positive]
    at product
  exact product

end

end Purelib.Polynomial.Winding.Box.Affine
