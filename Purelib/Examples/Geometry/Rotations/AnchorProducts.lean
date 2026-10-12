module

import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Geometry.Rotations.Cayley.Product
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

@[expose] public section

/-!
# Rational rotations, section 9: the anchor product

The partial product is stored by its displayed finite vector formula.  Its
composition law is proved directly in coordinates, rather than transferred
from an ordered or infinite field.  This keeps the construction executable
over every explicit field in its stated domain.
-/

namespace Purelib.Examples.Geometry.Rotations.AnchorProducts

open Purelib.Examples

open Purelib.Geometry.Rotations.Cayley
open Purelib.Data.Rat.Fraction (Rational)

variable {K : Type*} [ExplicitField K]
namespace ExampleFortySeven

/-- The displayed left anchor (4,1,5). -/
def left : Vector3 Fraction.Rational := ⟨4,
  1, 5⟩

/-- The displayed right anchor (-3,4,2). -/
def right : Vector3 Fraction.Rational :=
  ⟨-3, 4, 2⟩

/-- The displayed anchor product (-19,-28,12). -/
def result : Vector3 Fraction.Rational :=
  ⟨-19, -28, 12⟩

section
/-- The two displayed anchors have dot product two. -/
theorem dot_value : Vector3.dot
  left right = 2
  := by
  unfold left
    right Vector3.dot
  ring1

/-- The two displayed anchors have cross product (-18,-23,19). -/
theorem cross_value : Vector3.cross
  left right =
  ⟨-18, -23, 19⟩ := by
  apply Vector3.ext <;> decide

/-- The displayed anchor-product numerator is (19,28,-12). -/
theorem numerator_value :
  Product.anchorProductNumerator left
  right =
    ⟨19, 28, -12⟩ := by
  apply Vector3.ext <;> decide

/-- The displayed anchor-product denominator is nonzero. -/
theorem productDefined :
  Product.anchorProductDenominator left
  right ≠ 0 := by
  unfold Product.anchorProductDenominator
  rw [dot_value]
  decide

/-- The partial anchor product evaluates to the retained result (-19,-28,12). -/
theorem product_value :
  Product.anchorProduct left
  right
  productDefined =
  result := by
  rw [Product.anchorProduct_eq_inverse_scale,
    numerator_value]
  have denominatorValue : Product.anchorProductDenominator
    left right =
    -1 := by
    unfold Product.anchorProductDenominator
    rw [dot_value]
    ring1
  rw [denominatorValue]
  apply Vector3.ext <;> decide

/-- The left anchor has quadrance 42. -/
theorem left_quadrance :
  left.quadrance = 42 := by
  unfold left Vector3.quadrance Vector3.dot
  ring1

/-- The right anchor has quadrance 29. -/
theorem right_quadrance :
  right.quadrance = 29 := by
  unfold right Vector3.quadrance Vector3.dot
  ring1

/-- The result anchor has quadrance 1289. -/
theorem result_quadrance :
  result.quadrance = 1289 := by
  unfold result Vector3.quadrance Vector3.dot
  ring1

/-- The left Cayley cap denominator 43 is nonzero. -/
theorem leftDefined :
  Cap.capDenominator left ≠ 0 := by
  rw [show Cap.capDenominator left = (43 :
    Fraction.Rational) by
    unfold Cap.capDenominator
    rw [left_quadrance]
    ring1]
  exact (fun {value : Nat} (nonzero : value ≠ 0) => (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero
    (value := value) nonzero : (value : Rational) ≠ 0)) (by decide)

/-- The right Cayley cap denominator 30 is nonzero. -/
theorem rightDefined :
  Cap.capDenominator right ≠ 0 := by
  rw [show Cap.capDenominator right = (30 :
    Fraction.Rational) by
    unfold Cap.capDenominator
    rw [right_quadrance]
    ring1]
  exact (fun {value : Nat} (nonzero : value ≠ 0) => (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero
    (value := value) nonzero : (value : Rational) ≠ 0)) (by decide)

/-- The result Cayley cap denominator 1290 is nonzero. -/
theorem resultDefined :
  Cap.capDenominator result ≠ 0 := by
  rw [show Cap.capDenominator result = (1290 :
    Fraction.Rational) by
    unfold Cap.capDenominator
    rw [result_quadrance]
    ring1]
  exact (fun {value : Nat} (nonzero : value ≠ 0) => (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero
    (value := value) nonzero : (value : Rational) ≠ 0)) (by decide)

end

/-- The rational scalar two is nonzero. -/
theorem twoNonzero : (2 : Fraction.Rational)
  ≠ 0 := by decide

/-- The left cap rotation has half-spread 42/43. -/
theorem left_halfSpread :
  Rotations.Spread.halfSpread (Cap.capRotation left
  leftDefined) =
    (42 : Fraction.Rational) / 43 := by
  rw [Rotations.Spread.halfSpread_cap left
    leftDefined
    twoNonzero,
    left_quadrance]
  unfold Cap.capDenominator
  rw [left_quadrance]
  rw [show (1 + 42 : Fraction.Rational) = 43 by ring1]

/-- The right cap rotation has half-spread 29/30. -/
theorem right_halfSpread :
  Rotations.Spread.halfSpread (Cap.capRotation
  right
  rightDefined) =
    (29 : Fraction.Rational) / 30 := by
  rw [Rotations.Spread.halfSpread_cap right
    rightDefined
    twoNonzero,
    right_quadrance]
  unfold Cap.capDenominator
  rw [right_quadrance]
  rw [show (1 + 29 : Fraction.Rational) = 30 by ring1]

/-- The product cap rotation has half-spread 1289/1290. -/
theorem result_halfSpread :
  Rotations.Spread.halfSpread (Cap.capRotation
  result
  resultDefined) =
    (1289 : Fraction.Rational) / 1290 := by
  rw [Rotations.Spread.halfSpread_cap result
    resultDefined
    twoNonzero,
    result_quadrance]
  unfold Cap.capDenominator
  rw [result_quadrance]
  rw [show (1 + 1289 : Fraction.Rational) = 1290 by ring1]

/-- Example 47's composition, without multiplying the two displayed
three-by-three matrices by hand. -/
theorem composition :
    Coordinates3.Matrix3.mul (Cap.cap left
      leftDefined) (Cap.cap
      right
      rightDefined) =
      Cap.cap result resultDefined := by
  calc
    Coordinates3.Matrix3.mul (Cap.cap left
      leftDefined) (Cap.cap
      right
      rightDefined) =
        Cap.cap (Product.anchorProduct
          left
          right
          productDefined)
          (Product.capDenominator_anchorProduct_ne_zero
            left
            right
            leftDefined
            rightDefined
              productDefined) :=
      Product.cap_mul_cap left
        right
        leftDefined
        rightDefined
        productDefined
    _ = Cap.cap result resultDefined :=
      Cap.cap_congr_vector
        product_value _ _

end ExampleFortySeven
namespace ExampleFifty

/-- The first coordinate unit vector over the explicit field. -/
def axis : Vector3 K := ⟨1, 0, 0⟩

/-- The first coordinate unit vector has squared length one. -/
theorem dot_self : Vector3.dot
  (axis : Vector3 K) axis
  = 1 := by
  unfold axis Vector3.dot
  ring1

/-- The anchor product of the first coordinate axis with itself has zero denominator. -/
theorem first_product_undefined :
    Product.anchorProductDenominator (axis : Vector3 K)
      axis = 0 := by
  unfold Product.anchorProductDenominator
  rw [dot_self]
  ring1

/-- The Cayley cap denominator of the first coordinate axis is two. -/
theorem axis_capDenominator :
  Cap.capDenominator (axis : Vector3 K) = 2 := by
  unfold Cap.capDenominator axis Vector3.quadrance
    Vector3.dot
  ring1

/-- The axis and its negative have a defined anchor product when two is nonzero. -/
theorem innerDefined (twoNonzero : (2 : K) ≠ 0) :
    Product.anchorProductDenominator (axis : Vector3 K)
      (Vector3.neg axis) ≠ 0 := by
  rw [Product.anchorProductDenominator_neg_right,
    axis_capDenominator]
  exact twoNonzero

/-- The defined anchor product of the axis and its negative is the zero vector. -/
theorem inner_value (twoNonzero : (2 : K) ≠ 0) :
    Product.anchorProduct (axis : Vector3 K)
      (Vector3.neg axis)
        (innerDefined twoNonzero) = Vector3.zero := by
  exact Product.anchorProduct_neg_right_eq_zero axis
    (by rw [axis_capDenominator]; exact twoNonzero)

/-- The outer product of the axis with the retained inner product is defined when two is nonzero. -/
theorem outerDefined (twoNonzero : (2 : K) ≠ 0) :
    Product.anchorProductDenominator (axis : Vector3 K)
        (Product.anchorProduct axis (Vector3.neg
          axis)
          (innerDefined twoNonzero)) ≠ 0 := open Purelib in by
  rw [inner_value twoNonzero,
    Product.anchorProductDenominator_zero_right]
  exact Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero

/-- The explicit partiality witness following Theorem 50: the right
bracketing exists and returns the first anchor, while the left inner product
is undefined. -/
theorem right_bracketing_value (twoNonzero : (2 :
  K) ≠ 0) :
    Product.anchorProduct (axis : Vector3 K)
        (Product.anchorProduct axis (Vector3.neg
          axis)
          (innerDefined twoNonzero))
        (outerDefined twoNonzero) =
          axis := open Purelib in by
  let zeroDefined : Product.anchorProductDenominator
    (axis : Vector3 K)
      Vector3.zero ≠ 0 := by
    rw [Product.anchorProductDenominator_zero_right]
    exact Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
  calc
    Product.anchorProduct (axis : Vector3 K)
        (Product.anchorProduct axis (Vector3.neg
          axis)
          (innerDefined twoNonzero))
        (outerDefined twoNonzero) =
      Product.anchorProduct axis Vector3.zero
        zeroDefined :=
        Product.anchorProduct_congr_right
          (inner_value twoNonzero) _ _
    _ = Geometry.Rotations.AnchorProducts.ExampleFifty.axis := Product.anchorProduct_zero_right
      axis
      (Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero)

end ExampleFifty
end Purelib.Examples.Geometry.Rotations.AnchorProducts

end
