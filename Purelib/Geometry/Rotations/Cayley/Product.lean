module

import Purelib.Algebra.Field.Inverse
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Geometry.Rotations.Reflection
import Purelib.Geometry.Rotations.Basic
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Cayley

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

@[expose] public section

/-!
# Rational rotations, section 9: the anchor product

The partial product is stored by its displayed finite vector formula.  Its
composition law is proved directly in coordinates, rather than transferred
from an ordered or infinite field.  This keeps the construction executable
over every explicit field in its stated domain.
-/

namespace Purelib.Geometry.Rotations.Cayley.Product

variable {K : Type*} [ExplicitField K]

/-- The scalar whose nonvanishing defines the affine anchor product. -/
def anchorProductDenominator (left right : Coordinates3.Vector K) : K
  :=
  1 - Coordinates3.Vector.dot left right

/-- The numerator that remains meaningful when the affine product is undefined and its composed rotation is a half turn.
-/
def anchorProductNumerator (left right : Coordinates3.Vector K) :
  Coordinates3.Vector K :=
  Coordinates3.Vector.sub (Coordinates3.Vector.add left right) (Coordinates3.Vector.cross left right)

/-- Definition 45: the partial product of two anchor vectors. -/
def anchorProduct (left right : Coordinates3.Vector K)
    (_defined : anchorProductDenominator left right ≠ 0) : Coordinates3.Vector K :=
  Coordinates3.Vector.scale (1 / anchorProductDenominator left right)
    (anchorProductNumerator left right)

/-- The matrix-side denominator from Definition 45. -/
def anchorMatrixProductDenominator (left right : Coordinates3.Matrix3
  K) : K :=
  1 - Antisymmetric.anchorForm left right

/-- Definition 45 on displayed anchor matrices. -/
def anchorMatrixProduct (left right : Coordinates3.Matrix3 K)
    (_defined : anchorMatrixProductDenominator left right ≠ 0) : Coordinates3.Matrix3
      K :=
  Matrix3.scale (1 / anchorMatrixProductDenominator left right)
    (Matrix3.add (Matrix3.add left right)
      (Matrix3.sub (Matrix3.mul left right) (Matrix3.mul right left)))

/-- The matrix and vector anchor-product denominators agree when two is nonzero. -/
theorem anchorProductDenominator_anchor (left right :
  Coordinates3.Vector K)
    (twoNonzero : (2 : K) ≠ 0) :
    anchorMatrixProductDenominator (Antisymmetric.anchor left) (Antisymmetric.anchor right) =
      anchorProductDenominator left right := by
  unfold anchorMatrixProductDenominator anchorProductDenominator
  rw [Antisymmetric.anchorForm_anchor left right twoNonzero]

/-- The vector and matrix formulas in Definition 45 agree under the anchor bijection. -/
theorem anchor_anchorProduct (left right : Coordinates3.Vector K)
    (defined : anchorProductDenominator left right ≠ 0) :
    Antisymmetric.anchor (anchorProduct left right defined) =
      Matrix3.scale (1 / anchorProductDenominator left right)
        (Matrix3.add (Matrix3.add (Antisymmetric.anchor left) (Antisymmetric.anchor right))
          (Matrix3.sub (Matrix3.mul (Antisymmetric.anchor left) (Antisymmetric.anchor right))
            (Matrix3.mul (Antisymmetric.anchor right) (Antisymmetric.anchor left)))) := by
  ext <;> unfold anchorProduct anchorProductNumerator
    anchorProductDenominator Coordinates3.Vector.sub Coordinates3.Vector.add
      Coordinates3.Vector.scale Coordinates3.Vector.cross
    Antisymmetric.anchor Matrix3.scale Matrix3.add Matrix3.sub Matrix3.mul <;>
    simp only [ExplicitField.div_eq_mul_inv] <;> ring1

/-- The anchor map takes the vector partial product to the matrix partial product. -/
theorem anchorMatrixProduct_anchor (left right : Coordinates3.Vector K)
    (twoNonzero : (2 : K) ≠ 0)
    (defined : anchorProductDenominator left right ≠ 0) :
    anchorMatrixProduct (Antisymmetric.anchor left) (Antisymmetric.anchor right)
        (by rwa [anchorProductDenominator_anchor left right twoNonzero]) =
      Antisymmetric.anchor (anchorProduct left right defined) := by
  rw [anchor_anchorProduct]
  unfold anchorMatrixProduct
  rw [anchorProductDenominator_anchor left right twoNonzero]

/-- The quadratic norm of a scalar together with an anchor vector.

It is the scalar square plus the vector quadrance. Its value remains defined
when the affine anchor-product denominator vanishes.
-/
def homogeneousNorm (scalar : K) (vector :
  Coordinates3.Vector K) : K :=
  scalar ^ 2 + vector.quadrance

/-- The numerator of the homogeneous rotation formula, displayed in the paper's row-vector convention. -/
public def homogeneousRotationNumerator (scalar : K)
    (vector : Coordinates3.Vector K) : Coordinates3.Matrix3 K :=
  ⟨scalar ^ 2 + vector.t ^ 2 - vector.r ^ 2 - vector.s ^ 2,
    2 * (scalar * vector.s + vector.r * vector.t),
    2 * (-scalar * vector.r + vector.s * vector.t),
    2 * (-scalar * vector.s + vector.r * vector.t),
    scalar ^ 2 - vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2,
    2 * (scalar * vector.t + vector.r * vector.s),
    2 * (scalar * vector.r + vector.s * vector.t),
    2 * (-scalar * vector.t + vector.r * vector.s),
    scalar ^ 2 - vector.t ^ 2 - vector.r ^ 2 + vector.s ^ 2⟩

/-- The affine cap is its scalar-one homogeneous numerator divided by the cap denominator. -/
public theorem cap_eq_scaled_homogeneousNumerator
  (vector : Coordinates3.Vector K)
    (defined : Cap.capDenominator vector ≠ 0) :
    Cap.cap vector defined =
      Matrix3.scale (Cap.capDenominator vector)⁻¹
        (homogeneousRotationNumerator 1 vector) := by
  rw [Cap.cap_coordinate_formula]
  ext <;> unfold homogeneousRotationNumerator Matrix3.scale <;>
    simp only [ExplicitField.div_eq_mul_inv] <;> ring1

/-- The anchor-product scalar and numerator have multiplicative homogeneous norm.

For arbitrary input vectors, the squared affine denominator plus the numerator
quadrance equals the product of the two cap denominators. No nonvanishing
condition is required.
-/
theorem homogeneousNorm_anchorProductNumerator
    (left right : Coordinates3.Vector K) :
    homogeneousNorm (anchorProductDenominator left right)
        (anchorProductNumerator left right) =
      Cap.capDenominator left * Cap.capDenominator right := by
  unfold homogeneousNorm anchorProductDenominator anchorProductNumerator
    Cap.capDenominator Coordinates3.Vector.quadrance Coordinates3.Vector.dot Coordinates3.Vector.sub
      Coordinates3.Vector.add
    Coordinates3.Vector.cross
  ring1

/-- The denominator-cleared coordinate composition identity. -/
private theorem homogeneousRotationNumerator_product
    (left right : Coordinates3.Vector K) :
    Matrix3.mul (homogeneousRotationNumerator 1 left)
        (homogeneousRotationNumerator 1 right) =
      homogeneousRotationNumerator (anchorProductDenominator left right)
        (anchorProductNumerator left right) := by
  ext <;> unfold homogeneousRotationNumerator anchorProductDenominator
    anchorProductNumerator Matrix3.mul Coordinates3.Vector.sub Coordinates3.Vector.add
      Coordinates3.Vector.cross
    Coordinates3.Vector.dot <;> ring1

/-- Simultaneous homogeneous rescaling multiplies the rotation numerator by the scalar square. -/
private theorem homogeneousRotationNumerator_scale
  (factor scalar : K)
    (vector : Coordinates3.Vector K) :
    homogeneousRotationNumerator (factor * scalar)
        (Coordinates3.Vector.scale factor vector) =
      Matrix3.scale (factor ^ 2)
        (homogeneousRotationNumerator scalar vector) := by
  ext <;> unfold homogeneousRotationNumerator Matrix3.scale Coordinates3.Vector.scale <;>
    ring1

/-- The partial anchor product is its numerator scaled by the inverse denominator. -/
public theorem anchorProduct_eq_inverse_scale (left
  right : Coordinates3.Vector K)
    (defined : anchorProductDenominator left right ≠ 0) :
    anchorProduct left right defined =
      Coordinates3.Vector.scale (anchorProductDenominator left right)⁻¹
        (anchorProductNumerator left right) := by
  unfold anchorProduct
  congr 1
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- The product anchor's rotation numerator is the homogeneous product numerator scaled by the inverse denominator
square. -/
private theorem
  homogeneousRotationNumerator_anchorProduct
    (left right : Coordinates3.Vector K)
    (defined : anchorProductDenominator left right ≠ 0) :
    homogeneousRotationNumerator 1
      (anchorProduct left right defined) =
      Matrix3.scale ((anchorProductDenominator left right)⁻¹ ^ 2)
        (homogeneousRotationNumerator
          (anchorProductDenominator left right)
          (anchorProductNumerator left right)) := by
  have cancel := ExplicitField.mul_inv_cancel
    (anchorProductDenominator left right) defined
  have reverseCancel :
      (anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right = 1 := by
    calc
      (anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right =
        anchorProductDenominator left right *
          (anchorProductDenominator left right)⁻¹ := by ring1
      _ = 1 := cancel
  rw [anchorProduct_eq_inverse_scale]
  conv_lhs =>
    lhs
    rw [← reverseCancel]
  exact homogeneousRotationNumerator_scale
    (anchorProductDenominator left right)⁻¹
    (anchorProductDenominator left right)
    (anchorProductNumerator left right)

/-- Simultaneous homogeneous rescaling multiplies the norm by the scalar square. -/
private theorem homogeneousNorm_scale (factor scalar :
  K)
    (vector : Coordinates3.Vector K) :
    homogeneousNorm (factor * scalar) (Coordinates3.Vector.scale factor vector) =
      factor ^ 2 * homogeneousNorm scalar vector := by
  unfold homogeneousNorm Coordinates3.Vector.quadrance Coordinates3.Vector.dot
    Coordinates3.Vector.scale
  ring1

/-- The result denominator is cached algebraically from the two input denominators and the affine-chart denominator. -/
theorem capDenominator_anchorProduct (left right : Coordinates3.Vector
  K)
    (defined : anchorProductDenominator left right ≠ 0) :
    Cap.capDenominator (anchorProduct left right defined) =
      (anchorProductDenominator left right)⁻¹ ^ 2 *
        (Cap.capDenominator left * Cap.capDenominator right) := by
  have cancel := ExplicitField.mul_inv_cancel
    (anchorProductDenominator left right) defined
  have reverseCancel :
      (anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right = 1 := by
    calc
      (anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right =
        anchorProductDenominator left right *
          (anchorProductDenominator left right)⁻¹ := by ring1
      _ = 1 := cancel
  calc
    Cap.capDenominator (anchorProduct left right defined) =
        homogeneousNorm 1 (anchorProduct left right defined)
          := by
      unfold Cap.capDenominator homogeneousNorm
      ring1
    _ = homogeneousNorm
        ((anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right)
        (Coordinates3.Vector.scale (anchorProductDenominator left right)⁻¹
          (anchorProductNumerator left right)) := by
      rw [reverseCancel, anchorProduct_eq_inverse_scale]
    _ = (anchorProductDenominator left right)⁻¹ ^ 2 *
        homogeneousNorm (anchorProductDenominator left right)
          (anchorProductNumerator left right) :=
      homogeneousNorm_scale _ _ _
    _ = (anchorProductDenominator left right)⁻¹ ^ 2 *
        (Cap.capDenominator left * Cap.capDenominator right) := by
      rw [homogeneousNorm_anchorProductNumerator]

/-- A defined anchor product of two defined caps again has nonzero cap denominator. -/
theorem capDenominator_anchorProduct_ne_zero (left right :
  Coordinates3.Vector K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0)
    (productDefined : anchorProductDenominator left right ≠ 0) :
    Cap.capDenominator (anchorProduct left right productDefined) ≠ 0 := by
  rw [capDenominator_anchorProduct left right productDefined]
  exact ExplicitField.mul_ne_zero
    (by
      simpa only [pow_two] using ExplicitField.mul_ne_zero
        (ExplicitField.inv_ne_zero productDefined)
        (ExplicitField.inv_ne_zero productDefined))
    (ExplicitField.mul_ne_zero leftDefined rightDefined)

/-- The cap of a defined anchor product is the normalized homogeneous product numerator.

Both input caps and the affine anchor product must have nonzero denominators. -/
private theorem
  cap_anchorProduct_eq_scaled_homogeneousNumerator
    (left right : Coordinates3.Vector K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0)
    (productDefined : anchorProductDenominator left right ≠ 0) :
    Cap.cap (anchorProduct left right productDefined)
        (capDenominator_anchorProduct_ne_zero left right leftDefined
          rightDefined productDefined) =
      Matrix3.scale
        (homogeneousNorm
          (anchorProductDenominator left right)
          (anchorProductNumerator left right))⁻¹
        (homogeneousRotationNumerator
          (anchorProductDenominator left right)
          (anchorProductNumerator left right)) := by
  let result := anchorProduct left right productDefined
  let resultDefined := capDenominator_anchorProduct_ne_zero left right
    leftDefined rightDefined productDefined
  have resultCancel := ExplicitField.mul_inv_cancel
    (Cap.capDenominator result) resultDefined
  have normNonzero :
      homogeneousNorm
        (anchorProductDenominator left right)
          (anchorProductNumerator left right) ≠ 0 := by
    rw [homogeneousNorm_anchorProductNumerator]
    exact ExplicitField.mul_ne_zero leftDefined rightDefined
  have normCancel := ExplicitField.mul_inv_cancel
    (homogeneousNorm
      (anchorProductDenominator left right)
      (anchorProductNumerator left right)) normNonzero
  have coefficient :
      (Cap.capDenominator result)⁻¹ *
          (anchorProductDenominator left right)⁻¹ ^ 2 =
        (homogeneousNorm
          (anchorProductDenominator left right)
          (anchorProductNumerator left right))⁻¹ := by
    calc
      (Cap.capDenominator result)⁻¹ *
          (anchorProductDenominator left right)⁻¹ ^ 2 =
        (Cap.capDenominator result)⁻¹ *
          (anchorProductDenominator left right)⁻¹ ^ 2 *
          (homogeneousNorm
            (anchorProductDenominator left right)
            (anchorProductNumerator left right) *
            (homogeneousNorm
              (anchorProductDenominator left right)
              (anchorProductNumerator left right))⁻¹) := by
          rw [normCancel, mul_one]
      _ = ((Cap.capDenominator result)⁻¹ * Cap.capDenominator result) *
          (homogeneousNorm
            (anchorProductDenominator left right)
            (anchorProductNumerator left right))⁻¹ := by
        rw [capDenominator_anchorProduct left right productDefined,
          homogeneousNorm_anchorProductNumerator]
        ring1
      _ = (homogeneousNorm
        (anchorProductDenominator left right)
          (anchorProductNumerator left right))⁻¹ := by
        rw [show (Cap.capDenominator result)⁻¹ * Cap.capDenominator result = 1 by
          calc
            (Cap.capDenominator result)⁻¹ * Cap.capDenominator result =
                Cap.capDenominator result * (Cap.capDenominator result)⁻¹ := by ring1
            _ = 1 := resultCancel,
          one_mul]
  rw [cap_eq_scaled_homogeneousNumerator,
    homogeneousRotationNumerator_anchorProduct, Matrix3.scale_scale,
    coefficient]

/-- The product of two defined caps is the homogeneous product numerator scaled by the inverse input denominators. -/
public theorem
  cap_mul_cap_eq_scaled_homogeneousNumerator
    (left right : Coordinates3.Vector K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0) :
    Matrix3.mul (Cap.cap left leftDefined) (Cap.cap right rightDefined) =
      Matrix3.scale
        ((Cap.capDenominator left)⁻¹ * (Cap.capDenominator right)⁻¹)
        (homogeneousRotationNumerator
          (anchorProductDenominator left right)
          (anchorProductNumerator left right)) := by
  rw [cap_eq_scaled_homogeneousNumerator left leftDefined,
    cap_eq_scaled_homogeneousNumerator right rightDefined,
    Matrix3.mul_scale_left, Matrix3.mul_scale_right,
    Matrix3.scale_scale, homogeneousRotationNumerator_product]

/-- Multiplying two Cayley caps gives the cap of their partial anchor product.

Both input cap denominators and the anchor-product denominator must be nonzero; these hypotheses also certify that the
resulting anchor has a defined cap (Theorem 46). -/
theorem cap_mul_cap (left right : Coordinates3.Vector K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0)
    (productDefined : anchorProductDenominator left right ≠ 0) :
    Matrix3.mul (Cap.cap left leftDefined) (Cap.cap right rightDefined) =
      Cap.cap (anchorProduct left right productDefined)
        (capDenominator_anchorProduct_ne_zero left right leftDefined
          rightDefined productDefined) := by
  rw [cap_eq_scaled_homogeneousNumerator left leftDefined,
    cap_eq_scaled_homogeneousNumerator right rightDefined,
    Matrix3.mul_scale_left, Matrix3.mul_scale_right,
    Matrix3.scale_scale, homogeneousRotationNumerator_product,
    cap_anchorProduct_eq_scaled_homogeneousNumerator left right
      leftDefined
      rightDefined productDefined,
    homogeneousNorm_anchorProductNumerator,
    Purelib.Algebra.Field.Inverse.inverse_product leftDefined rightDefined]

/-- Executable multiplication in the stored rotation structure. -/
def rotationProduct (left right : Rotations.Basic.Rotation K) :
  Rotations.Basic.Rotation K where
  matrix := Matrix3.mul left.matrix right.matrix
  orthogonal := Matrix3.isOrthogonal_mul left.orthogonal right.orthogonal
  determinantOne := by
    rw [Matrix3.determinant_mul, left.determinantOne,
      right.determinantOne, one_mul]

/-- The trace formula valid even on the forbidden affine locus. -/
theorem trace_cap_mul_cap (left right : Coordinates3.Vector K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0) :
    Matrix3.trace (Matrix3.mul (Cap.cap left leftDefined)
        (Cap.cap right rightDefined)) =
      (3 * anchorProductDenominator left right ^ 2 -
          (anchorProductNumerator left right).quadrance) /
        (Cap.capDenominator left * Cap.capDenominator right) := by
  rw [cap_mul_cap_eq_scaled_homogeneousNumerator left right
    leftDefined
    rightDefined]
  unfold Matrix3.trace Matrix3.scale homogeneousRotationNumerator
    Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  simp only [ExplicitField.div_eq_mul_inv]
  rw [← Purelib.Algebra.Field.Inverse.inverse_product leftDefined rightDefined]
  ring1

/-- The complementary half spread of a product of two caps is the square of the affine denominator divided by the two
cap denominators. -/
theorem one_sub_halfSpread_capProduct (left right : Coordinates3.Vector
  K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    1 - Spread.halfSpread
        (rotationProduct (Cap.capRotation left leftDefined)
          (Cap.capRotation right rightDefined)) =
      anchorProductDenominator left right ^ 2 /
        (Cap.capDenominator left * Cap.capDenominator right) := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have fourCancel := ExplicitField.mul_inv_cancel (4 : K) fourNonzero
  have denominatorNonzero :=
    ExplicitField.mul_ne_zero leftDefined rightDefined
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (Cap.capDenominator left * Cap.capDenominator right) denominatorNonzero
  have normEquation :
      Cap.capDenominator left * Cap.capDenominator right =
        anchorProductDenominator left right ^ 2 +
          (anchorProductNumerator left right).quadrance := by
    symm
    exact homogeneousNorm_anchorProductNumerator left right
  unfold Spread.halfSpread rotationProduct Cap.capRotation
  rw [trace_cap_mul_cap left right leftDefined rightDefined]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 -
        (3 -
          (3 * anchorProductDenominator left right ^ 2 -
              (anchorProductNumerator left right).quadrance) *
            (Cap.capDenominator left * Cap.capDenominator right)⁻¹) *
          (4 : K)⁻¹ =
      (4 -
        (3 -
          (3 * anchorProductDenominator left right ^ 2 -
              (anchorProductNumerator left right).quadrance) *
            (Cap.capDenominator left * Cap.capDenominator right)⁻¹)) *
        (4 : K)⁻¹ := by rw [← fourCancel]; ring1
    _ = ((Cap.capDenominator left * Cap.capDenominator right) *
          (Cap.capDenominator left * Cap.capDenominator right)⁻¹ +
        (3 * anchorProductDenominator left right ^ 2 -
            (anchorProductNumerator left right).quadrance) *
          (Cap.capDenominator left * Cap.capDenominator right)⁻¹) *
        (4 : K)⁻¹ := by rw [denominatorCancel]; ring1
    _ = 4 * anchorProductDenominator left right ^ 2 *
        (Cap.capDenominator left * Cap.capDenominator right)⁻¹ *
          (4 : K)⁻¹ := by rw [normEquation]; ring1
    _ = anchorProductDenominator left right ^ 2 *
        (Cap.capDenominator left * Cap.capDenominator right)⁻¹ := by
      calc
        4 * anchorProductDenominator left right ^ 2 *
            (Cap.capDenominator left * Cap.capDenominator right)⁻¹ * (4 : K)⁻¹ =
          (4 * (4 : K)⁻¹) *
            (anchorProductDenominator left right ^ 2 *
              (Cap.capDenominator left * Cap.capDenominator right)⁻¹) := by ring1
        _ = anchorProductDenominator left right ^ 2 *
            (Cap.capDenominator left * Cap.capDenominator right)⁻¹ := by
          rw [fourCancel, one_mul]

/-- Corollary 48: the composed cap rotation is a half turn exactly on the forbidden affine locus. -/
theorem capProduct_halfSpread_eq_one [DecidableEq K]
    (left right : Coordinates3.Vector K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread
        (rotationProduct (Cap.capRotation left leftDefined)
          (Cap.capRotation right rightDefined)) = 1 ↔
      Coordinates3.Vector.dot left right = 1 := by
  have denominatorNonzero :=
    ExplicitField.mul_ne_zero leftDefined rightDefined
  constructor
  · intro Purelib.Geometry.Rotations.Reflection.halfTurn
    have complementZero :
        1 - Spread.halfSpread
          (rotationProduct (Cap.capRotation left leftDefined)
            (Cap.capRotation right rightDefined)) = 0 := by
      rw [Purelib.Geometry.Rotations.Reflection.halfTurn]
      ring1
    rw [one_sub_halfSpread_capProduct left right leftDefined rightDefined
      twoNonzero] at complementZero
    have squareZero : anchorProductDenominator left right ^ 2 = 0 := by
      calc
        anchorProductDenominator left right ^ 2 =
            (anchorProductDenominator left right ^ 2 /
              (Cap.capDenominator left * Cap.capDenominator right)) *
                (Cap.capDenominator left * Cap.capDenominator right) := by
          symm
          exact ExplicitField.div_mul_cancel _ denominatorNonzero
        _ = 0 := by rw [complementZero, zero_mul]
    by_cases denominatorZero : anchorProductDenominator left right = 0
    · have displayedZero : 1 - Coordinates3.Vector.dot left right = 0 := by
        simpa only [anchorProductDenominator] using denominatorZero
      calc
        Coordinates3.Vector.dot left right =
            1 - (1 - Coordinates3.Vector.dot left right) := by ring1
        _ = 1 := by rw [displayedZero]; ring1
    · have squareNonzero : anchorProductDenominator left right ^ 2 ≠ 0 := by
        simpa only [pow_two] using ExplicitField.mul_ne_zero
          denominatorZero denominatorZero
      exact (squareNonzero squareZero).elim
  · intro dotOne
    have denominatorZero : anchorProductDenominator left right = 0 := by
      unfold anchorProductDenominator
      rw [dotOne]
      ring1
    have complementZero :
        1 - Spread.halfSpread
          (rotationProduct (Cap.capRotation left leftDefined)
            (Cap.capRotation right rightDefined)) = 0 := by
      rw [one_sub_halfSpread_capProduct left right leftDefined rightDefined
        twoNonzero, denominatorZero]
      rw [show (0 : K) ^ 2 = 0 by ring1,
        ExplicitField.zero_div]
    calc
      Spread.halfSpread
          (rotationProduct (Cap.capRotation left leftDefined)
            (Cap.capRotation right rightDefined)) =
        1 - (1 - Spread.halfSpread
          (rotationProduct (Cap.capRotation left leftDefined)
            (Cap.capRotation right rightDefined))) := by ring1
      _ = 1 := by rw [complementZero]; ring1

/-- On the forbidden affine locus, the surviving numerator has exactly the product of the two cap denominators as its
quadrance. -/
theorem anchorProductNumerator_quadrance_of_dot_eq_one
    (left right : Coordinates3.Vector K) (dotOne : Coordinates3.Vector.dot left right = 1) :
    (anchorProductNumerator left right).quadrance =
      Cap.capDenominator left * Cap.capDenominator right := by
  have identity := homogeneousNorm_anchorProductNumerator left right
  unfold homogeneousNorm at identity
  have denominatorZero : anchorProductDenominator left right = 0 := by
    unfold anchorProductDenominator
    rw [dotOne]
    ring1
  rw [denominatorZero] at identity
  rw [show (0 : K) ^ 2 = 0 by ring1, zero_add] at identity
  exact identity

/-- On the dot-product-one locus, the surviving product numerator is non-null when both caps are defined. -/
theorem anchorProductNumerator_nonNull_of_dot_eq_one
    (left right : Coordinates3.Vector K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0)
    (dotOne : Coordinates3.Vector.dot left right = 1) :
    (anchorProductNumerator left right).quadrance ≠ 0 := by
  rw [anchorProductNumerator_quadrance_of_dot_eq_one left right dotOne]
  exact ExplicitField.mul_ne_zero leftDefined rightDefined

/-- The exact axis refinement of Corollary 48 used in Example 53. -/
theorem cap_mul_cap_eq_halfTurn_of_dot_eq_one
    (left right : Coordinates3.Vector K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0)
    (dotOne : Coordinates3.Vector.dot left right = 1) :
    Matrix3.mul (Cap.cap left leftDefined) (Cap.cap right rightDefined) =
      Reflection.halfTurn (anchorProductNumerator left right)
        (anchorProductNumerator_nonNull_of_dot_eq_one left right leftDefined
          rightDefined dotOne) := by
  let axis := anchorProductNumerator left right
  have axisQuadrance : axis.quadrance =
      Cap.capDenominator left * Cap.capDenominator right :=
    anchorProductNumerator_quadrance_of_dot_eq_one left right dotOne
  have axisNonNull : axis.quadrance ≠ 0 := by
    rw [axisQuadrance]
    exact ExplicitField.mul_ne_zero leftDefined rightDefined
  have denominatorZero : anchorProductDenominator left right = 0 := by
    unfold anchorProductDenominator
    rw [dotOne]
    ring1
  calc
    Matrix3.mul (Cap.cap left leftDefined) (Cap.cap right rightDefined) =
      Matrix3.scale
        ((Cap.capDenominator left)⁻¹ * (Cap.capDenominator right)⁻¹)
        (homogeneousRotationNumerator 0 axis) := by
      rw [cap_mul_cap_eq_scaled_homogeneousNumerator left right
        leftDefined
        rightDefined, denominatorZero]
    _ = Matrix3.scale axis.quadrance⁻¹
        (homogeneousRotationNumerator 0 axis) := by
      rw [axisQuadrance, Purelib.Algebra.Field.Inverse.inverse_product leftDefined rightDefined]
    _ = Reflection.halfTurn axis axisNonNull := by
      have axisCancel := ExplicitField.mul_inv_cancel
        axis.quadrance axisNonNull
      have axisCancelExpanded :
          (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s) *
            axis.quadrance⁻¹ = 1 := by
        simpa only [Coordinates3.Vector.quadrance, Coordinates3.Vector.dot] using axisCancel
      have inverseExpanded : axis.quadrance⁻¹ =
          (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s)⁻¹ := by
        rfl
      have expandedCancel :
          (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s) *
            (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s)⁻¹ = 1 := by
        rw [← inverseExpanded]
        exact axisCancelExpanded
      ext <;> unfold homogeneousRotationNumerator <;>
        unfold Reflection.halfTurn Reflection.reflection <;>
        unfold Matrix3.neg Matrix3.sub Matrix3.scale Matrix3.identity
          Matrix3.outer Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
        simp only [ExplicitField.div_eq_mul_inv] <;>
        (try rw [← expandedCancel]) <;> ring1

/-- The scalar denominator in Corollary 49. -/
def tangentDenominator (axis : Coordinates3.Vector K) (left right : K)
  : K :=
  1 - axis.quadrance * left * right

/-- For two multiples of one axis, the anchor-product denominator is the tangent denominator. -/
theorem anchorProductDenominator_scale_same (axis : Coordinates3.Vector
  K)
    (left right : K) :
    anchorProductDenominator (Coordinates3.Vector.scale left axis)
        (Coordinates3.Vector.scale right axis) =
      tangentDenominator axis left right := by
  unfold anchorProductDenominator tangentDenominator Coordinates3.Vector.quadrance
  rw [Coordinates3.Vector.dot_scale_left, Coordinates3.Vector.dot_scale_right]
  ring1

/-- The vector calculation underlying tangent addition. -/
theorem anchorProduct_scale_same (axis : Coordinates3.Vector K) (left
  right : K)
    (defined : tangentDenominator axis left right ≠ 0) :
    anchorProduct (Coordinates3.Vector.scale left axis) (Coordinates3.Vector.scale
      right axis)
        (by rwa [anchorProductDenominator_scale_same]) =
      Coordinates3.Vector.scale ((left + right) / tangentDenominator axis left right)
        axis := by
  have numerator :
      anchorProductNumerator (Coordinates3.Vector.scale left axis)
          (Coordinates3.Vector.scale right axis) =
        Coordinates3.Vector.scale (left + right) axis := by
    apply Coordinates3.Vector.ext <;> unfold anchorProductNumerator Coordinates3.Vector.scale
      Coordinates3.Vector.sub
      Coordinates3.Vector.add Coordinates3.Vector.cross <;> ring1
  rw [anchorProduct_eq_inverse_scale,
    anchorProductDenominator_scale_same, numerator, Coordinates3.Vector.scale_scale]
  congr 1
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- The tangent-addition result has a defined cap when both input caps and the tangent denominator are defined. -/
theorem tangentResultDefined (axis : Coordinates3.Vector K) (left right
  : K)
    (leftDefined : Cap.capDenominator (Coordinates3.Vector.scale left axis) ≠ 0)
    (rightDefined : Cap.capDenominator (Coordinates3.Vector.scale right axis) ≠ 0)
    (productDefined : tangentDenominator axis left right ≠ 0) :
    Cap.capDenominator
        (Coordinates3.Vector.scale ((left + right) /
          tangentDenominator axis left right) axis) ≠ 0 := by
  rw [← anchorProduct_scale_same axis left right productDefined]
  exact capDenominator_anchorProduct_ne_zero _ _ leftDefined rightDefined
    (by rwa [anchorProductDenominator_scale_same])

/-- Corollary 49: tangent addition on a fixed anchor line. -/
theorem tangentAddition (axis : Coordinates3.Vector K) (left right : K)
    (leftDefined : Cap.capDenominator (Coordinates3.Vector.scale left axis) ≠ 0)
    (rightDefined : Cap.capDenominator (Coordinates3.Vector.scale right axis) ≠ 0)
    (productDefined : tangentDenominator axis left right ≠ 0) :
    Matrix3.mul
        (Cap.cap (Coordinates3.Vector.scale left axis) leftDefined)
        (Cap.cap (Coordinates3.Vector.scale right axis) rightDefined) =
      Cap.cap
        (Coordinates3.Vector.scale ((left + right) /
          tangentDenominator axis left right) axis)
        (tangentResultDefined axis left right leftDefined rightDefined
          productDefined) := by
  let affineDefined : anchorProductDenominator
      (Coordinates3.Vector.scale left axis) (Coordinates3.Vector.scale right axis) ≠ 0 := by
    rwa [anchorProductDenominator_scale_same]
  calc
    Matrix3.mul
        (Cap.cap (Coordinates3.Vector.scale left axis) leftDefined)
        (Cap.cap (Coordinates3.Vector.scale right axis) rightDefined) =
      Cap.cap
        (anchorProduct (Coordinates3.Vector.scale left axis)
          (Coordinates3.Vector.scale right axis)
          affineDefined)
        (capDenominator_anchorProduct_ne_zero _ _ leftDefined rightDefined
          affineDefined) :=
      cap_mul_cap _ _ leftDefined rightDefined affineDefined
    _ = Cap.cap
        (Coordinates3.Vector.scale ((left + right) /
          tangentDenominator axis left right) axis)
        (tangentResultDefined axis left right leftDefined rightDefined
          productDefined) := by
      exact Geometry.Rotations.Cayley.Cap.cap_congr_vector
        (anchorProduct_scale_same axis left right productDefined) _ _

/-- Scalar coordinate of the denominator-cleared pair product used to prove associativity without assuming that any cap
exists. -/
def homogeneousAnchorProductScalar (leftScalar : K) (left :
  Coordinates3.Vector K)
    (rightScalar : K) (right : Coordinates3.Vector K) : K :=
  leftScalar * rightScalar - Coordinates3.Vector.dot left right

/-- Vector coordinate of the denominator-cleared pair product. -/
def homogeneousAnchorProductVector (leftScalar : K) (left :
  Coordinates3.Vector K)
    (rightScalar : K) (right : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.sub
    (Coordinates3.Vector.add (Coordinates3.Vector.scale leftScalar right)
      (Coordinates3.Vector.scale rightScalar left))
    (Coordinates3.Vector.cross left right)

/-- The scalar coordinate of the homogeneous anchor product associates. -/
private theorem
  homogeneousAnchorProduct_scalar_associative
    (firstScalar : K) (first : Coordinates3.Vector K)
    (secondScalar : K) (second : Coordinates3.Vector K)
    (thirdScalar : K) (third : Coordinates3.Vector K) :
    homogeneousAnchorProductScalar
        (homogeneousAnchorProductScalar firstScalar first secondScalar second)
        (homogeneousAnchorProductVector firstScalar first secondScalar second)
        thirdScalar third =
      homogeneousAnchorProductScalar firstScalar first
        (homogeneousAnchorProductScalar secondScalar second thirdScalar third)
        (homogeneousAnchorProductVector secondScalar second thirdScalar third) := by
  unfold homogeneousAnchorProductScalar homogeneousAnchorProductVector
    Coordinates3.Vector.dot Coordinates3.Vector.sub Coordinates3.Vector.add Coordinates3.Vector.scale
      Coordinates3.Vector.cross
  ring1

/-- The vector coordinate of the homogeneous anchor product associates. -/
private theorem
  homogeneousAnchorProduct_vector_associative
    (firstScalar : K) (first : Coordinates3.Vector K)
    (secondScalar : K) (second : Coordinates3.Vector K)
    (thirdScalar : K) (third : Coordinates3.Vector K) :
    homogeneousAnchorProductVector
        (homogeneousAnchorProductScalar firstScalar first secondScalar second)
        (homogeneousAnchorProductVector firstScalar first secondScalar second)
        thirdScalar third =
      homogeneousAnchorProductVector firstScalar first
        (homogeneousAnchorProductScalar secondScalar second thirdScalar third)
        (homogeneousAnchorProductVector secondScalar second thirdScalar third) := by
  apply Coordinates3.Vector.ext <;> unfold homogeneousAnchorProductScalar
    homogeneousAnchorProductVector Coordinates3.Vector.dot Coordinates3.Vector.sub
      Coordinates3.Vector.add
    Coordinates3.Vector.scale Coordinates3.Vector.cross <;> ring1

/-- The partial anchor product respects equality of its left vector. -/
private theorem anchorProduct_congr_left {first second
  right : Coordinates3.Vector K}
    (equal : first = second)
    (firstDefined : anchorProductDenominator first right ≠ 0)
    (secondDefined : anchorProductDenominator second right ≠ 0) :
    anchorProduct first right firstDefined =
      anchorProduct second right secondDefined := by
  subst second
  rfl

/-- The partial anchor product respects equality of its right vector. -/
public theorem anchorProduct_congr_right {left first
  second : Coordinates3.Vector K}
    (equal : first = second)
    (firstDefined : anchorProductDenominator left first ≠ 0)
    (secondDefined : anchorProductDenominator left second ≠ 0) :
    anchorProduct left first firstDefined =
      anchorProduct left second secondDefined := by
  subst second
  rfl

/-- Normalize a homogeneous left factor before forming the affine anchor product.

The homogeneous scalar and resulting affine denominator must both be nonzero. -/
private theorem anchorProduct_normalized_left (scalar :
  K)
    (vector right : Coordinates3.Vector K) (scalarNonzero : scalar ≠ 0)
    (defined : anchorProductDenominator
      (Coordinates3.Vector.scale scalar⁻¹ vector) right ≠ 0) :
    anchorProduct (Coordinates3.Vector.scale scalar⁻¹ vector) right defined =
      Coordinates3.Vector.scale
        (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹
        (homogeneousAnchorProductVector scalar vector 1 right) := by
  have cancel := ExplicitField.mul_inv_cancel scalar scalarNonzero
  have reverseCancel : scalar⁻¹ * scalar = 1 := by
    calc
      scalar⁻¹ * scalar = scalar * scalar⁻¹ := by ring1
      _ = 1 := cancel
  have denominatorRelation :
      anchorProductDenominator (Coordinates3.Vector.scale scalar⁻¹ vector) right =
        scalar⁻¹ *
          homogeneousAnchorProductScalar scalar vector 1 right := by
    unfold anchorProductDenominator homogeneousAnchorProductScalar
    rw [Coordinates3.Vector.dot_scale_left]
    calc
      1 - scalar⁻¹ * Coordinates3.Vector.dot vector right =
          scalar⁻¹ * scalar - scalar⁻¹ * Coordinates3.Vector.dot vector right := by
        rw [reverseCancel]
      _ = scalar⁻¹ *
          (scalar * 1 - Coordinates3.Vector.dot vector right) := by ring1
  have numeratorRelation :
      anchorProductNumerator (Coordinates3.Vector.scale scalar⁻¹ vector) right =
        Coordinates3.Vector.scale scalar⁻¹
          (homogeneousAnchorProductVector scalar vector 1 right) := by
    have rightRescaled : right =
        Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.scale scalar right) := by
      symm
      rw [Coordinates3.Vector.scale_scale, reverseCancel, Coordinates3.Vector.one_scale]
    unfold anchorProductNumerator
    rw [Coordinates3.Vector.cross_scale_left]
    calc
      Coordinates3.Vector.sub (Coordinates3.Vector.add (Coordinates3.Vector.scale scalar⁻¹ vector) right)
          (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.cross vector right)) =
        Coordinates3.Vector.sub
          (Coordinates3.Vector.add (Coordinates3.Vector.scale scalar⁻¹ vector)
            (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.scale scalar right)))
          (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.cross vector right)) :=
        congrArg
          (fun replacement => Coordinates3.Vector.sub
            (Coordinates3.Vector.add (Coordinates3.Vector.scale scalar⁻¹ vector) replacement)
            (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.cross vector right)))
          rightRescaled
      _ = Coordinates3.Vector.sub
          (Coordinates3.Vector.scale scalar⁻¹
            (Coordinates3.Vector.add vector (Coordinates3.Vector.scale scalar right)))
          (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.cross vector right)) := by
        rw [Coordinates3.Vector.scale_add]
      _ = Coordinates3.Vector.scale scalar⁻¹
          (Coordinates3.Vector.sub (Coordinates3.Vector.add vector (Coordinates3.Vector.scale scalar right))
            (Coordinates3.Vector.cross vector right)) := by
        rw [Coordinates3.Vector.scale_sub]
      _ = Coordinates3.Vector.scale scalar⁻¹
          (homogeneousAnchorProductVector scalar vector 1 right) := by
        congr 1
        apply Coordinates3.Vector.ext <;> unfold homogeneousAnchorProductVector
          Coordinates3.Vector.sub Coordinates3.Vector.add Coordinates3.Vector.scale <;> ring1
  have resultScalarNonzero :
      homogeneousAnchorProductScalar scalar vector 1 right ≠ 0 := by
    intro resultZero
    apply defined
    rw [denominatorRelation, resultZero, mul_zero]
  have resultCancel := ExplicitField.mul_inv_cancel
    (homogeneousAnchorProductScalar scalar vector 1 right)
    resultScalarNonzero
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (anchorProductDenominator (Coordinates3.Vector.scale scalar⁻¹ vector) right) defined
  have coefficient :
      (anchorProductDenominator (Coordinates3.Vector.scale scalar⁻¹ vector) right)⁻¹ *
          scalar⁻¹ =
        (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹ := by
    calc
      (anchorProductDenominator (Coordinates3.Vector.scale scalar⁻¹ vector) right)⁻¹ *
          scalar⁻¹ =
        (anchorProductDenominator (Coordinates3.Vector.scale scalar⁻¹ vector) right)⁻¹ *
          scalar⁻¹ *
          (homogeneousAnchorProductScalar scalar vector 1 right *
            (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹) := by
              rw [resultCancel, mul_one]
      _ = ((anchorProductDenominator
          (Coordinates3.Vector.scale scalar⁻¹ vector) right)⁻¹ *
            anchorProductDenominator (Coordinates3.Vector.scale scalar⁻¹ vector) right) *
          (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹ := by
        rw [denominatorRelation]
        ring1
      _ = (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹ := by
        rw [show
          (anchorProductDenominator
            (Coordinates3.Vector.scale scalar⁻¹ vector) right)⁻¹ *
              anchorProductDenominator (Coordinates3.Vector.scale scalar⁻¹ vector) right = 1 by
            calc
              _ = anchorProductDenominator
                  (Coordinates3.Vector.scale scalar⁻¹ vector) right *
                    (anchorProductDenominator
                      (Coordinates3.Vector.scale scalar⁻¹ vector) right)⁻¹ := by ring1
              _ = 1 := denominatorCancel,
          one_mul]
  rw [anchorProduct_eq_inverse_scale, numeratorRelation,
    Coordinates3.Vector.scale_scale, coefficient]

/-- Normalize a homogeneous right factor before forming the affine anchor product.

The homogeneous scalar and resulting affine denominator must both be nonzero. -/
private theorem anchorProduct_normalized_right (left :
  Coordinates3.Vector K)
    (scalar : K) (vector : Coordinates3.Vector K) (scalarNonzero : scalar ≠ 0)
    (defined : anchorProductDenominator left
      (Coordinates3.Vector.scale scalar⁻¹ vector) ≠ 0) :
    anchorProduct left (Coordinates3.Vector.scale scalar⁻¹ vector) defined =
      Coordinates3.Vector.scale
        (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹
        (homogeneousAnchorProductVector 1 left scalar vector) := by
  have cancel := ExplicitField.mul_inv_cancel scalar scalarNonzero
  have reverseCancel : scalar⁻¹ * scalar = 1 := by
    calc
      scalar⁻¹ * scalar = scalar * scalar⁻¹ := by ring1
      _ = 1 := cancel
  have denominatorRelation :
      anchorProductDenominator left (Coordinates3.Vector.scale scalar⁻¹ vector) =
        scalar⁻¹ *
          homogeneousAnchorProductScalar 1 left scalar vector := by
    unfold anchorProductDenominator homogeneousAnchorProductScalar
    rw [Coordinates3.Vector.dot_scale_right]
    calc
      1 - scalar⁻¹ * Coordinates3.Vector.dot left vector =
          scalar⁻¹ * scalar - scalar⁻¹ * Coordinates3.Vector.dot left vector := by
        rw [reverseCancel]
      _ = scalar⁻¹ *
          (1 * scalar - Coordinates3.Vector.dot left vector) := by ring1
  have numeratorRelation :
      anchorProductNumerator left (Coordinates3.Vector.scale scalar⁻¹ vector) =
        Coordinates3.Vector.scale scalar⁻¹
          (homogeneousAnchorProductVector 1 left scalar vector) := by
    have leftRescaled : left =
        Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.scale scalar left) := by
      symm
      rw [Coordinates3.Vector.scale_scale, reverseCancel, Coordinates3.Vector.one_scale]
    unfold anchorProductNumerator
    rw [Coordinates3.Vector.cross_scale_right]
    calc
      Coordinates3.Vector.sub (Coordinates3.Vector.add left (Coordinates3.Vector.scale scalar⁻¹ vector))
          (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.cross left vector)) =
        Coordinates3.Vector.sub
          (Coordinates3.Vector.add (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.scale scalar left))
            (Coordinates3.Vector.scale scalar⁻¹ vector))
          (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.cross left vector)) :=
        congrArg
          (fun replacement => Coordinates3.Vector.sub
            (Coordinates3.Vector.add replacement (Coordinates3.Vector.scale scalar⁻¹ vector))
            (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.cross left vector)))
          leftRescaled
      _ = Coordinates3.Vector.sub
          (Coordinates3.Vector.scale scalar⁻¹
            (Coordinates3.Vector.add (Coordinates3.Vector.scale scalar left) vector))
          (Coordinates3.Vector.scale scalar⁻¹ (Coordinates3.Vector.cross left vector)) := by
        rw [Coordinates3.Vector.scale_add]
      _ = Coordinates3.Vector.scale scalar⁻¹
          (Coordinates3.Vector.sub (Coordinates3.Vector.add (Coordinates3.Vector.scale scalar left) vector)
            (Coordinates3.Vector.cross left vector)) := by
        rw [Coordinates3.Vector.scale_sub]
      _ = Coordinates3.Vector.scale scalar⁻¹
          (homogeneousAnchorProductVector 1 left scalar vector) := by
        congr 1
        apply Coordinates3.Vector.ext <;> unfold homogeneousAnchorProductVector
          Coordinates3.Vector.sub Coordinates3.Vector.add Coordinates3.Vector.scale <;> ring1
  have resultScalarNonzero :
      homogeneousAnchorProductScalar 1 left scalar vector ≠ 0 := by
    intro resultZero
    apply defined
    rw [denominatorRelation, resultZero, mul_zero]
  have resultCancel := ExplicitField.mul_inv_cancel
    (homogeneousAnchorProductScalar 1 left scalar vector)
    resultScalarNonzero
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (anchorProductDenominator left (Coordinates3.Vector.scale scalar⁻¹ vector)) defined
  have coefficient :
      (anchorProductDenominator left (Coordinates3.Vector.scale scalar⁻¹ vector))⁻¹ *
          scalar⁻¹ =
        (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹ := by
    calc
      (anchorProductDenominator left (Coordinates3.Vector.scale scalar⁻¹ vector))⁻¹ *
          scalar⁻¹ =
        (anchorProductDenominator left (Coordinates3.Vector.scale scalar⁻¹ vector))⁻¹ *
          scalar⁻¹ *
          (homogeneousAnchorProductScalar 1 left scalar vector *
            (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹) := by
              rw [resultCancel, mul_one]
      _ = ((anchorProductDenominator left
          (Coordinates3.Vector.scale scalar⁻¹ vector))⁻¹ *
            anchorProductDenominator left (Coordinates3.Vector.scale scalar⁻¹ vector)) *
          (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹ := by
        rw [denominatorRelation]
        ring1
      _ = (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹ := by
        rw [show
          (anchorProductDenominator left
            (Coordinates3.Vector.scale scalar⁻¹ vector))⁻¹ *
              anchorProductDenominator left (Coordinates3.Vector.scale scalar⁻¹ vector) = 1 by
            calc
              _ = anchorProductDenominator left
                  (Coordinates3.Vector.scale scalar⁻¹ vector) *
                    (anchorProductDenominator left
                      (Coordinates3.Vector.scale scalar⁻¹ vector))⁻¹ := by ring1
              _ = 1 := denominatorCancel,
          one_mul]
  rw [anchorProduct_eq_inverse_scale, numeratorRelation,
    Coordinates3.Vector.scale_scale, coefficient]

/-- A left-nested defined anchor product equals its normalized homogeneous numerator. -/
private theorem nestedAnchorProduct_left_normalized
    (first second third : Coordinates3.Vector K)
    (firstDefined : anchorProductDenominator first second ≠ 0)
    (secondDefined : anchorProductDenominator
      (anchorProduct first second firstDefined) third ≠ 0) :
    anchorProduct (anchorProduct first second
      firstDefined) third
        secondDefined =
      Coordinates3.Vector.scale
        (homogeneousAnchorProductScalar
          (anchorProductDenominator first second)
          (anchorProductNumerator first second) 1 third)⁻¹
        (homogeneousAnchorProductVector
          (anchorProductDenominator first second)
          (anchorProductNumerator first second) 1 third) := by
  have innerEqual := anchorProduct_eq_inverse_scale first second
    firstDefined
  let normalizedDefined : anchorProductDenominator
      (Coordinates3.Vector.scale (anchorProductDenominator first second)⁻¹
        (anchorProductNumerator first second)) third ≠ 0 := by
    rw [← innerEqual]
    exact secondDefined
  calc
    anchorProduct (anchorProduct first second
      firstDefined) third
        secondDefined =
      anchorProduct
        (Coordinates3.Vector.scale (anchorProductDenominator first second)⁻¹
          (anchorProductNumerator first second)) third normalizedDefined :=
      anchorProduct_congr_left innerEqual _ _
    _ = _ := anchorProduct_normalized_left _ _ _ firstDefined
      normalizedDefined

/-- A right-nested defined anchor product equals its normalized homogeneous numerator. -/
private theorem nestedAnchorProduct_right_normalized
    (first second third : Coordinates3.Vector K)
    (firstDefined : anchorProductDenominator second third ≠ 0)
    (secondDefined : anchorProductDenominator first
      (anchorProduct second third firstDefined) ≠ 0) :
    anchorProduct first (anchorProduct second third
      firstDefined)
        secondDefined =
      Coordinates3.Vector.scale
        (homogeneousAnchorProductScalar 1 first
          (anchorProductDenominator second third)
          (anchorProductNumerator second third))⁻¹
        (homogeneousAnchorProductVector 1 first
          (anchorProductDenominator second third)
          (anchorProductNumerator second third)) := by
  have innerEqual := anchorProduct_eq_inverse_scale second third
    firstDefined
  let normalizedDefined : anchorProductDenominator first
      (Coordinates3.Vector.scale (anchorProductDenominator second third)⁻¹
        (anchorProductNumerator second third)) ≠ 0 := by
    rw [← innerEqual]
    exact secondDefined
  calc
    anchorProduct first (anchorProduct second third
      firstDefined)
        secondDefined =
      anchorProduct first
        (Coordinates3.Vector.scale (anchorProductDenominator second third)⁻¹
          (anchorProductNumerator second third)) normalizedDefined :=
      anchorProduct_congr_right innerEqual _ _
    _ = _ := anchorProduct_normalized_right _ _ _ firstDefined
      normalizedDefined

/-- The partial anchor product is associative wherever both nested products are defined.

The four denominator certificates cover the two intermediate products and their two outer products. No cap-chart
condition on the three inputs is required (Theorem 50). -/
theorem anchorProduct_associative (first second third :
  Coordinates3.Vector K)
    (firstSecondDefined : anchorProductDenominator first second ≠ 0)
    (leftDefined : anchorProductDenominator
      (anchorProduct first second firstSecondDefined) third ≠ 0)
    (secondThirdDefined : anchorProductDenominator second third ≠ 0)
    (rightDefined : anchorProductDenominator first
      (anchorProduct second third secondThirdDefined) ≠ 0) :
    anchorProduct (anchorProduct first second
      firstSecondDefined) third
        leftDefined =
      anchorProduct first (anchorProduct second
        third secondThirdDefined)
        rightDefined := by
  rw [nestedAnchorProduct_left_normalized first second third
      firstSecondDefined leftDefined,
    nestedAnchorProduct_right_normalized first second third
      secondThirdDefined rightDefined]
  have scalarAssociative :
      homogeneousAnchorProductScalar
          (anchorProductDenominator first second)
          (anchorProductNumerator first second) 1 third =
        homogeneousAnchorProductScalar 1 first
          (anchorProductDenominator second third)
          (anchorProductNumerator second third) := by
    unfold homogeneousAnchorProductScalar anchorProductDenominator
      anchorProductNumerator Coordinates3.Vector.dot Coordinates3.Vector.sub
        Coordinates3.Vector.add Coordinates3.Vector.cross
    ring1
  have vectorAssociative :
      homogeneousAnchorProductVector
          (anchorProductDenominator first second)
          (anchorProductNumerator first second) 1 third =
        homogeneousAnchorProductVector 1 first
          (anchorProductDenominator second third)
          (anchorProductNumerator second third) := by
    apply Coordinates3.Vector.ext <;> unfold homogeneousAnchorProductVector
      anchorProductDenominator
      anchorProductNumerator Coordinates3.Vector.dot Coordinates3.Vector.sub
        Coordinates3.Vector.add Coordinates3.Vector.scale
      Coordinates3.Vector.cross <;> ring1
  exact congrArg₂ Coordinates3.Vector.scale (congrArg Inv.inv scalarAssociative)
    vectorAssociative

/-- The denominator of an anchor and its negative is the cap denominator. -/
theorem anchorProductDenominator_neg_right (vector :
  Coordinates3.Vector K) :
    anchorProductDenominator vector (Coordinates3.Vector.neg vector) =
      Cap.capDenominator vector := by
  unfold anchorProductDenominator Cap.capDenominator Coordinates3.Vector.quadrance
  rw [Coordinates3.Vector.dot_neg_right]
  ring1

/-- An anchor multiplied by its negative gives zero whenever its cap is defined. -/
theorem anchorProduct_neg_right_eq_zero (vector : Coordinates3.Vector
  K)
    (defined : Cap.capDenominator vector ≠ 0) :
    anchorProduct vector (Coordinates3.Vector.neg vector)
        (by rwa [anchorProductDenominator_neg_right]) = Coordinates3.Vector.zero := by
  rw [anchorProduct_eq_inverse_scale]
  apply Coordinates3.Vector.ext <;> unfold anchorProductNumerator Coordinates3.Vector.neg
    Coordinates3.Vector.sub
    Coordinates3.Vector.add Coordinates3.Vector.cross Coordinates3.Vector.scale Coordinates3.Vector.zero <;> ring1

/-- The anchor-product denominator with zero on the right is one. -/
theorem anchorProductDenominator_zero_right (vector :
  Coordinates3.Vector K) :
    anchorProductDenominator vector Coordinates3.Vector.zero = 1 := by
  unfold anchorProductDenominator
  rw [Coordinates3.Vector.dot_zero_right]
  ring1

/-- Zero is a right unit for the partial anchor product when one is nonzero. -/
theorem anchorProduct_zero_right (vector : Coordinates3.Vector K)
    (oneNonzero : (1 : K) ≠ 0) :
    anchorProduct vector Coordinates3.Vector.zero
        (by rwa [anchorProductDenominator_zero_right]) = vector := by
  have oneCancel := ExplicitField.mul_inv_cancel (1 : K) oneNonzero
  rw [anchorProduct_eq_inverse_scale]
  have denominator : anchorProductDenominator vector Coordinates3.Vector.zero = 1 :=
    anchorProductDenominator_zero_right vector
  rw [denominator]
  have inverseOne : (1 : K)⁻¹ = 1 := by
    calc
      (1 : K)⁻¹ = 1 * (1 : K)⁻¹ := by rw [one_mul]
      _ = 1 := oneCancel
  rw [inverseOne, Coordinates3.Vector.one_scale]
  apply Coordinates3.Vector.ext <;> unfold anchorProductNumerator Coordinates3.Vector.zero
    Coordinates3.Vector.sub
    Coordinates3.Vector.add Coordinates3.Vector.cross <;> ring1

/-- The companion numerator of Theorem 51. -/
def oppositeAnchorProductNumerator (left right : Coordinates3.Vector K)
  : Coordinates3.Vector K :=
  Coordinates3.Vector.add (Coordinates3.Vector.add left right) (Coordinates3.Vector.cross left right)

/-- Form the opposite partial anchor product using the positive cross-product term.

Divide `left + right + left × right` by `1 - left · right`, retaining the supplied nonzero denominator certificate
(Theorem 51). -/
def oppositeAnchorProduct (left right : Coordinates3.Vector K)
    (_defined : anchorProductDenominator left right ≠ 0) : Coordinates3.Vector K :=
  Coordinates3.Vector.scale (1 / anchorProductDenominator left right)
    (oppositeAnchorProductNumerator left right)

/-- The anchor-product denominator is symmetric in the two vectors. -/
theorem anchorProductDenominator_comm (left right : Coordinates3.Vector
  K) :
    anchorProductDenominator left right =
      anchorProductDenominator right left := by
  unfold anchorProductDenominator
  rw [Coordinates3.Vector.dot_comm]

/-- Theorem 51: the companion operation is the ordinary product in reverse order. -/
theorem oppositeAnchorProduct_eq_reverse (left right :
  Coordinates3.Vector K)
    (defined : anchorProductDenominator left right ≠ 0) :
    oppositeAnchorProduct left right defined =
      anchorProduct right left
        (by rwa [← anchorProductDenominator_comm left right]) := by
  have numerator : oppositeAnchorProductNumerator left right =
      anchorProductNumerator right left := by
    apply Coordinates3.Vector.ext <;> unfold oppositeAnchorProductNumerator
      anchorProductNumerator Coordinates3.Vector.add Coordinates3.Vector.sub
        Coordinates3.Vector.cross <;> ring1
  unfold oppositeAnchorProduct
  rw [anchorProduct_eq_inverse_scale,
    ← anchorProductDenominator_comm left right, numerator]
  congr 1
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- The opposite anchor product inherits conditional associativity from the ordinary anchor product, with the three
inputs and the two bracketings reversed. -/
theorem oppositeAnchorProduct_associative (first second third :
  Coordinates3.Vector K)
    (firstSecondDefined : anchorProductDenominator first second ≠ 0)
    (secondThirdDefined : anchorProductDenominator second third ≠ 0)
    (leftDefined : anchorProductDenominator
      (oppositeAnchorProduct first second firstSecondDefined) third ≠ 0)
    (rightDefined : anchorProductDenominator first
      (oppositeAnchorProduct second third secondThirdDefined) ≠ 0) :
    oppositeAnchorProduct
        (oppositeAnchorProduct first second firstSecondDefined) third
          leftDefined =
      oppositeAnchorProduct first
        (oppositeAnchorProduct second third secondThirdDefined) rightDefined := by
  let thirdSecondDefined : anchorProductDenominator third second ≠ 0 := by
    rwa [anchorProductDenominator_comm third second]
  let secondFirstDefined : anchorProductDenominator second first ≠ 0 := by
    rwa [anchorProductDenominator_comm second first]
  have firstSecondReverse := oppositeAnchorProduct_eq_reverse first second
    firstSecondDefined
  have secondThirdReverse := oppositeAnchorProduct_eq_reverse second third
    secondThirdDefined
  let reversedLeftDefined : anchorProductDenominator third
      (anchorProduct second first secondFirstDefined) ≠ 0 := by
    rw [← firstSecondReverse, anchorProductDenominator_comm]
    exact leftDefined
  let reversedRightDefined : anchorProductDenominator
      (anchorProduct third second thirdSecondDefined) first ≠ 0 := by
    rw [← secondThirdReverse, anchorProductDenominator_comm]
    exact rightDefined
  calc
    oppositeAnchorProduct
        (oppositeAnchorProduct first second firstSecondDefined) third
          leftDefined =
      anchorProduct third
        (oppositeAnchorProduct first second firstSecondDefined)
          (by rwa [anchorProductDenominator_comm third]) :=
            oppositeAnchorProduct_eq_reverse _ _ _
    _ = anchorProduct third (anchorProduct second
      first secondFirstDefined)
        reversedLeftDefined :=
      anchorProduct_congr_right firstSecondReverse _ _
    _ = anchorProduct (anchorProduct third second
      thirdSecondDefined) first
        reversedRightDefined :=
      (anchorProduct_associative third second first thirdSecondDefined
        reversedRightDefined secondFirstDefined reversedLeftDefined).symm
    _ = anchorProduct
        (oppositeAnchorProduct second third secondThirdDefined) first
          (by rwa [secondThirdReverse]) :=
      anchorProduct_congr_left secondThirdReverse.symm _ _
    _ = oppositeAnchorProduct first
        (oppositeAnchorProduct second third secondThirdDefined) rightDefined :=
      (oppositeAnchorProduct_eq_reverse _ _ _).symm

/-- The rotation interpretation of Theorem 51. -/
theorem cap_mul_cap_opposite (left right : Coordinates3.Vector K)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0)
    (productDefined : anchorProductDenominator left right ≠ 0) :
    Matrix3.mul (Cap.cap right rightDefined) (Cap.cap left leftDefined) =
      Cap.cap (oppositeAnchorProduct left right productDefined)
        (by
          rw [show oppositeAnchorProduct left right productDefined =
              anchorProduct right left
                (by rwa [← anchorProductDenominator_comm left right]) from
            oppositeAnchorProduct_eq_reverse left right productDefined]
          exact capDenominator_anchorProduct_ne_zero right left rightDefined
            leftDefined
            (by rwa [← anchorProductDenominator_comm left right])) := by
  let reverseDefined : anchorProductDenominator right left ≠ 0 := by
    rwa [← anchorProductDenominator_comm left right]
  calc
    Matrix3.mul (Cap.cap right rightDefined) (Cap.cap left leftDefined) =
        Cap.cap (anchorProduct right left reverseDefined)
          (capDenominator_anchorProduct_ne_zero right left rightDefined
            leftDefined reverseDefined) :=
      cap_mul_cap right left rightDefined leftDefined reverseDefined
    _ = Cap.cap (oppositeAnchorProduct left right productDefined) _ :=
      Geometry.Rotations.Cayley.Cap.cap_congr_vector
        (oppositeAnchorProduct_eq_reverse left right productDefined).symm _ _

end Purelib.Geometry.Rotations.Cayley.Product

end

section
public section
namespace Purelib.Geometry.Rotations.Cayley.Product

variable {K : Type*} [ExplicitField K]

/-- The opposite anchor product respects equality of its left input. -/
public theorem
  oppositeAnchorProduct_congr_left
    {first second right : Coordinates3.Vector K} (equal : first = second)
    (firstDefined : anchorProductDenominator first right ≠ 0)
    (secondDefined : anchorProductDenominator second right ≠ 0) :
    oppositeAnchorProduct first right firstDefined =
      oppositeAnchorProduct second right secondDefined := by
  subst second
  rfl

/-- The opposite anchor product respects equality of its right input. -/
public theorem
  oppositeAnchorProduct_congr_right
    {left first second : Coordinates3.Vector K} (equal : first = second)
    (firstDefined : anchorProductDenominator left first ≠ 0)
    (secondDefined : anchorProductDenominator left second ≠ 0) :
    oppositeAnchorProduct left first firstDefined =
      oppositeAnchorProduct left second secondDefined := by
  subst second
  rfl

end Purelib.Geometry.Rotations.Cayley.Product
end

end
