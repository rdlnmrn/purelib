module

import formalisations.RationalRotations.RationalRotations
import Purelib.Tactic.Ring

/-!
# Consumer checks for the revised Euclidean publication

The matrix model and old quaternion operations are reached through the
publication facade, over an explicit field with a supplied imaginary element.
-/

namespace Test.Geometry.Rotations.EuclideanPublication

open Purelib.Algebra.Quaternion
open Purelib.Algebra
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Algebra.Field.Characteristic.Nonzero (one_ne_zero_of_nonzero)
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.Geometry.Rotations
open Purelib.Geometry.Rotations.Basic (Rotation)
open Purelib.Geometry.Rotations.Projective
open Purelib.Geometry.Rotations.Cayley
open Purelib.Examples.Geometry.Rotations
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
open Purelib.Geometry.Quadratic.Space3
open Purelib.Geometry.Quadratic
open Purelib.Examples.Geometry.Quadratic.Finite
open Purelib.Algebra.Field.ExplicitOrder.Sign
open Purelib.Polynomial
open Purelib.Polynomial.RecursiveDense.Rational
open Purelib.Algebra.Quaternion.Ray.Basic (RayProportion)
open Purelib.Polynomial.Quadratic
open Purelib.Data.Rat.Fraction.Order.Basic (lt_iff_zero_lt_sub)
open formalisations.RationalRotations.Chapters

variable {K : Type*} [ExplicitField K]

/-- The complete introductory example is public through the promised facade, including its inverse and fixed axis. -/
private theorem introductory_example :
    IntroductoryExample.proportion.toProportion.norm = 18 ∧
      Action.NonNullProportion.rotationMatrix IntroductoryExample.proportion = IntroductoryExample.displayed ∧
      IntroductoryExample.displayed.IsOrthogonal ∧ IntroductoryExample.displayed.determinant = 1 ∧
      Matrix3.rowMul IntroductoryExample.axis IntroductoryExample.displayed = IntroductoryExample.axis ∧
      Spread.halfSpread (Action.NonNullProportion.rotation IntroductoryExample.proportion) = (7 : Rational) / 9 ∧
      Action.NonNullProportion.rotationMatrix IntroductoryExample.proportion.conjugate =
        Matrix3.transpose IntroductoryExample.displayed :=
  ⟨IntroductoryExample.proportion_norm, IntroductoryExample.rotation_matrix,
    IntroductoryExample.displayed_isOrthogonal, IntroductoryExample.displayed_determinant,
    IntroductoryExample.axis_fixed, IntroductoryExample.halfSpread_value, IntroductoryExample.conjugate_matrix⟩

/-- The coordinate-axis example retains the generic block, both literal caps, their square and both half spreads. -/
private theorem coordinate_axis_example :
    Cap.cap Caps.CoordinateAxis.firstVector Caps.CoordinateAxis.firstDefined =
        ⟨1, 0, 0, 0, 3 / 5, 4 / 5, 0, -4 / 5, 3 / 5⟩ ∧
      Cap.cap Caps.CoordinateAxis.secondVector Caps.CoordinateAxis.secondDefined =
        ⟨1, 0, 0, 0, -7 / 25, 24 / 25, 0, -24 / 25, -7 / 25⟩ ∧
      Matrix3.mul (Cap.cap Caps.CoordinateAxis.firstVector Caps.CoordinateAxis.firstDefined)
        (Cap.cap Caps.CoordinateAxis.firstVector Caps.CoordinateAxis.firstDefined) =
          Cap.cap Caps.CoordinateAxis.secondVector Caps.CoordinateAxis.secondDefined ∧
      Spread.halfSpread (Cap.capRotation Caps.CoordinateAxis.firstVector Caps.CoordinateAxis.firstDefined) =
        (1 : Rational) / 5 ∧
      Spread.halfSpread (Cap.capRotation Caps.CoordinateAxis.secondVector Caps.CoordinateAxis.secondDefined) =
        (16 : Rational) / 25 :=
  ⟨Caps.CoordinateAxis.first_cap, Caps.CoordinateAxis.second_cap, Caps.CoordinateAxis.square,
    Caps.CoordinateAxis.first_halfSpread, Caps.CoordinateAxis.second_halfSpread⟩

/-- The original coordinate-axis family has the revised rational block for every admissible parameter. -/
private theorem coordinate_axis_block (parameter : K)
    (defined : Cap.capDenominator (⟨parameter, 0, 0⟩ : Vector3 K) ≠ 0) :
    Cap.cap (⟨parameter, 0, 0⟩ : Vector3 K) defined =
      ⟨1, 0, 0, 0, (1 - parameter ^ 2) / (1 + parameter ^ 2),
        2 * parameter / (1 + parameter ^ 2), 0,
        -(2 * parameter / (1 + parameter ^ 2)), (1 - parameter ^ 2) / (1 + parameter ^ 2)⟩ :=
  Caps.CoordinateAxis.cap_parameter parameter defined

/-- The revised affine breakdown example retains its exact half-turn matrix, axis and polynomial. -/
private theorem half_turn_breakdown_example (X : Rational) :
    Caps.ExampleTwentyFive.vector.dot Breakdowns.ExampleFiftyThree.fourth = 1 ∧
      Product.anchorProductNumerator Caps.ExampleTwentyFive.vector Breakdowns.ExampleFiftyThree.fourth =
        (⟨15, 21, -2⟩ : Vector3 Rational) ∧
      Breakdowns.ExampleFiftyThree.product =
        ⟨-22 / 67, 63 / 67, -6 / 67, 63 / 67, 106 / 335, -42 / 335, -6 / 67, -42 / 335, -331 / 335⟩ ∧
      Breakdowns.ExampleFiftyThree.product =
        Reflection.halfTurn Breakdowns.ExampleFiftyThree.axis Breakdowns.ExampleFiftyThree.axisNonNull ∧
      Matrix3.characteristicValue Breakdowns.ExampleFiftyThree.product X = (X - 1) * (X + 1) ^ 2 ∧
      Charts.reciprocalAnchorPath 0 Breakdowns.ExampleFiftyThree.axis
        (Charts.reciprocalAnchorPath_zeroDefined Breakdowns.ExampleFiftyThree.axis
          Breakdowns.ExampleFiftyThree.axisNonNull) = Breakdowns.ExampleFiftyThree.product :=
  ⟨Breakdowns.ExampleFiftyThree.dot_one, Breakdowns.ExampleFiftyThree.numerator_value,
    Breakdowns.ExampleFiftyThree.product_displayed, Breakdowns.ExampleFiftyThree.product_halfTurn,
    Breakdowns.ExampleFiftyThree.characteristic_polynomial X, Breakdowns.ExampleFiftyThree.path_at_zero⟩

/-- The reciprocal-anchor repair keeps its original cap at every nonzero admissible parameter. -/
private theorem half_turn_breakdown_path (parameter : Rational) (nonzero : parameter ≠ 0)
    (defined : Charts.reciprocalAnchorPathDenominator parameter Breakdowns.ExampleFiftyThree.axis ≠ 0) :
    Charts.reciprocalAnchorPathDenominator parameter Breakdowns.ExampleFiftyThree.axis = parameter ^ 2 + 670 ∧
      Charts.reciprocalAnchorPath parameter Breakdowns.ExampleFiftyThree.axis defined =
        Cap.cap (Vector3.scale parameter⁻¹ Breakdowns.ExampleFiftyThree.axis)
          (Charts.reciprocalAnchorCapDefined parameter Breakdowns.ExampleFiftyThree.axis nonzero defined) :=
  ⟨Breakdowns.ExampleFiftyThree.path_denominator parameter,
    Breakdowns.ExampleFiftyThree.path_at_nonzero parameter nonzero defined⟩

/-- Original quaternion norms and projective rescalings have the revised coordinate formula. -/
private theorem proportion_definition (value : Proportion K) (factor : K) :
    value.norm = value.scalar ^ 2 + value.vector.t ^ 2 + value.vector.r ^ 2 + value.vector.s ^ 2 ∧
      (Proportion.scale factor value).norm = factor ^ 2 * value.norm := by
  refine ⟨?_, Proportion.norm_scale factor value⟩
  unfold Proportion.norm Vector3.quadrance Vector3.dot
  ring1

/-- The revised no-null-proportions clause consumes the generic original four-square certificate. -/
private theorem ordered_proportion_nonNull {F : Type*} [RayOrderedExplicitField F]
    (value : Proportion F) (nonzero : value.IsNonzero) : value.norm ≠ 0 :=
  proportion_norm_ne_zero_of_isNonzero orderedSumFourSquaresSeparate value nonzero

/-- The original projective matrix is the revised homogeneous quadratic formula. -/
private theorem projective_rotation_definition (value : NonNullProportion K) :
    Action.NonNullProportion.rotationMatrix value = Matrix3.add Matrix3.identity
      (Matrix3.scale (2 / value.toProportion.norm)
        (Matrix3.add (Matrix3.scale value.scalar (Antisymmetric.anchor value.vector))
          (Matrix3.mul (Antisymmetric.anchor value.vector) (Antisymmetric.anchor value.vector)))) := rfl

/-- The original non-null proportion has the revised affine cap and infinite-chart half-turn readbacks. -/
private theorem projective_rotation_charts (value : NonNullProportion K) :
    (∀ scalarNonzero : value.scalar ≠ 0,
      Action.NonNullProportion.rotationMatrix value = Cap.cap (Vector3.scale value.scalar⁻¹ value.vector)
        (Charts.reciprocalAnchorCapDefined value.scalar value.vector scalarNonzero value.normNonzero)) ∧
      (∀ scalarZero : value.scalar = 0,
        Action.NonNullProportion.rotationMatrix value = Reflection.halfTurn value.vector
          (Action.NonNullProportion.vector_nonNull_of_scalar_eq_zero value scalarZero)) :=
  ⟨fun nonzero => Action.NonNullProportion.rotationMatrix_eq_cap value nonzero,
    fun zero => Action.NonNullProportion.rotationMatrix_eq_halfTurn value zero⟩

/-- Both parts of the original quaternion norm give the revised half-spread identities and conjugate transpose. -/
private theorem proportion_half_spread (value : NonNullProportion K) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Action.NonNullProportion.rotation value) = value.vector.quadrance / value.toProportion.norm ∧
      1 - Spread.halfSpread (Action.NonNullProportion.rotation value) = value.scalar ^ 2 / value.toProportion.norm ∧
      Action.NonNullProportion.rotationMatrix (NonNullProportion.conjugate value) =
        Matrix3.transpose (Action.NonNullProportion.rotationMatrix value) :=
  ⟨Action.NonNullProportion.halfSpread_rotation value twoNonzero,
    Action.NonNullProportion.one_sub_halfSpread_rotation value twoNonzero,
    Action.NonNullProportion.rotationMatrix_conjugate value⟩

/-- Every scalar coordinate of the original quaternion product has the revised sign. -/
private theorem quaternion_product_coordinates (x₁ t₁ r₁ s₁ x₂ t₂ r₂ s₂ : K) :
    Proportion.mul ⟨x₁, ⟨t₁, r₁, s₁⟩⟩ ⟨x₂, ⟨t₂, r₂, s₂⟩⟩ =
      ⟨x₁ * x₂ - t₁ * t₂ - r₁ * r₂ - s₁ * s₂,
        ⟨x₁ * t₂ + x₂ * t₁ - r₁ * s₂ + r₂ * s₁,
          x₁ * r₂ + x₂ * r₁ - s₁ * t₂ + s₂ * t₁,
          x₁ * s₂ + x₂ * s₁ - t₁ * r₂ + t₂ * r₁⟩⟩ := by
  apply Proportion.ext
  · unfold Proportion.mul Vector3.dot
    ring1
  · apply Vector3.ext <;> unfold Proportion.mul Vector3.scale Vector3.sub Vector3.add Vector3.cross <;> ring1

/-- The original quaternion algebra retains both additive laws, associativity, conjugation and multiplicative norm. -/
private theorem quaternion_algebra (first second third : Proportion K) :
    Proportion.mul first (Proportion.add second third) =
        Proportion.add (Proportion.mul first second) (Proportion.mul first third) ∧
      Proportion.mul (Proportion.add first second) third =
        Proportion.add (Proportion.mul first third) (Proportion.mul second third) ∧
      Proportion.mul (Proportion.mul first second) third = Proportion.mul first (Proportion.mul second third) ∧
      Proportion.conjugate (Proportion.mul first second) =
        Proportion.mul (Proportion.conjugate second) (Proportion.conjugate first) ∧
      (Proportion.mul first second).norm = first.norm * second.norm :=
  ⟨Proportion.mul_add first second third, Proportion.add_mul first second third,
    Proportion.mul_assoc first second third, Proportion.conjugate_mul_reverse first second,
    Proportion.norm_mul first second⟩

/-- Conjugation takes Hamilton's opposite product to the original row-action product. -/
private theorem hamilton_conjugation (left right : Proportion K) :
    Proportion.conjugate (Proportion.mul right left) =
      Proportion.mul (Proportion.conjugate left) (Proportion.conjugate right) :=
  Proportion.conjugate_mul_reverse right left

/-- The revised quaternion inverse clause returns the original computed inverse and proves its exact domain. -/
private theorem quaternion_inverse (value : Proportion K) (oneNonzero : (1 : K) ≠ 0) :
    (∃ inverse : Proportion K, Proportion.mul value inverse = Proportion.identity ∧
      Proportion.mul inverse value = Proportion.identity) ↔ value.norm ≠ 0 :=
  Proportion.exists_inverse_iff value oneNonzero

/-- Euler's displayed eight-coordinate identity is the original quaternion norm law. -/
private theorem euler_four_squares (x₁ t₁ r₁ s₁ x₂ t₂ r₂ s₂ : K) :
    (x₁ ^ 2 + t₁ ^ 2 + r₁ ^ 2 + s₁ ^ 2) * (x₂ ^ 2 + t₂ ^ 2 + r₂ ^ 2 + s₂ ^ 2) =
      (x₁ * x₂ - t₁ * t₂ - r₁ * r₂ - s₁ * s₂) ^ 2 +
        (x₁ * t₂ + x₂ * t₁ - r₁ * s₂ + r₂ * s₁) ^ 2 +
        (x₁ * r₂ + x₂ * r₁ - s₁ * t₂ + s₂ * t₁) ^ 2 +
        (x₁ * s₂ + x₂ * s₁ - t₁ * r₂ + t₂ * r₁) ^ 2 := by
  ring1

/-- The original non-null projective product has total multiplicative norm and exact associativity. -/
private theorem nonNull_product (first second third : NonNullProportion K) :
    (NonNullProportion.mul first second).toProportion.norm = first.toProportion.norm * second.toProportion.norm ∧
      NonNullProportion.mul (NonNullProportion.mul first second) third =
        NonNullProportion.mul first (NonNullProportion.mul second third) :=
  ⟨NonNullProportion.mul_norm first second, NonNullProportion.mul_assoc first second third⟩

/-- The revised sandwich uses the original non-null owner, multiplication and row-vector action. -/
private theorem quaternion_sandwich (value : NonNullProportion K) (vector : Vector3 K) :
    Proportion.scale value.toProportion.norm⁻¹
      (Proportion.mul (Proportion.mul (Proportion.conjugate value.toProportion) ⟨0, vector⟩) value.toProportion) =
        ⟨0, Matrix3.rowMul vector (Action.NonNullProportion.rotationMatrix value)⟩ :=
  Action.NonNullProportion.sandwich_formula value vector

/-- The original constructive projective rotation theorem is available through the revised facade. -/
private def projective_correspondence [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) :
    Correspondence.ProjectiveRotationTheorem K := Correspondence.projectiveRotationTheorem twoNonzero

/-- The original projective group bundle retains total multiplication, conjugate inverses and scale equivalence. -/
private def projective_group (twoNonzero : (2 : K) ≠ 0) : Correspondence.ProjectiveProportionGroupLaws K :=
  Correspondence.projectiveProportionGroupLaws twoNonzero

/-- The revised pure basis table is the original row-action quaternion multiplication table. -/
private theorem quaternion_basis :
    Proportion.mul (Proportion.i : Proportion K) Proportion.i = Proportion.ofScalar (-1) ∧
      Proportion.mul (Proportion.j : Proportion K) Proportion.j = Proportion.ofScalar (-1) ∧
      Proportion.mul (Proportion.k : Proportion K) Proportion.k = Proportion.ofScalar (-1) ∧
      Proportion.mul (Proportion.j : Proportion K) Proportion.i = Proportion.k ∧
      Proportion.mul (Proportion.k : Proportion K) Proportion.j = Proportion.i ∧
      Proportion.mul (Proportion.i : Proportion K) Proportion.k = Proportion.j ∧
      Proportion.mul (Proportion.i : Proportion K) Proportion.j = Proportion.scale (-1) Proportion.k ∧
      Proportion.mul (Proportion.j : Proportion K) Proportion.k = Proportion.scale (-1) Proportion.i ∧
      Proportion.mul (Proportion.k : Proportion K) Proportion.i = Proportion.scale (-1) Proportion.j :=
  Proportion.basis_products

/-- The affine inverse uses the exact homogeneous scalar and antisymmetric vector printed in the revised paper. -/
private theorem projective_affine_inverse (rotation : Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    (Correspondence.RotationProportion.affineHomogeneous rotation notHalfTurn twoNonzero).scalar =
        1 + Matrix3.trace rotation.matrix ∧
      Antisymmetric.anchor
        (Correspondence.RotationProportion.affineHomogeneousVector rotation notHalfTurn) =
          Matrix3.scale 2 (Antisymmetric.antisymmetricPart rotation.matrix) ∧
      Action.NonNullProportion.rotationMatrix
        (Correspondence.RotationProportion.affineHomogeneous rotation notHalfTurn twoNonzero) = rotation.matrix :=
  ⟨Correspondence.RotationProportion.affineHomogeneous_scalar rotation notHalfTurn twoNonzero,
    Correspondence.RotationProportion.anchor_affineHomogeneousVector_eq_two_antisymmetricPart
      rotation notHalfTurn twoNonzero,
    Correspondence.RotationProportion.affineHomogeneous_rotationMatrix rotation notHalfTurn twoNonzero⟩

/-- Every nonzero image of `I+R`, including each nonzero row, gives the original half-turn matrix. -/
private theorem projective_half_turn_inverse [DecidableEq K] (rotation : Rotation K)
    (halfTurnSpread : Spread.halfSpread rotation = 1) (twoNonzero : (2 : K) ≠ 0) (vector : Vector3 K)
    (nonzero : Matrix3.rowMul vector (Matrix3.add Matrix3.identity rotation.matrix) ≠ Vector3.zero) :
    Action.NonNullProportion.rotationMatrix
      (NonNullProportion.ofNonNullVector
        (Matrix3.rowMul vector (Matrix3.add Matrix3.identity rotation.matrix))
        (Correspondence.RotationProportion.halfTurn_image_nonNull
          rotation halfTurnSpread twoNonzero vector nonzero)) = rotation.matrix :=
  Correspondence.RotationProportion.halfTurn_image_rotationMatrix
    rotation halfTurnSpread twoNonzero vector nonzero

/-- Original quaternion multiplication represents the matrix product in the paper's exact row order. -/
private theorem projective_multiplication (left right : NonNullProportion K) :
    Action.NonNullProportion.rotationMatrix (NonNullProportion.mul left right) =
      Matrix3.mul (Action.NonNullProportion.rotationMatrix left) (Action.NonNullProportion.rotationMatrix right) :=
  Action.NonNullProportion.rotationMatrix_mul left right

/-- Equal original rotation matrices have precisely the original nonzero projective scale relation. -/
private theorem projective_injectivity [DecidableEq K] (left right : NonNullProportion K)
    (twoNonzero : (2 : K) ≠ 0) :
    Action.NonNullProportion.rotationMatrix left = Action.NonNullProportion.rotationMatrix right ↔
      left.Equivalent right := Correspondence.NonNullProportion.rotationMatrix_eq_iff_equivalent left right twoNonzero

/-- The original projective map has exactly the nonzero scalar quaternions as its kernel. -/
private theorem projective_scalar_kernel [DecidableEq K] (value : NonNullProportion K)
    (twoNonzero : (2 : K) ≠ 0) :
    Action.NonNullProportion.rotationMatrix value = Matrix3.identity ↔
      ∃ factor : K, factor ≠ 0 ∧ value.toProportion = Proportion.scale factor Proportion.identity :=
  Correspondence.NonNullProportion.rotationMatrix_eq_identity_iff_scalar value twoNonzero

/-- Every original nonzero ordered-field quaternion gives a retained non-null projective representative. -/
private def ordered_projective_representative {F : Type*} [RayOrderedExplicitField F]
    (value : Proportion F) (nonzero : value.IsNonzero) : NonNullProportion F :=
  NonNullProportion.ofNonzero orderedSumFourSquaresSeparate value nonzero

/-- The original partial vector product has the revised signed cross term and matrix-anchor readback. -/
private theorem anchor_product_definition (left right : Vector3 K)
    (defined : Product.anchorProductDenominator left right ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Product.anchorProduct left right defined =
      Vector3.scale (1 / (1 - left.dot right))
        (Vector3.sub (Vector3.add left right) (left.cross right)) ∧
      Product.anchorMatrixProduct (Antisymmetric.anchor left) (Antisymmetric.anchor right)
        (by rwa [Product.anchorProductDenominator_anchor left right twoNonzero]) =
          Antisymmetric.anchor (Product.anchorProduct left right defined) :=
  ⟨rfl, Product.anchorMatrixProduct_anchor left right twoNonzero defined⟩

/-- The original anchor-product norm identity holds without an affine-domain assumption. -/
private theorem anchor_product_norm (left right : Vector3 K) :
    (1 - left.dot right) ^ 2 +
      (Vector3.sub (Vector3.add left right) (left.cross right)).quadrance =
        (1 + left.quadrance) * (1 + right.quadrance) :=
  Product.homogeneousNorm_anchorProductNumerator left right

/-- The original product cap denominator has the revised quotient value and is certified nonzero. -/
private theorem anchor_product_domain (left right : Vector3 K)
    (leftDefined : Cap.capDenominator left ≠ 0) (rightDefined : Cap.capDenominator right ≠ 0)
    (defined : Product.anchorProductDenominator left right ≠ 0) :
    Cap.capDenominator (Product.anchorProduct left right defined) =
      (Product.anchorProductDenominator left right)⁻¹ ^ 2 *
        (Cap.capDenominator left * Cap.capDenominator right) ∧
      Cap.capDenominator (Product.anchorProduct left right defined) ≠ 0 :=
  ⟨Product.capDenominator_anchorProduct left right defined,
    Product.capDenominator_anchorProduct_ne_zero left right leftDefined rightDefined defined⟩

/-- Original cap multiplication is the revised row-vector anchor product on its exact domain. -/
private theorem anchor_composition (left right : Vector3 K)
    (leftDefined : Cap.capDenominator left ≠ 0) (rightDefined : Cap.capDenominator right ≠ 0)
    (defined : Product.anchorProductDenominator left right ≠ 0) :
    Matrix3.mul (Cap.cap left leftDefined) (Cap.cap right rightDefined) =
      Cap.cap (Product.anchorProduct left right defined)
        (Product.capDenominator_anchorProduct_ne_zero left right leftDefined rightDefined defined) :=
  Product.cap_mul_cap left right leftDefined rightDefined defined

/-- The revised composition example retains its input coordinates, dot, cross and product vector. -/
private theorem anchor_composition_example :
    AnchorProducts.ExampleFortySeven.left = (⟨4, 1, 5⟩ : Vector3 Rational) ∧
      AnchorProducts.ExampleFortySeven.right = ⟨-3, 4, 2⟩ ∧
      AnchorProducts.ExampleFortySeven.left.dot AnchorProducts.ExampleFortySeven.right = 2 ∧
      AnchorProducts.ExampleFortySeven.left.cross AnchorProducts.ExampleFortySeven.right = ⟨-18, -23, 19⟩ ∧
      Product.anchorProduct AnchorProducts.ExampleFortySeven.left AnchorProducts.ExampleFortySeven.right
        AnchorProducts.ExampleFortySeven.productDefined = ⟨-19, -28, 12⟩ ∧
      Spread.halfSpread (Cap.capRotation AnchorProducts.ExampleFortySeven.left
        AnchorProducts.ExampleFortySeven.leftDefined) = (42 : Rational) / 43 ∧
      Spread.halfSpread (Cap.capRotation AnchorProducts.ExampleFortySeven.right
        AnchorProducts.ExampleFortySeven.rightDefined) = (29 : Rational) / 30 ∧
      Spread.halfSpread (Cap.capRotation AnchorProducts.ExampleFortySeven.result
        AnchorProducts.ExampleFortySeven.resultDefined) = (1289 : Rational) / 1290 :=
  ⟨rfl, rfl, AnchorProducts.ExampleFortySeven.dot_value, AnchorProducts.ExampleFortySeven.cross_value,
    AnchorProducts.ExampleFortySeven.product_value, AnchorProducts.ExampleFortySeven.left_halfSpread,
    AnchorProducts.ExampleFortySeven.right_halfSpread, AnchorProducts.ExampleFortySeven.result_halfSpread⟩

/-- The original cap product is a half turn exactly at the forbidden affine locus. -/
private theorem half_turn_product_criterion [DecidableEq K] (left right : Vector3 K)
    (leftDefined : Cap.capDenominator left ≠ 0) (rightDefined : Cap.capDenominator right ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Product.rotationProduct (Cap.capRotation left leftDefined)
      (Cap.capRotation right rightDefined)) = 1 ↔ left.dot right = 1 :=
  Product.capProduct_halfSpread_eq_one left right leftDefined rightDefined twoNonzero

/-- At the forbidden affine locus, the retained numerator is the non-null half-turn axis. -/
private theorem half_turn_product_axis (left right : Vector3 K)
    (leftDefined : Cap.capDenominator left ≠ 0) (rightDefined : Cap.capDenominator right ≠ 0)
    (dotOne : left.dot right = 1) :
    Matrix3.mul (Cap.cap left leftDefined) (Cap.cap right rightDefined) =
      Reflection.halfTurn (Product.anchorProductNumerator left right)
        (Product.anchorProductNumerator_nonNull_of_dot_eq_one left right leftDefined rightDefined dotOne) :=
  Product.cap_mul_cap_eq_halfTurn_of_dot_eq_one left right leftDefined rightDefined dotOne

/-- The fixed-axis family composes with the original rational tangent-addition parameter. -/
private theorem tangent_addition (axis : Vector3 K) (left right : K)
    (leftDefined : Cap.capDenominator (Vector3.scale left axis) ≠ 0)
    (rightDefined : Cap.capDenominator (Vector3.scale right axis) ≠ 0)
    (defined : Product.tangentDenominator axis left right ≠ 0) :
    Product.tangentDenominator axis left right = 1 - axis.quadrance * left * right ∧
      Matrix3.mul (Cap.cap (Vector3.scale left axis) leftDefined)
        (Cap.cap (Vector3.scale right axis) rightDefined) =
          Cap.cap (Vector3.scale ((left + right) / Product.tangentDenominator axis left right) axis)
            (Product.tangentResultDefined axis left right leftDefined rightDefined defined) :=
  ⟨rfl, Product.tangentAddition axis left right leftDefined rightDefined defined⟩

/-- Reversing the original product gives the companion with the positive cross term. -/
private theorem opposite_anchor_product (left right : Vector3 K)
    (defined : Product.anchorProductDenominator left right ≠ 0) :
    Product.oppositeAnchorProduct left right defined =
      Vector3.scale (1 / (1 - left.dot right)) (Vector3.add (Vector3.add left right) (left.cross right)) ∧
      Product.oppositeAnchorProduct left right defined = Product.anchorProduct right left
        (by rwa [← Product.anchorProductDenominator_comm left right]) :=
  ⟨rfl, Product.oppositeAnchorProduct_eq_reverse left right defined⟩

/-- Original affine associativity retains all four intermediate nonzero-denominator certificates. -/
private theorem conditional_anchor_associativity (first second third : Vector3 K)
    (firstSecond : Product.anchorProductDenominator first second ≠ 0)
    (left : Product.anchorProductDenominator (Product.anchorProduct first second firstSecond) third ≠ 0)
    (secondThird : Product.anchorProductDenominator second third ≠ 0)
    (right : Product.anchorProductDenominator first (Product.anchorProduct second third secondThird) ≠ 0) :
    Product.anchorProduct (Product.anchorProduct first second firstSecond) third left =
      Product.anchorProduct first (Product.anchorProduct second third secondThird) right :=
  Product.anchorProduct_associative first second third firstSecond left secondThird right

/-- The revised partiality example has an undefined left bracketing and a defined right bracketing. -/
private theorem anchor_partiality (twoNonzero : (2 : K) ≠ 0) :
    Product.anchorProductDenominator (AnchorProducts.ExampleFifty.axis : Vector3 K)
      AnchorProducts.ExampleFifty.axis = 0 ∧
      Product.anchorProduct AnchorProducts.ExampleFifty.axis
        (Product.anchorProduct AnchorProducts.ExampleFifty.axis (Vector3.neg AnchorProducts.ExampleFifty.axis)
          (AnchorProducts.ExampleFifty.innerDefined twoNonzero))
        (AnchorProducts.ExampleFifty.outerDefined twoNonzero) = AnchorProducts.ExampleFifty.axis :=
  ⟨AnchorProducts.ExampleFifty.first_product_undefined,
    AnchorProducts.ExampleFifty.right_bracketing_value twoNonzero⟩

/-- Inversion preserves the original half spread and reverses both recovered anchor coordinates. -/
private theorem inverse_anchor_laws (rotation : Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Orientation.Handedness.inverseRotation rotation) = Spread.halfSpread rotation ∧
      Axis.Recovery.rotationAnchor (Orientation.Handedness.inverseRotation rotation)
        (Orientation.Handedness.inverseRotation_notHalfTurn rotation notHalfTurn) =
          Matrix3.neg (Axis.Recovery.rotationAnchor rotation notHalfTurn) ∧
      Axis.Recovery.rotationAnchorVector (Orientation.Handedness.inverseRotation rotation)
        (Orientation.Handedness.inverseRotation_notHalfTurn rotation notHalfTurn) =
          Vector3.neg (Axis.Recovery.rotationAnchorVector rotation notHalfTurn) :=
  ⟨Orientation.Handedness.halfSpread_inverseRotation rotation,
    Orientation.Handedness.rotationAnchor_inverseRotation rotation notHalfTurn,
    Orientation.Handedness.rotationAnchorVector_inverseRotation rotation notHalfTurn twoNonzero⟩

/-- The revised orientation determinant has both literal quadrance and half-spread formulas. -/
private theorem cap_orientation (axis transversal : Vector3 K) (defined : Cap.capDenominator axis ≠ 0)
    (perpendicular : transversal.Perpendicular axis) (twoNonzero : (2 : K) ≠ 0) :
    Vector3.determinant axis transversal (Matrix3.rowMul transversal (Cap.cap axis defined)) =
        (2 * axis.quadrance / Cap.capDenominator axis) * transversal.quadrance ∧
      Vector3.determinant axis transversal (Matrix3.rowMul transversal (Cap.cap axis defined)) =
        2 * Spread.halfSpread (Cap.capRotation axis defined) *
          (1 - Spread.halfSpread (Cap.capRotation axis defined)) *
            Cap.capDenominator axis * transversal.quadrance :=
  ⟨Orientation.Handedness.handednessDet_cap axis defined transversal perpendicular,
    Orientation.Handedness.handednessDet_cap_halfSpread axis defined transversal perpendicular twoNonzero⟩

/-- The retained ordered frame is positive for the cap and negative for its inverse about the same axis. -/
private theorem ordered_orientation {F : Type*} [RayOrderedExplicitField F] (law : OrderDifferenceLaw F)
    (axis transversal : Vector3 F) (defined : Cap.capDenominator axis ≠ 0)
    (axisNonzero : axis ≠ Vector3.zero) (transversalNonzero : transversal ≠ Vector3.zero)
    (perpendicular : transversal.Perpendicular axis) :
    0 < Orientation.Handedness.handednessDet axis transversal (Cap.cap axis defined) ∧
      Orientation.Handedness.handednessDet axis transversal
        (Cap.cap (Vector3.neg axis) (Cap.cap_neg_defined axis defined)) < 0 :=
  ⟨Orientation.Handedness.rightHandRule axis transversal defined axisNonzero transversalNonzero perpendicular,
    Orientation.Handedness.inverseRightHandRule law axis transversal defined
      axisNonzero transversalNonzero perpendicular⟩

/-- The revised rational orientation example retains its transversal, quadrances and both signed determinants. -/
private theorem orientation_example :
    Handedness.ExampleFortyThree.transversal = (⟨1, 3, -1⟩ : Vector3 Rational) ∧
      Caps.ExampleTwentyFive.vector.quadrance = 66 ∧
      Handedness.ExampleFortyThree.transversal.quadrance = 11 ∧
      Handedness.ExampleFortyThree.transversal.Perpendicular Caps.ExampleTwentyFive.vector ∧
      Orientation.Handedness.handednessDet Caps.ExampleTwentyFive.vector
        Handedness.ExampleFortyThree.transversal
        (Cap.cap Caps.ExampleTwentyFive.vector Caps.ExampleTwentyFive.defined) = (1452 : Rational) / 67 ∧
      Orientation.Handedness.handednessDet Caps.ExampleTwentyFive.vector
        Handedness.ExampleFortyThree.transversal
        (Cap.cap (Vector3.neg Caps.ExampleTwentyFive.vector)
          (Cap.cap_neg_defined Caps.ExampleTwentyFive.vector Caps.ExampleTwentyFive.defined)) =
            (-1452 : Rational) / 67 :=
  ⟨rfl, Caps.ExampleTwentyFive.quadrance, Handedness.ExampleFortyThree.quadrance,
    Handedness.ExampleFortyThree.perpendicular, Handedness.ExampleFortyThree.handedness_value,
    Handedness.ExampleFortyThree.inverse_handedness_value⟩

/-- The original null cap has invisible orientation for every perpendicular transversal and a distinct inverse. -/
private theorem null_orientation_example (transversal : Vector3 Field.Finite.Five.Element)
    (perpendicular : transversal.Perpendicular Caps.ExampleTwentySeven.vector) :
    Orientation.Handedness.handednessDet Caps.ExampleTwentySeven.vector transversal
        (Cap.cap Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined) = 0 ∧
      Matrix3.mul (Cap.cap Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined)
        (Cap.cap (Vector3.neg Caps.ExampleTwentySeven.vector)
          (Cap.cap_neg_defined Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined)) = Matrix3.identity ∧
      Matrix3.mul (Cap.cap (Vector3.neg Caps.ExampleTwentySeven.vector)
          (Cap.cap_neg_defined Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined))
        (Cap.cap Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined) = Matrix3.identity ∧
      Cap.cap Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined ≠
        Cap.cap (Vector3.neg Caps.ExampleTwentySeven.vector)
          (Cap.cap_neg_defined Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined) :=
  ⟨Handedness.ExampleFortyFour.handedness_invisible transversal perpendicular,
    Handedness.ExampleFortyFour.inverse_product, Handedness.ExampleFortyFour.reverse_inverse_product,
    Handedness.ExampleFortyFour.inverse_distinct⟩

/-- The original big Cayley transform and its rotation domain match the revised definition. -/
private theorem rotation_anchor_domain (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) :
    (Matrix3.determinant (Matrix3.add Matrix3.identity rotation.matrix) ≠ 0 ↔
      Spread.halfSpread rotation ≠ 1) ∧
      Axis.Recovery.rotationAnchor rotation notHalfTurn =
        Matrix3.neg (Cayley.bigCayley rotation.matrix
          (Axis.Recovery.determinant_identity_add_rotation_ne_zero rotation notHalfTurn twoNonzero)) ∧
      Axis.Recovery.rotationAnchor rotation notHalfTurn =
        Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
          (Matrix3.inverse (Matrix3.add Matrix3.identity rotation.matrix)
            (Axis.Recovery.determinant_identity_add_rotation_ne_zero rotation notHalfTurn twoNonzero)) :=
  ⟨Axis.Recovery.determinant_identity_add_rotation_ne_zero_iff rotation twoNonzero,
    Axis.Recovery.rotationAnchor_eq_neg_bigCayley rotation notHalfTurn twoNonzero,
    Axis.Recovery.rotationAnchor_eq_bigCayleyFormula rotation notHalfTurn twoNonzero⟩

/-- The computed original anchor is antisymmetric and has one exact vector readback. -/
private theorem rotation_anchor_readback (rotation : Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    (Axis.Recovery.rotationAnchor rotation notHalfTurn).IsAntisymmetric ∧
      Antisymmetric.anchor (Axis.Recovery.rotationAnchorVector rotation notHalfTurn) =
        Axis.Recovery.rotationAnchor rotation notHalfTurn ∧
      ∀ vector : Vector3 K,
        Antisymmetric.anchor vector = Axis.Recovery.rotationAnchor rotation notHalfTurn →
          vector = Axis.Recovery.rotationAnchorVector rotation notHalfTurn :=
  ⟨Axis.Recovery.rotationAnchor_isAntisymmetric rotation notHalfTurn,
    Axis.Recovery.anchor_rotationAnchorVector rotation notHalfTurn twoNonzero,
    fun vector encodes => Axis.Recovery.rotationAnchorVector_unique rotation notHalfTurn twoNonzero vector encodes⟩

/-- Cap and anchor consume the original recovered vector and its computed admissibility certificate. -/
private theorem rotation_anchor_cap_inverse (rotation : Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Cap.cap (Axis.Recovery.rotationAnchorVector rotation notHalfTurn)
      (Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero) = rotation.matrix :=
  Axis.Recovery.cap_rotationAnchor rotation notHalfTurn twoNonzero

/-- Recovery from an original cap returns both its original anchor and its vector. -/
private theorem cap_anchor_inverse (vector : Vector3 K) (defined : Cap.capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Axis.Recovery.rotationAnchor (Cap.capRotation vector defined)
      (Spread.halfSpread_cap_ne_one vector defined twoNonzero) = Antisymmetric.anchor vector ∧
      Axis.Recovery.rotationAnchorVector (Cap.capRotation vector defined)
        (Spread.halfSpread_cap_ne_one vector defined twoNonzero) = vector := by
  refine ⟨Axis.Recovery.rotationAnchor_cap vector defined twoNonzero, ?_⟩
  apply Antisymmetric.anchor_injective
  exact (Axis.Recovery.anchor_rotationAnchorVector _ _ twoNonzero).trans
    (Axis.Recovery.rotationAnchor_cap vector defined twoNonzero)

/-- The recovered original vector is fixed, has the revised half twist and encodes the scaled antisymmetric part. -/
private theorem rotation_anchor_laws (rotation : Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul (Axis.Recovery.rotationAnchorVector rotation notHalfTurn) rotation.matrix =
        Axis.Recovery.rotationAnchorVector rotation notHalfTurn ∧
      (Axis.Recovery.rotationAnchorVector rotation notHalfTurn).quadrance =
        Spread.halfSpread rotation / (1 - Spread.halfSpread rotation) ∧
      Axis.Recovery.rotationAnchor rotation notHalfTurn =
        Matrix3.scale (2 / (1 + Matrix3.trace rotation.matrix))
          (Antisymmetric.antisymmetricPart rotation.matrix) :=
  ⟨Axis.Recovery.rowMul_rotationAnchorVector rotation notHalfTurn twoNonzero,
    Axis.Recovery.quadrance_rotationAnchorVector rotation notHalfTurn twoNonzero,
    Axis.Recovery.rotationAnchor_eq_antisymmetricPart rotation notHalfTurn twoNonzero⟩

/-- The revised numerical anchor example retains every trace, antisymmetric and vector coordinate. -/
private theorem rotation_anchor_example :
    Matrix3.trace RotationAnchors.ExampleThirtySix.rotation.matrix = (-63 : Rational) / 67 ∧
      1 + Matrix3.trace RotationAnchors.ExampleThirtySix.rotation.matrix = (4 : Rational) / 67 ∧
      Antisymmetric.antisymmetricPart RotationAnchors.ExampleThirtySix.rotation.matrix =
        Matrix3.scale (1 / 67) ⟨0, 14, -2, -14, 0, 8, 2, -8, 0⟩ ∧
      Axis.Recovery.rotationAnchor RotationAnchors.ExampleThirtySix.rotation
        (Spread.halfSpread_cap_ne_one Caps.ExampleTwentyFive.vector Caps.ExampleTwentyFive.defined
          RotationAnchors.ExampleThirtySix.displayedTwoNonzero) = ⟨0, 7, -1, -7, 0, 4, 1, -4, 0⟩ ∧
      Axis.Recovery.rotationAnchorVector RotationAnchors.ExampleThirtySix.rotation
        (Spread.halfSpread_cap_ne_one Caps.ExampleTwentyFive.vector Caps.ExampleTwentyFive.defined
          RotationAnchors.ExampleThirtySix.displayedTwoNonzero) = ⟨4, 1, 7⟩ :=
  ⟨RotationAnchors.ExampleThirtySix.trace_value, RotationAnchors.ExampleThirtySix.trace_denominator,
    RotationAnchors.ExampleThirtySix.antisymmetricPart_displayed,
    RotationAnchors.ExampleThirtySix.recovered_anchor, RotationAnchors.ExampleThirtySix.recovered_vector⟩

/-- The original Euclidean cap denominator and both Cayley determinants have the revised value. -/
private theorem cap_domain (vector : Vector3 K) :
    Cap.capDenominator vector = 1 + vector.quadrance ∧
      Matrix3.determinant (Matrix3.sub Matrix3.identity (Antisymmetric.anchor vector)) =
        Cap.capDenominator vector ∧
      Matrix3.determinant (Matrix3.add Matrix3.identity (Antisymmetric.anchor vector)) =
        Cap.capDenominator vector ∧
      (Cap.capDenominator vector ≠ 0 ↔ vector.quadrance ≠ -1) := by
  refine ⟨rfl, Cap.determinant_identity_sub_anchor vector, Cap.determinant_identity_add_anchor vector, ?_⟩
  constructor
  · intro defined excluded
    apply defined
    unfold Cap.capDenominator
    rw [excluded]
    ring1
  · intro admissible denominatorZero
    apply admissible
    calc
      vector.quadrance = Cap.capDenominator vector - 1 := by unfold Cap.capDenominator; ring1
      _ = -1 := by rw [denominatorZero]; ring1

/-- Every ordered-field anchor constructs the original Euclidean cap with its supplied domain certificate. -/
private def ordered_cap {F : Type*} [RayOrderedExplicitField F] (vector : Vector3 F) : Rotation F :=
  Cap.capRotation vector (FieldRealizations.OrderedFieldClaims.capDenominatorNonzero vector)

/-- The revised Cayley product consumes the original certified quadratic resolvent inverse. -/
private theorem cap_cayley (vector : Vector3 K) (defined : Cap.capDenominator vector ≠ 0) :
    Cap.cap vector defined = Matrix3.mul (Matrix3.add Matrix3.identity (Antisymmetric.anchor vector))
      (Cap.anchorResolventInverse vector defined) := Cap.cap_eq_cayley vector defined

/-- Both inverse certificates and the literal quadratic resolvent formula are available through the facade. -/
private theorem cap_resolvent (vector : Vector3 K) (defined : Cap.capDenominator vector ≠ 0) :
    Cap.anchorResolventInverse vector defined = Matrix3.add Matrix3.identity
        (Matrix3.scale (1 / Cap.capDenominator vector)
          (Matrix3.add (Antisymmetric.anchor vector)
            (Matrix3.mul (Antisymmetric.anchor vector) (Antisymmetric.anchor vector)))) ∧
      Matrix3.mul (Matrix3.sub Matrix3.identity (Antisymmetric.anchor vector))
        (Cap.anchorResolventInverse vector defined) = Matrix3.identity ∧
      Matrix3.mul (Cap.anchorResolventInverse vector defined)
        (Matrix3.sub Matrix3.identity (Antisymmetric.anchor vector)) = Matrix3.identity :=
  ⟨rfl, Cap.anchorResolventInverse_left vector defined, Cap.anchorResolventInverse_right vector defined⟩

/-- The revised quadratic cap formula is the original executable cap value. -/
private theorem cap_quadratic (vector : Vector3 K) (defined : Cap.capDenominator vector ≠ 0) :
    Cap.cap vector defined = Matrix3.add Matrix3.identity
      (Matrix3.scale (2 / Cap.capDenominator vector)
        (Matrix3.add (Antisymmetric.anchor vector)
          (Matrix3.mul (Antisymmetric.anchor vector) (Antisymmetric.anchor vector)))) :=
  Cap.cap_quadratic vector defined

/-- Every entry of the revised cap matrix has the original numerator and denominator. -/
private theorem cap_coordinates (v : Vector3 K) (defined : Cap.capDenominator v ≠ 0) :
    Cap.cap v defined = Matrix3.scale (1 / Cap.capDenominator v)
      ⟨v.t ^ 2 - v.r ^ 2 - v.s ^ 2 + 1, 2 * (v.s + v.r * v.t), 2 * (-v.r + v.s * v.t),
        2 * (-v.s + v.r * v.t), -v.t ^ 2 + v.r ^ 2 - v.s ^ 2 + 1, 2 * (v.t + v.r * v.s),
        2 * (v.r + v.s * v.t), 2 * (-v.t + v.r * v.s), -v.t ^ 2 - v.r ^ 2 + v.s ^ 2 + 1⟩ :=
  Cap.cap_coordinate_formula v defined

/-- Original cap rotation, fixed axis, trace and characteristic polynomial agree with the revised formulas. -/
private theorem cap_rotation_laws (vector : Vector3 K) (defined : Cap.capDenominator vector ≠ 0) (X : K) :
    (Cap.cap vector defined).IsOrthogonal ∧ Matrix3.determinant (Cap.cap vector defined) = 1 ∧
      Matrix3.rowMul vector (Cap.cap vector defined) = vector ∧
      Matrix3.trace (Cap.cap vector defined) = (3 - vector.quadrance) / Cap.capDenominator vector ∧
      Matrix3.characteristicValue (Cap.cap vector defined) X =
        (X - 1) * (X ^ 2 - (2 * (1 - vector.quadrance) / Cap.capDenominator vector) * X + 1) :=
  ⟨Cap.cap_isOrthogonal vector defined, Cap.determinant_cap vector defined,
    Cap.rowMul_self_cap vector defined, Cap.trace_cap vector defined, Cap.characteristicValue_cap vector defined X⟩

/-- The revised minus-one eigenvalue exclusion holds for every original cap vector. -/
private theorem cap_negative_eigenvector (vector eigenvector : Vector3 K)
    (defined : Cap.capDenominator vector ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (negativeEigen : Matrix3.rowMul eigenvector (Cap.cap vector defined) = Vector3.neg eigenvector) :
    eigenvector = Vector3.zero := Cap.rowMul_cap_eq_neg_implies_zero vector defined twoNonzero eigenvector negativeEigen

/-- Equal original caps recover the same original anchor vector. -/
private theorem cap_injective (first second : Vector3 K)
    (firstDefined : Cap.capDenominator first ≠ 0) (secondDefined : Cap.capDenominator second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (equal : Cap.cap first firstDefined = Cap.cap second secondDefined) :
    first = second := Cap.cap_injective twoNonzero first second firstDefined secondDefined equal

/-- The revised rational cap example retains `(4,1,7)`, quadrance sixty-six, its displayed matrix and fixed vector. -/
private theorem cap_rational_example :
    Caps.ExampleTwentyFive.vector = (⟨4, 1, 7⟩ : Vector3 Rational) ∧
      Caps.ExampleTwentyFive.vector.quadrance = 66 ∧
      Cap.cap Caps.ExampleTwentyFive.vector Caps.ExampleTwentyFive.defined =
        Matrix3.scale (1 / 67) (⟨-33, 22, 54, -6, -63, 22, 58, 6, 33⟩ : Matrix3 Rational) ∧
      Matrix3.rowMul Caps.ExampleTwentyFive.vector Caps.ExampleTwentyFive.displayed = Caps.ExampleTwentyFive.vector :=
  ⟨rfl, Caps.ExampleTwentyFive.quadrance, Caps.ExampleTwentyFive.cap_displayed, Caps.ExampleTwentyFive.vector_fixed⟩

/-- The rational example has the literal characteristic polynomial printed in the revision.

The proof specializes the retained quadrance, then transports the denominator
and quadratic coefficient by scalar field equalities.
-/
private theorem cap_rational_characteristic (X : Rational) :
    Matrix3.characteristicValue (Cap.cap Caps.ExampleTwentyFive.vector Caps.ExampleTwentyFive.defined) X =
      (X - 1) * (X ^ 2 + (130 / 67 : Rational) * X + 1) := by
  have denominator : Cap.capDenominator Caps.ExampleTwentyFive.vector = (67 : Rational) := by
    unfold Cap.capDenominator
    rw [Caps.ExampleTwentyFive.quadrance]
    ring1
  rw [Cap.characteristicValue_cap, Caps.ExampleTwentyFive.quadrance, denominator]
  simp only [ExplicitField.div_eq_mul_inv, -eq_self, -iff_self]
  ring1

/-- The revised F5 excluded anchor has quadrance minus one, zero denominator and singular `I-A`. -/
private theorem cap_excluded_example :
    Caps.ExampleTwentySix.vector = ⟨2, 0, 0⟩ ∧ Caps.ExampleTwentySix.vector.quadrance = -1 ∧
      Cap.capDenominator Caps.ExampleTwentySix.vector = 0 ∧
      Matrix3.determinant (Matrix3.sub Matrix3.identity (Antisymmetric.anchor Caps.ExampleTwentySix.vector)) = 0 :=
  ⟨rfl, Caps.ExampleTwentySix.quadrance, Caps.ExampleTwentySix.denominator_zero,
    Caps.ExampleTwentySix.identity_sub_anchor_singular⟩

/-- Every original null-anchor cap has the revised quadratic formula and unipotent characteristic polynomial. -/
private theorem null_cap_laws (vector : Vector3 K) (defined : Cap.capDenominator vector ≠ 0)
    (null : vector.quadrance = 0) (X : K) :
    Cap.cap vector defined = Matrix3.add Matrix3.identity (Matrix3.scale 2
        (Matrix3.add (Antisymmetric.anchor vector)
          (Matrix3.mul (Antisymmetric.anchor vector) (Antisymmetric.anchor vector)))) ∧
      Matrix3.characteristicValue (Cap.cap vector defined) X = (X - 1) ^ 3 :=
  ⟨FieldRealizations.cap_of_null vector defined null,
    FieldRealizations.characteristicValue_cap_of_null vector defined null X⟩

/-- The revised F5 null cap is the displayed nonidentity rotation with its original fixed vector and polynomial. -/
private theorem null_cap_example (X : Field.Finite.Five.Element) :
    Caps.ExampleTwentySeven.vector = ⟨1, 2, 0⟩ ∧ Caps.ExampleTwentySeven.vector.quadrance = 0 ∧
      Cap.cap Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined =
        ⟨3, 4, 1, 4, 4, 2, 4, 3, 1⟩ ∧
      Caps.ExampleTwentySeven.displayed.IsOrthogonal ∧
      Matrix3.determinant Caps.ExampleTwentySeven.displayed = 1 ∧
      Matrix3.rowMul Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.displayed =
        Caps.ExampleTwentySeven.vector ∧
      Caps.ExampleTwentySeven.displayed ≠ Matrix3.identity ∧
      Matrix3.characteristicValue Caps.ExampleTwentySeven.displayed X = (X - 1) ^ 3 := by
  refine ⟨rfl, Caps.ExampleTwentySeven.null, Caps.ExampleTwentySeven.cap_displayed, ?_, ?_,
    Caps.ExampleTwentySeven.vector_fixed, Caps.ExampleTwentySeven.not_identity,
    Caps.ExampleTwentySeven.characteristic_unipotent X⟩
  · exact Caps.ExampleTwentySeven.cap_displayed ▸
      Cap.cap_isOrthogonal Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined
  · exact Caps.ExampleTwentySeven.cap_displayed ▸
      Cap.determinant_cap Caps.ExampleTwentySeven.vector Caps.ExampleTwentySeven.defined

/-- The original rational field has no nonidentity null-anchor cap. -/
private theorem rational_null_cap (vector : Vector3 Rational) (null : vector.quadrance = 0) :
    Cap.cap vector (FieldRealizations.RationalFieldClaims.capDenominator_ne_zero vector) = Matrix3.identity :=
  FieldRealizations.RationalFieldClaims.null_cap_eq_identity vector null

/-- The revised half-spread definition is the original trace-over-four expression. -/
private theorem half_spread_definition (rotation : Rotation K) :
    Spread.halfSpread rotation = (3 - Matrix3.trace rotation.matrix) / 4 := rfl

/-- All six revised cap half-spread identities retain their original denominator and recovery formula. -/
private theorem cap_half_spread_identities (vector : Vector3 K)
    (defined : Cap.capDenominator vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Cap.capRotation vector defined) =
        vector.quadrance / Cap.capDenominator vector ∧
      1 - Spread.halfSpread (Cap.capRotation vector defined) = 1 / Cap.capDenominator vector ∧
      1 - 2 * Spread.halfSpread (Cap.capRotation vector defined) = (1 - vector.quadrance) / Cap.capDenominator vector ∧
      Spread.halfSpread (Cap.capRotation vector defined) * (1 - Spread.halfSpread (Cap.capRotation vector defined)) =
        vector.quadrance / Cap.capDenominator vector ^ 2 ∧
      Spread.halfSpread (Cap.capRotation vector defined) ≠ 1 ∧
      vector.quadrance = Spread.halfSpread (Cap.capRotation vector defined) /
        (1 - Spread.halfSpread (Cap.capRotation vector defined)) :=
  ⟨Spread.halfSpread_cap vector defined twoNonzero,
    Spread.one_sub_halfSpread_cap vector defined twoNonzero,
    Spread.one_sub_two_mul_halfSpread_cap vector defined twoNonzero,
    Spread.halfSpread_mul_one_sub_cap vector defined twoNonzero,
    Spread.halfSpread_cap_ne_one vector defined twoNonzero,
    Spread.quadrance_eq_halfSpread_div_one_sub vector defined twoNonzero⟩

/-- Every original Euclidean half turn has half spread one. -/
private theorem half_spread_half_turn (axis : Vector3 K) (nonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Reflection.halfTurnRotation axis nonNull) = 1 :=
  Spread.halfSpread_halfTurn axis nonNull twoNonzero

/-- Ordered cap half spread has the claimed endpoint and strict upper bound for the original retained order. -/
private theorem cap_half_spread_interval {F : Type*} [RayOrderedExplicitField F]
    (law : OrderDifferenceLaw F) (vector : Vector3 F) (defined : Cap.capDenominator vector ≠ 0)
    (twoNonzero : (2 : F) ≠ 0) :
    (Spread.halfSpread (Cap.capRotation vector defined) = 0 ∨ 0 < Spread.halfSpread (Cap.capRotation vector defined)) ∧
      Spread.halfSpread (Cap.capRotation vector defined) < 1 :=
  FieldRealizations.OrderedFieldClaims.halfSpread_cap_unit_interval law vector defined twoNonzero

/-- Every requested finite odd-field half spread has an original non-null quaternion rotation preimage. -/
private theorem finite_half_spread_surjective
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) (value : K) :
    ∃ proportion : NonNullProportion K,
      Spread.halfSpread (Action.NonNullProportion.rotation proportion) = value :=
  presentation.halfSpread_surjective value

/-- A geometric measurement is the original vector spread between the retained vector and its image. -/
private theorem rotation_spread_definition (rotation : Rotation K) (vector : Vector3 K)
    (nonNull : vector.quadrance ≠ 0) :
    Spread.rotationSpreadAt rotation vector nonNull = Vector3.spread vector (Matrix3.rowMul vector rotation.matrix)
      nonNull (Spread.rowMul_rotation_nonNull rotation vector nonNull) := rfl

/-- Every original Euclidean axis has an executable retained non-null perpendicular measurement vector. -/
private def perpendicular_measurement [DecidableEq K] (axis : Vector3 K) (twoNonzero : (2 : K) ≠ 0) :
    Perpendicular.PerpendicularNonNullWitness axis := Perpendicular.perpendicularNonNullWitness axis twoNonzero

/-- Every original cap measurement on a non-null perpendicular vector is its revised half-spread polynomial. -/
private theorem cap_geometric_spread (axis vector : Vector3 K) (defined : Cap.capDenominator axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (nonNull : vector.quadrance ≠ 0) (perpendicular : vector.Perpendicular axis) :
    Spread.rotationSpreadAt (Cap.capRotation axis defined) vector nonNull =
      4 * Spread.halfSpread (Cap.capRotation axis defined) * (1 - Spread.halfSpread (Cap.capRotation axis defined)) :=
  Spread.rotationSpreadAt_cap axis defined twoNonzero vector nonNull perpendicular

/-- Every original half-turn measurement on a non-null perpendicular vector is the same revised polynomial. -/
private theorem half_turn_geometric_spread (axis vector : Vector3 K) (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (nonNull : vector.quadrance ≠ 0) (perpendicular : vector.Perpendicular axis) :
    Spread.rotationSpreadAt (Reflection.halfTurnRotation axis axisNonNull) vector nonNull =
      4 * Spread.halfSpread (Reflection.halfTurnRotation axis axisNonNull) *
        (1 - Spread.halfSpread (Reflection.halfTurnRotation axis axisNonNull)) :=
  Spread.rotationSpreadAt_halfTurn axis axisNonNull twoNonzero vector nonNull perpendicular

/-- Both original rotation charts give the same spread on any two admissible perpendicular measurement vectors. -/
private theorem geometric_spread_independent (axis first second : Vector3 K)
    (defined : Cap.capDenominator axis ≠ 0) (axisNonNull : axis.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (firstNonNull : first.quadrance ≠ 0) (firstPerpendicular : first.Perpendicular axis)
    (secondNonNull : second.quadrance ≠ 0) (secondPerpendicular : second.Perpendicular axis) :
    Spread.rotationSpreadAt (Cap.capRotation axis defined) first firstNonNull =
        Spread.rotationSpreadAt (Cap.capRotation axis defined) second secondNonNull ∧
      Spread.rotationSpreadAt (Reflection.halfTurnRotation axis axisNonNull) first firstNonNull =
        Spread.rotationSpreadAt (Reflection.halfTurnRotation axis axisNonNull) second secondNonNull :=
  ⟨Spread.rotationSpreadAt_cap_independent axis defined twoNonzero first second
      firstNonNull secondNonNull firstPerpendicular secondPerpendicular,
    Spread.rotationSpreadAt_halfTurn_independent axis axisNonNull twoNonzero first second
      firstNonNull secondNonNull firstPerpendicular secondPerpendicular⟩

/-- The revised quadrance and null definitions reduce to the original displayed coordinates. -/
private theorem quadrance_coordinates (vector : Vector3 K) :
    vector.quadrance = vector.t ^ 2 + vector.r ^ 2 + vector.s ^ 2 ∧
      (vector.IsNull ↔ vector.quadrance = 0) := by
  constructor
  · simp only [Vector3.quadrance, Vector3.dot, pow_two, -eq_self, -iff_self]
    rfl
  · exact Iff.rfl

/-- The ordered-field null-vector claim uses the original ray-ordered field operations. -/
private theorem ordered_null_vector {F : Type*} [RayOrderedExplicitField F]
    (vector : Vector3 F) (null : vector.IsNull) : vector = Vector3.zero :=
  Ordered.OrderedFieldClaims.only_zero_null_vector vector null

/-- The rational null-vector clause is public through the revised facade. -/
private theorem rational_null_vector (vector : Vector3 Rational) (null : vector.IsNull) :
    vector = Vector3.zero := NullVectors.rational_only_zero_null_vector vector null

/-- An original finite odd-field presentation computes its retained nonzero null vector. -/
private def finite_null_vector
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) :
    NullVectors.NonzeroNullVector K := presentation.nullCertificate.witness

/-- The finite odd-field witness retains both required mathematical certificates. -/
private theorem finite_null_vector_spec
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) :
    (finite_null_vector presentation).vector.IsNull ∧
      (finite_null_vector presentation).vector ≠ Vector3.zero :=
  ⟨(finite_null_vector presentation).null, (finite_null_vector presentation).nonzero⟩

/-- The revised finite-field example is literally `(1,2,0)`, null, nonzero and self-perpendicular. -/
private theorem field_five_null_example :
    Five.FieldFive.nullVector = ⟨1, 2, 0⟩ ∧
      Five.FieldFive.nullVector.IsNull ∧
      Five.FieldFive.nullVector ≠ Vector3.zero ∧
      Five.FieldFive.nullVector.Perpendicular Five.FieldFive.nullVector :=
  ⟨rfl, Five.FieldFive.nullVector_isNull, Five.FieldFive.nullVector_ne_zero,
    Five.FieldFive.nullVector_perpendicular_self⟩

/-- Spread has the literal revised formula and is one exactly for perpendicular non-null vectors. -/
private theorem spread_definition [DecidableEq K] (left right : Vector3 K)
    (leftNonNull : left.quadrance ≠ 0) (rightNonNull : right.quadrance ≠ 0) :
    Vector3.spread left right leftNonNull rightNonNull =
        1 - (left.dot right) ^ 2 / (left.quadrance * right.quadrance) ∧
      (Vector3.spread left right leftNonNull rightNonNull = 1 ↔ left.Perpendicular right) :=
  ⟨rfl, Vector3.spread_eq_one_iff_perpendicular left right leftNonNull rightNonNull⟩

/-- Both independent nonzero line rescalings preserve the revised spread. -/
private theorem spread_lines (left right : Vector3 K) (factor : K) (nonzero : factor ≠ 0)
    (leftNonNull : left.quadrance ≠ 0) (rightNonNull : right.quadrance ≠ 0) :
    Vector3.spread (Vector3.scale factor left) right
        (Vector3.quadrance_scale_ne_zero factor left nonzero leftNonNull) rightNonNull =
      Vector3.spread left right leftNonNull rightNonNull ∧
    Vector3.spread left (Vector3.scale factor right) leftNonNull
        (Vector3.quadrance_scale_ne_zero factor right nonzero rightNonNull) =
      Vector3.spread left right leftNonNull rightNonNull :=
  ⟨Vector3.spread_scale_left factor left right nonzero leftNonNull rightNonNull,
    Vector3.spread_scale_right factor left right nonzero leftNonNull rightNonNull⟩

/-- All scalar and vector identities in the revised vector-algebra theorem retain their original signs. -/
private theorem vector_algebra (u v w z : Vector3 K) :
    (Vector3.cross u v).dot w = Vector3.determinant u v w ∧
      (Vector3.cross u v).dot u = 0 ∧ (Vector3.cross u v).dot v = 0 ∧
      Vector3.cross u (Vector3.cross v w) =
        Vector3.sub (Vector3.scale (u.dot w) v) (Vector3.scale (u.dot v) w) ∧
      (Vector3.cross u v).dot (Vector3.cross w z) = u.dot w * v.dot z - u.dot z * v.dot w :=
  ⟨Vector3.scalar_triple_product u v w, Vector3.cross_dot_left u v, Vector3.cross_dot_right u v,
    Vector3.vector_triple_product u v w, Vector3.binet_cauchy u v w z⟩

/-- The revised Lagrange identity and its divided cross-quadrance formula are both public. -/
private theorem lagrange_spread (left right : Vector3 K)
    (leftNonNull : left.quadrance ≠ 0) (rightNonNull : right.quadrance ≠ 0) :
    (left.dot right) ^ 2 + (Vector3.cross left right).quadrance = left.quadrance * right.quadrance ∧
      Vector3.spread left right leftNonNull rightNonNull =
        (Vector3.cross left right).quadrance / (left.quadrance * right.quadrance) :=
  ⟨Vector3.lagrange left right,
    Vector3.spread_eq_cross_quadrance left right leftNonNull rightNonNull⟩

/-- A nonzero null cross product gives zero spread and excludes every equality of the two lines. -/
private theorem null_cross_spread (left right : Vector3 K)
    (leftNonNull : left.quadrance ≠ 0) (rightNonNull : right.quadrance ≠ 0)
    (crossNull : (Vector3.cross left right).IsNull)
    (crossNonzero : Vector3.cross left right ≠ Vector3.zero) :
    Vector3.spread left right leftNonNull rightNonNull = 0 ∧
      ¬ ∃ factor : K, factor ≠ 0 ∧ right = Vector3.scale factor left := by
  constructor
  · rw [Vector3.spread_eq_cross_quadrance, crossNull, ExplicitField.zero_div]
  · rintro ⟨factor, _, scaled⟩
    apply crossNonzero
    rw [scaled, Vector3.cross_scale_right]
    have selfCross : Vector3.cross left left = Vector3.zero := by
      apply Vector3.ext <;> unfold Vector3.cross Vector3.zero <;> ring1
    rw [selfCross, Vector3.scale_zero]

/-- The ordered spread bounds use the same retained strict comparison and explicit difference law. -/
private theorem spread_interval {F : Type*} [RayOrderedExplicitField F]
    (law : OrderDifferenceLaw F) (left right : Vector3 F)
    (leftNonNull : left.quadrance ≠ 0) (rightNonNull : right.quadrance ≠ 0) :
    (Vector3.spread left right leftNonNull rightNonNull = 0 ∨
      0 < Vector3.spread left right leftNonNull rightNonNull) ∧
    (Vector3.spread left right leftNonNull rightNonNull = 1 ∨
      Vector3.spread left right leftNonNull rightNonNull < 1) :=
  Ordered.OrderedFieldClaims.spread_unit_interval law left right leftNonNull rightNonNull

/-- The revised vanishing lemma has an arbitrary finite arity and retains its actual nonzero-locus condition. -/
private theorem vanishing {arity : Nat} (g h : Basic.Expression arity)
    (hNonzero : h.isZero = false)
    (vanishes : ∀ point : Basic.Point arity,
      h.eval point ≠ 0 → g.eval point = 0) : g.isZero = true :=
  Avoidance.isZero_of_vanishes_where_second_nonzero g h hNonzero vanishes

/-- The original integer-coefficient identity transfers from a nonzero rational locus to any supplied explicit field. -/
private theorem integral_identity_transfer {arity : Nat} (polynomial locus : Basic.Expression arity)
    (integral : polynomial.Integral) (locusNonzero : locus.isZero = false)
    (vanishes : ∀ point : Basic.Point arity,
      locus.eval point ≠ 0 → polynomial.eval point = 0)
    (point : Basic.PointOver K arity) : polynomial.evalIntegral integral point = 0 :=
  polynomial.transfer_integral_identity locus integral locusNonzero vanishes point

/-- The certified integer evaluation retains the original rational coefficients and coordinate tuple. -/
private theorem integral_rational_agreement {arity : Nat} (polynomial : Basic.Expression arity)
    (integral : polynomial.Integral) (point : Basic.PointOver Rational arity) :
    polynomial.evalIntegral integral point = polynomial.eval point.toRationalPoint :=
  polynomial.evalIntegral_rational integral point

/-- The original anchor coordinates, linear laws and both inverse readbacks remain public. -/
private theorem anchor_bijection (v w : Vector3 K) (factor : K) (A : Matrix3 K)
    (twoNonzero : (2 : K) ≠ 0) (antisymmetric : A.IsAntisymmetric) :
    Antisymmetric.anchor v = ⟨0, v.s, -v.r, -v.s, 0, v.t, v.r, -v.t, 0⟩ ∧
      (Antisymmetric.anchor v).IsAntisymmetric ∧
      Antisymmetric.anchor (Vector3.add v w) = Matrix3.add (Antisymmetric.anchor v) (Antisymmetric.anchor w) ∧
      Antisymmetric.anchor (Vector3.scale factor v) = Matrix3.scale factor (Antisymmetric.anchor v) ∧
      Antisymmetric.anchorVector (Antisymmetric.anchor v) = v ∧
      Antisymmetric.anchor (Antisymmetric.anchorVector A) = A :=
  ⟨rfl, Antisymmetric.anchor_isAntisymmetric v, Antisymmetric.anchor_add v w,
    Antisymmetric.anchor_scale factor v, Antisymmetric.anchorVector_anchor v,
    Antisymmetric.anchor_anchorVector_of_isAntisymmetric A twoNonzero antisymmetric⟩

/-- Row action by the revised anchor is the original signed cross product. -/
private theorem anchor_action (v w : Vector3 K) :
    Matrix3.rowMul w (Antisymmetric.anchor v) = Vector3.cross v w ∧
      Matrix3.rowMul v (Antisymmetric.anchor v) = Vector3.zero :=
  ⟨Antisymmetric.rowMul_anchor v w, Antisymmetric.rowMul_self_anchor v⟩

/-- The revised anchor-product theorem retains the reversed outer-product order. -/
private theorem anchor_product (v w : Vector3 K) :
    Matrix3.mul (Antisymmetric.anchor v) (Antisymmetric.anchor w) =
      Matrix3.sub (Matrix3.outer w v) (Matrix3.scale (v.dot w) Matrix3.identity) :=
  Antisymmetric.anchor_product v w

/-- The four revised anchor corollaries retain the square, commutator, sandwich and trace signs. -/
private theorem anchor_corollaries (v w : Vector3 K) :
    Matrix3.mul (Antisymmetric.anchor v) (Antisymmetric.anchor v) =
        Matrix3.sub (Matrix3.outer v v) (Matrix3.scale v.quadrance Matrix3.identity) ∧
      Matrix3.sub (Matrix3.mul (Antisymmetric.anchor v) (Antisymmetric.anchor w))
        (Matrix3.mul (Antisymmetric.anchor w) (Antisymmetric.anchor v)) =
          Matrix3.sub (Matrix3.outer w v) (Matrix3.outer v w) ∧
      Matrix3.sub (Matrix3.mul (Antisymmetric.anchor v) (Antisymmetric.anchor w))
        (Matrix3.mul (Antisymmetric.anchor w) (Antisymmetric.anchor v)) =
          Antisymmetric.anchor (Vector3.cross w v) ∧
      Matrix3.mul (Matrix3.mul (Antisymmetric.anchor v) (Antisymmetric.anchor w)) (Antisymmetric.anchor v) =
        Matrix3.scale (-(v.dot w)) (Antisymmetric.anchor v) ∧
      Matrix3.trace (Matrix3.mul (Antisymmetric.anchor v) (Antisymmetric.anchor w)) = -2 * v.dot w :=
  ⟨Antisymmetric.anchor_square v,
    (Antisymmetric.anchor_commutator v w).trans (Antisymmetric.outer_commutator_eq_anchor_cross w v).symm,
    Antisymmetric.anchor_commutator v w,
    Antisymmetric.anchor_sandwich v w, Antisymmetric.trace_anchor_product v w⟩

/-- The revised anchor form, quadrance and isometry use the original determinant-free definitions. -/
private theorem anchor_isometry (v w : Vector3 K) (A B : Matrix3 K) (twoNonzero : (2 : K) ≠ 0) :
    Antisymmetric.anchorForm A B = -Matrix3.trace (Matrix3.mul A B) / 2 ∧
      Antisymmetric.anchorQuadrance A = Antisymmetric.anchorForm A A ∧
      Antisymmetric.anchorForm (Antisymmetric.anchor v) (Antisymmetric.anchor w) = v.dot w ∧
      Antisymmetric.anchorQuadrance (Antisymmetric.anchor v) = v.quadrance :=
  ⟨rfl, rfl, Antisymmetric.anchorForm_anchor v w twoNonzero, Antisymmetric.anchorQuadrance_anchor v twoNonzero⟩

/-- The complete revised anchor characteristic polynomial and vanishing trace and determinant are public. -/
private theorem anchor_characteristic (v : Vector3 K) (X : K) :
    Matrix3.characteristicValue (Antisymmetric.anchor v) X = X * (X ^ 2 + v.quadrance) ∧
      Matrix3.trace (Antisymmetric.anchor v) = 0 ∧ Matrix3.determinant (Antisymmetric.anchor v) = 0 :=
  ⟨Antisymmetric.characteristicValue_anchor v X, Antisymmetric.trace_anchor v, Antisymmetric.determinant_anchor v⟩

/-- The revised reflection formula and its dependence on the normal line retain the original matrix. -/
private theorem reflection_definition (axis : Vector3 K) (nonNull : axis.quadrance ≠ 0)
    (factor : K) (nonzero : factor ≠ 0) :
    Reflection.reflection axis nonNull =
        Matrix3.sub Matrix3.identity (Matrix3.scale (2 / axis.quadrance) (Matrix3.outer axis axis)) ∧
      Reflection.reflection (Vector3.scale factor axis)
        (Vector3.quadrance_scale_ne_zero factor axis nonzero nonNull) = Reflection.reflection axis nonNull :=
  ⟨rfl, Reflection.reflection_scale factor axis nonzero nonNull⟩

/-- All five revised reflection clauses apply to the original Euclidean matrix. -/
private theorem reflection_laws (axis vector : Vector3 K) (nonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.transpose (Reflection.reflection axis nonNull) = Reflection.reflection axis nonNull ∧
      Matrix3.mul (Reflection.reflection axis nonNull) (Reflection.reflection axis nonNull) = Matrix3.identity ∧
      Matrix3.rowMul axis (Reflection.reflection axis nonNull) = Vector3.neg axis ∧
      (Matrix3.rowMul vector (Reflection.reflection axis nonNull) = vector ↔ vector.Perpendicular axis) ∧
      (Reflection.reflection axis nonNull).IsOrthogonal ∧
      Matrix3.determinant (Reflection.reflection axis nonNull) = -1 :=
  ⟨Reflection.reflection_transpose axis nonNull, Reflection.reflection_square axis nonNull,
    Reflection.rowMul_self_reflection axis nonNull,
    Reflection.rowMul_reflection_eq_iff_perpendicular axis nonNull twoNonzero vector,
    Reflection.reflection_isOrthogonal axis nonNull, Reflection.determinant_reflection axis nonNull⟩

/-- Original reflection row action preserves every dot product. -/
private theorem reflection_pairing (axis first second : Vector3 K) (nonNull : axis.quadrance ≠ 0) :
    (Matrix3.rowMul first (Reflection.reflection axis nonNull)).dot
        (Matrix3.rowMul second (Reflection.reflection axis nonNull)) = first.dot second :=
  Reflection.dot_rowMul_reflection axis nonNull first second

/-- The revised half turn is the negative reflection and has the literal projection matrix. -/
private theorem half_turn_definition (axis : Vector3 K) (nonNull : axis.quadrance ≠ 0) :
    Reflection.halfTurn axis nonNull = Matrix3.neg (Reflection.reflection axis nonNull) ∧
      Reflection.halfTurn axis nonNull =
        Matrix3.add (Matrix3.neg Matrix3.identity)
          (Matrix3.scale (2 / axis.quadrance) (Matrix3.outer axis axis)) := by
  constructor
  · rfl
  · apply Matrix3.ext <;>
      unfold Reflection.halfTurn Reflection.reflection Matrix3.neg Matrix3.sub Matrix3.add <;> ring1

/-- The original half turn fixes its axis, negates the perpendicular plane, and is an involution in SO(3). -/
private theorem half_turn_laws (axis vector : Vector3 K) (nonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (perpendicular : vector.Perpendicular axis) :
    (Reflection.halfTurn axis nonNull).IsSpecialOrthogonal ∧
      Matrix3.rowMul axis (Reflection.halfTurn axis nonNull) = axis ∧
      Matrix3.rowMul vector (Reflection.halfTurn axis nonNull) = Vector3.neg vector ∧
      Matrix3.mul (Reflection.halfTurn axis nonNull) (Reflection.halfTurn axis nonNull) = Matrix3.identity :=
  ⟨Reflection.halfTurn_isSpecialOrthogonal axis nonNull, Reflection.rowMul_self_halfTurn axis nonNull,
    Reflection.rowMul_halfTurn_of_perpendicular axis nonNull twoNonzero vector perpendicular,
    Reflection.halfTurn_square axis nonNull⟩

/-- The revised uniqueness clause is public for every original Euclidean half-turn matrix. -/
private theorem half_turn_unique (axis : Vector3 K) (nonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (matrix : Matrix3 K)
    (fixesAxis : Matrix3.rowMul axis matrix = axis)
    (negatesPerpendicular : ∀ vector : Vector3 K, vector.Perpendicular axis →
      Matrix3.rowMul vector matrix = Vector3.neg vector) : matrix = Reflection.halfTurn axis nonNull :=
  Reflection.halfTurn_unique axis nonNull twoNonzero matrix fixesAxis negatesPerpendicular

/-- The fixed vectors of the original Euclidean half turn are exactly all scalar multiples of its axis. -/
private theorem half_turn_fixed_line (axis vector : Vector3 K) (nonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul vector (Reflection.halfTurn axis nonNull) = vector ↔
      ∃ factor : K, vector = Vector3.scale factor axis := by
  constructor
  · intro fixed
    exact ⟨vector.dot axis / axis.quadrance,
      (Reflection.rowMul_halfTurn_eq_self_iff_projection axis nonNull twoNonzero vector).mp fixed⟩
  · rintro ⟨factor, scaled⟩
    rw [scaled, Matrix3.rowMul_vector_scale, Reflection.rowMul_self_halfTurn]

/-- Equality of original Euclidean half turns is precisely equality of their non-null axis lines. -/
private theorem half_turn_lines (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Reflection.halfTurn first firstNonNull = Reflection.halfTurn second secondNonNull ↔
      ∃ factor : K, factor ≠ 0 ∧ second = Vector3.scale factor first :=
  Reflection.halfTurn_eq_iff_same_line first second firstNonNull secondNonNull twoNonzero

/-- Every original Euclidean rotation has an executable certified two-reflection factorization. -/
private def two_reflections [DecidableEq K] (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    Axis.Recovery.ReflectionFactorization rotation := Axis.Recovery.twoReflectionsTheorem rotation twoNonzero

/-- Every product of two retained non-null Euclidean reflection matrices is a rotation. -/
private theorem two_reflections_converse (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0) :
    (Matrix3.mul (Reflection.reflection first firstNonNull)
      (Reflection.reflection second secondNonNull)).IsSpecialOrthogonal :=
  Reflection.reflection_product_isSpecialOrthogonal first second firstNonNull secondNonNull

/-- Identity-form mirror products in the nonunique factorization have the original Euclidean reflection matrices. -/
private theorem reflection_product_identity_form (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0)
    (oneNonzero : (1 : K) ≠ 0) :
    Matrix3.mul (Reflection.reflection first firstNonNull) (Reflection.reflection second secondNonNull) =
      Matrix3.mul
        ((TernaryForm.euclidean oneNonzero).reflection first
          (by rw [TernaryForm.quadrance_euclidean]; exact firstNonNull))
        ((TernaryForm.euclidean oneNonzero).reflection second
          (by rw [TernaryForm.quadrance_euclidean]; exact secondNonNull)) :=
  congrArg₂ Matrix3.mul (Reflection.reflection_eq_euclidean first firstNonNull oneNonzero)
    (Reflection.reflection_eq_euclidean second secondNonNull oneNonzero)

/-- The cross-product axis of the original reflection product and every scalar multiple are fixed. -/
private theorem reflection_product_axis (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (factor : K) :
    Matrix3.rowMul (Vector3.scale factor (Vector3.cross first second))
        (Matrix3.mul (Reflection.reflection first firstNonNull) (Reflection.reflection second secondNonNull)) =
      Vector3.scale factor (Vector3.cross first second) := by
  rw [Matrix3.rowMul_vector_scale,
    Reflection.rowMul_cross_reflection_product first second firstNonNull secondNonNull twoNonzero]

/-- The revised reflection example retains its two normals, quadrances, displayed matrices and fixed axis. -/
private theorem reflection_example :
    Reflections.ExampleTwenty.first = (⟨1, 2, 3⟩ : Vector3 Rational) ∧
      Reflections.ExampleTwenty.second = (⟨2, 1, -1⟩ : Vector3 Rational) ∧
      Reflections.ExampleTwenty.first.quadrance = 14 ∧ Reflections.ExampleTwenty.second.quadrance = 6 ∧
      Reflection.reflection Reflections.ExampleTwenty.first Reflections.ExampleTwenty.first_nonNull =
        Matrix3.scale (1 / 7) (⟨6, -2, -3, -2, 3, -6, -3, -6, -2⟩ : Matrix3 Rational) ∧
      Reflection.reflection Reflections.ExampleTwenty.second Reflections.ExampleTwenty.second_nonNull =
        Matrix3.scale (1 / 3) (⟨-1, -2, 2, -2, 2, 1, 2, 1, 2⟩ : Matrix3 Rational) ∧
      Matrix3.mul (Reflection.reflection Reflections.ExampleTwenty.first Reflections.ExampleTwenty.first_nonNull)
          (Reflection.reflection Reflections.ExampleTwenty.second Reflections.ExampleTwenty.second_nonNull) =
        Matrix3.scale (1 / 21) (⟨-8, -19, 4, -16, 4, -13, 11, -8, -16⟩ : Matrix3 Rational) ∧
      Vector3.cross Reflections.ExampleTwenty.first Reflections.ExampleTwenty.second =
        (⟨-5, 7, -3⟩ : Vector3 Rational) ∧
      Matrix3.rowMul Reflections.ExampleTwenty.axis Reflections.ExampleTwenty.productDisplayed =
        Reflections.ExampleTwenty.axis :=
  ⟨rfl, rfl, Reflections.ExampleTwenty.first_quadrance, Reflections.ExampleTwenty.second_quadrance,
    Reflections.ExampleTwenty.first_reflection_displayed, Reflections.ExampleTwenty.second_reflection_displayed,
    Reflections.ExampleTwenty.product_displayed, Reflections.ExampleTwenty.cross_displayed,
    Reflections.ExampleTwenty.axis_fixed⟩

/-- The matrix determinant law is reachable for an explicitly supplied imaginary unit. -/
private theorem matrix_norm (i : K) (iSquare : i ^ 2 = -1) (value : Proportion K) :
    Purelib.LinearAlgebra.Coordinates2.Matrix.determinant (Matrix.toMatrix i value) =
      Proportion.norm value := Matrix.determinant_toMatrix i iSquare value

/-- The matrix product law is reachable in the same row-action convention. -/
private theorem matrix_product (i : K) (iSquare : i ^ 2 = -1) (left right : Proportion K) :
    Matrix.toMatrix i (Proportion.mul left right) =
      Purelib.LinearAlgebra.Coordinates2.Matrix.mul (Matrix.toMatrix i left) (Matrix.toMatrix i right) :=
  Matrix.toMatrix_mul i iSquare left right

/-- Matrix decoding is available as a genuine inverse through the publication facade. -/
private theorem matrix_recovery (i : K) (iNonzero : i ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (matrix : Purelib.LinearAlgebra.Coordinates2.Matrix K) :
    Matrix.toMatrix i (Matrix.fromMatrix i matrix) = matrix :=
  Matrix.toMatrix_fromMatrix i iNonzero twoNonzero matrix

/-- The original Euclidean rotation has a nonzero fixed direction through the revised facade. -/
private def fixed_direction [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    Σ' vector : Vector3 K, vector ≠ Vector3.zero ∧ Matrix3.rowMul vector rotation.matrix = vector :=
  rotation.fixedDirection twoNonzero

/-- The general ternary characteristic law applies to the original Euclidean rotation matrix. -/
private theorem characteristic (rotation : Rotation K) (oneNonzero : (1 : K) ≠ 0) (X : K) :
    Matrix3.characteristicValue rotation.matrix X =
      (X - 1) * (X ^ 2 - (Matrix3.trace rotation.matrix - 1) * X + 1) :=
  (rotation.toTernary oneNonzero).characteristicValue_matrix X

/-- The shared characteristic polynomial uses the original Euclidean trace half spread. -/
private theorem half_spread_characteristic (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) (X : K) :
    Matrix3.characteristicValue rotation.matrix X =
      (X - 1) * (X ^ 2 - 2 * (1 - 2 * Spread.halfSpread rotation) * X + 1) :=
  (TernaryForm.euclidean (one_ne_zero_of_nonzero twoNonzero)).characteristicValue_rotation_halfSpread
    (rotation.toTernary (one_ne_zero_of_nonzero twoNonzero)) twoNonzero X

/-- The original Euclidean rotation has a non-null half-turn axis when its half spread is one. -/
private def half_turn_converse [DecidableEq K] (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (halfSpreadOne : Spread.halfSpread rotation = 1) :
    Σ' axis : Vector3 K, Σ' nonNull : Vector3.quadrance axis ≠ 0,
      Reflection.halfTurnRotation axis nonNull = rotation :=
  rotation.halfTurnWitness twoNonzero halfSpreadOne

/-- The original Euclidean rotation has a retained geometric measurement of its trace spread polynomial. -/
private def geometric_spread_witness [DecidableEq K] (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    let form := TernaryForm.euclidean (one_ne_zero_of_nonzero twoNonzero)
    let converted := rotation.toTernary (one_ne_zero_of_nonzero twoNonzero)
    Σ' witness : Ternary.Cayley.TernaryForm.RotationAxisSpreadWitness form converted,
      form.spread witness.perpendicular (TernaryForm.Isometry.act converted.toIsometry witness.perpendicular)
        witness.perpendicularNonNull
        (converted.toIsometry.quadrance_act_ne_zero witness.perpendicular witness.perpendicularNonNull) =
          4 * Spread.halfSpread rotation * (1 - Spread.halfSpread rotation) :=
  Ternary.Cayley.TernaryForm.geometricSpreadWitness
    (TernaryForm.euclidean (one_ne_zero_of_nonzero twoNonzero))
    (rotation.toTernary (one_ne_zero_of_nonzero twoNonzero)) twoNonzero

/-- The squared-rotation half-spread law holds for every original Euclidean rotation. -/
private theorem square_half_spread (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Rotation.mul rotation rotation) =
      4 * Spread.halfSpread rotation * (1 - Spread.halfSpread rotation) :=
  rotation.halfSpread_square twoNonzero

/-- The literal spread-of-normals law is public for the original Euclidean reflection product. -/
private theorem normals_half_spread (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Reflection.reflectionProductRotation first second firstNonNull secondNonNull) =
      Vector3.spread first second firstNonNull secondNonNull :=
  Spread.halfSpread_reflectionProduct first second firstNonNull secondNonNull twoNonzero

/-- Perpendicular original Euclidean normals construct a certified half turn about a non-null axis. -/
private def perpendicular_normals_half_turn [DecidableEq K] (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (perpendicular : first.Perpendicular second) :
    Σ' axis : Vector3 K, Σ' nonNull : axis.quadrance ≠ 0,
      Reflection.halfTurnRotation axis nonNull =
        Reflection.reflectionProductRotation first second firstNonNull secondNonNull := by
  apply (Reflection.reflectionProductRotation first second firstNonNull secondNonNull).halfTurnWitness twoNonzero
  rw [Spread.halfSpread_reflectionProduct first second firstNonNull secondNonNull twoNonzero]
  exact (Vector3.spread_eq_one_iff_perpendicular first second firstNonNull secondNonNull).mpr perpendicular

/-- The revised normals example retains all three rational spread and trace values. -/
private theorem normals_example :
    Vector3.spread Reflections.ExampleTwenty.first Reflections.ExampleTwenty.second
        Reflections.ExampleTwenty.first_nonNull Reflections.ExampleTwenty.second_nonNull = (83 : Rational) / 84 ∧
      Spread.halfSpread (Reflection.reflectionProductRotation
        Reflections.ExampleTwenty.first Reflections.ExampleTwenty.second
        Reflections.ExampleTwenty.first_nonNull Reflections.ExampleTwenty.second_nonNull) = (83 : Rational) / 84 ∧
      Matrix3.trace (Matrix3.mul
        (Reflection.reflection Reflections.ExampleTwenty.first Reflections.ExampleTwenty.first_nonNull)
        (Reflection.reflection Reflections.ExampleTwenty.second Reflections.ExampleTwenty.second_nonNull)) =
          (-20 : Rational) / 21 :=
  ⟨HalfSpreads.ExampleThirtyThree.spread_value, HalfSpreads.ExampleThirtyThree.product_halfSpread,
    HalfSpreads.ExampleThirtyThree.product_trace⟩

/-- The revised anchor domain is checked on the matrix of the original Euclidean rotation. -/
private theorem anchor_domain (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.determinant (Matrix3.add Matrix3.identity rotation.matrix) ≠ 0 ↔ Spread.halfSpread rotation ≠ 1 :=
  (rotation.toTernary (one_ne_zero_of_nonzero twoNonzero)).determinant_identity_add_ne_zero_iff twoNonzero

/-- The shared computed anchor has the literal Cayley inverse formula for the original Euclidean matrix. -/
private theorem anchor_inverse_formula (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) :
    let converted := rotation.toTernary (one_ne_zero_of_nonzero twoNonzero)
    let defined := (converted.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn
    let determinantNonzero := (converted.determinant_identity_add_ne_zero_iff twoNonzero).mpr notHalfTurn
    converted.anchor defined = Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
      (Matrix3.inverse (Matrix3.add Matrix3.identity rotation.matrix) determinantNonzero) :=
  (rotation.toTernary (one_ne_zero_of_nonzero twoNonzero)).anchor_eq_inverseFormula _ _

/-- The original Euclidean reflection product satisfies the literal cross and outer-product anchor formulas. -/
private theorem reflection_product_anchor (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0)
    (pairingNonzero : first.dot second ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    let rotation := Reflection.reflectionProductRotation first second firstNonNull secondNonNull
    let notHalfTurn := Axis.Recovery.reflectionProduct_notHalfTurn
      first second firstNonNull secondNonNull pairingNonzero twoNonzero
    let vector := Axis.Recovery.reflectionProductAnchorVector first second pairingNonzero
    Axis.Recovery.rotationAnchor rotation notHalfTurn = Antisymmetric.anchor vector ∧
      Axis.Recovery.rotationAnchor rotation notHalfTurn = Matrix3.scale (1 / first.dot second)
        (Matrix3.sub (Matrix3.outer first second) (Matrix3.outer second first)) ∧
      Axis.Recovery.rotationAnchorVector rotation notHalfTurn = vector ∧
      vector.quadrance = Vector3.spread first second firstNonNull secondNonNull /
        (1 - Vector3.spread first second firstNonNull secondNonNull) :=
  ⟨Axis.Recovery.rotationAnchor_reflectionProduct
      first second firstNonNull secondNonNull pairingNonzero twoNonzero,
    Axis.Recovery.rotationAnchor_reflectionProduct_outerFormula
      first second firstNonNull secondNonNull pairingNonzero twoNonzero,
    Axis.Recovery.rotationAnchorVector_reflectionProduct
      first second firstNonNull secondNonNull pairingNonzero twoNonzero,
    Axis.Recovery.quadrance_reflectionProductAnchorVector
      first second firstNonNull secondNonNull pairingNonzero twoNonzero⟩

/-- Independent nonzero scaling of the original Euclidean normals leaves their anchor vector unchanged. -/
private theorem reflection_anchor_lines (first second : Vector3 K) (leftScale rightScale : K)
    (leftNonzero : leftScale ≠ 0) (rightNonzero : rightScale ≠ 0) (pairingNonzero : first.dot second ≠ 0) :
    Axis.Recovery.reflectionProductAnchorVector (Vector3.scale leftScale first) (Vector3.scale rightScale second)
        (by rw [Vector3.dot_scale_left, Vector3.dot_scale_right]
            exact ExplicitField.mul_ne_zero leftNonzero (ExplicitField.mul_ne_zero rightNonzero pairingNonzero)) =
      Axis.Recovery.reflectionProductAnchorVector first second pairingNonzero :=
  Axis.Recovery.reflectionProductAnchorVector_scale first second leftScale rightScale
    leftNonzero rightNonzero pairingNonzero

/-- The revised Euclidean reflection-product example retains the vector `(-5,7,-3)` and half twist eighty-three. -/
private theorem reflection_anchor_example :
    Axis.Recovery.reflectionProductAnchorVector Reflections.ExampleTwenty.first Reflections.ExampleTwenty.second
        RotationAnchors.ExampleThirtyNine.dot_nonzero = (⟨-5, 7, -3⟩ : Vector3 Rational) ∧
      (Axis.Recovery.reflectionProductAnchorVector Reflections.ExampleTwenty.first Reflections.ExampleTwenty.second
        RotationAnchors.ExampleThirtyNine.dot_nonzero).quadrance = (83 : Rational) := by
  constructor
  · exact RotationAnchors.ExampleThirtyNine.recovered_vector
  · exact RotationAnchors.ExampleThirtyNine.recovered_quadrance

/-- A supplied original Euclidean first normal constructs the exact second cap normal and its product matrix. -/
private def free_first_cap_mirror (axis first : Vector3 K)
    (defined : Cap.capDenominator axis ≠ 0) (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular axis) (twoNonzero : (2 : K) ≠ 0) :
    Σ' second : Vector3 K, Σ' secondNonNull : second.quadrance ≠ 0,
      second = Vector3.add first (Vector3.cross axis first) ∧
        Matrix3.mul (Reflection.reflection first firstNonNull) (Reflection.reflection second secondNonNull) =
          Cap.cap axis defined :=
  ⟨Axis.Recovery.capSecondMirror axis first,
    Axis.Recovery.capSecondMirror_nonNull axis first defined firstNonNull perpendicular,
    rfl, Axis.Recovery.reflection_mul_capSecondMirror axis first defined firstNonNull perpendicular twoNonzero⟩

/-- A supplied original Euclidean first normal constructs the exact second half-turn normal and its product matrix. -/
private def free_first_half_turn_mirror (axis first : Vector3 K)
    (axisNonNull : axis.quadrance ≠ 0) (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular axis) :
    Σ' second : Vector3 K, Σ' secondNonNull : second.quadrance ≠ 0,
      second = Vector3.cross axis first ∧
        Matrix3.mul (Reflection.reflection first firstNonNull) (Reflection.reflection second secondNonNull) =
          Reflection.halfTurn axis axisNonNull :=
  ⟨Axis.Recovery.halfTurnSecondMirror axis first,
    Axis.Recovery.halfTurnSecondMirror_nonNull axis first axisNonNull firstNonNull perpendicular,
    rfl, Axis.Recovery.reflection_mul_halfTurnSecondMirror axis first axisNonNull firstNonNull perpendicular⟩

/-- The Euclidean anchor example's exact spread/complement ratio is public through the facade. -/
private theorem reflection_anchor_half_twist :
    Vector3.spread Reflections.ExampleTwenty.first Reflections.ExampleTwenty.second
        Reflections.ExampleTwenty.first_nonNull Reflections.ExampleTwenty.second_nonNull /
      (1 - Vector3.spread Reflections.ExampleTwenty.first Reflections.ExampleTwenty.second
        Reflections.ExampleTwenty.first_nonNull Reflections.ExampleTwenty.second_nonNull) = (83 : Rational) :=
  RotationAnchors.ExampleThirtyNine.half_twist

/-- The revised quaternion matrix dictionary agrees literally with the source Lorentz matrix coordinates. -/
private theorem matrix_lorentz_dictionary (oneNonzero : (1 : K) ≠ 0) (i : K) (value : Proportion K) :
    Matrix.toMatrix i value = Clifford.Lorentz.Matrix.toMatrix oneNonzero
      (Clifford.Lorentz.Matrix.coordinates oneNonzero value.scalar
        ⟨value.vector.t, i * value.vector.r, i * value.vector.s⟩) :=
  Matrix.toMatrix_eq_lorentz_coordinates oneNonzero i value

/-- The original Euclidean rotation matrix admits two certified mirror factorizations with distinct first lines. -/
private def distinct_mirror_factorizations [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    let oneNonzero := one_ne_zero_of_nonzero twoNonzero
    let form := TernaryForm.euclidean oneNonzero
    let converted := rotation.toTernary oneNonzero
    Σ' first : form.TwoHalfTurnFactorization converted, Σ' second : form.TwoHalfTurnFactorization converted,
      ¬ ∃ factor : K, factor ≠ 0 ∧ second.firstAxis = Vector3.scale factor first.firstAxis :=
  (TernaryForm.euclidean (one_ne_zero_of_nonzero twoNonzero)).distinctFirstMirrorFactorizations
    (rotation.toTernary (one_ne_zero_of_nonzero twoNonzero)) twoNonzero

/-- A finite odd-field square-table certificate supplies a complete quaternion matrix realization. -/
private theorem finite_split_matrix
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (left right : Proportion K) (matrix : Purelib.LinearAlgebra.Coordinates2.Matrix K) :
    let split := SplitMatrix.finiteSplit presentation
    Purelib.LinearAlgebra.Coordinates2.Matrix.determinant (SplitMatrix.toMatrix split left) = left.norm ∧
      SplitMatrix.toMatrix split (Proportion.mul left right) =
        Purelib.LinearAlgebra.Coordinates2.Matrix.mul
          (SplitMatrix.toMatrix split left) (SplitMatrix.toMatrix split right) ∧
      SplitMatrix.fromMatrix split (SplitMatrix.toMatrix split left) = left ∧
      SplitMatrix.toMatrix split (SplitMatrix.fromMatrix split matrix) = matrix :=
  ⟨SplitMatrix.determinant_toMatrix _ left, SplitMatrix.toMatrix_mul _ left right,
    SplitMatrix.fromMatrix_toMatrix _ presentation.twoNonzero left,
    SplitMatrix.toMatrix_fromMatrix _ presentation.twoNonzero matrix⟩

/-- The new split realization preserves the original imaginary-unit matrix body. -/
private theorem imaginary_split_dictionary (i : K) (iSquare : i ^ 2 = -1) (value : Proportion K) :
    SplitMatrix.toMatrix (SplitMatrix.imaginarySplit i iSquare) value = Matrix.toMatrix i value :=
  SplitMatrix.toMatrix_imaginarySplit i iSquare value

/-- The imaginary extension retains the entire original pair-ring record literally. -/
private theorem imaginary_extension_ring [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0) :
    (Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero).toCommRing =
      Quadratic.Pair.instCommRing (K := K) (radialSquare := (1 : K)) := rfl

/-- The extension's inverse and division use the computed conjugate-over-quadrance function. -/
private theorem imaginary_extension_operations [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (left right : Quadratic.Pair K (1 : K)) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    right⁻¹ = Quadratic.Pair.ImaginaryField.inverse right ∧
      left / right = left * Quadratic.Pair.ImaginaryField.inverse right := ⟨rfl, rfl⟩

/-- The original ordered-field certificate excludes square roots of negative one without a field completion. -/
private theorem ordered_imaginary_root_exclusion {F : Type*} [RayOrderedExplicitField F] :
    Field.Squares.NoSquareRootOfNegativeOne (K := F) :=
  Field.Squares.NoSquareRootOfNegativeOne.ofRayOrdered

/-- The formal quadratic field gives the revised extension matrix model for every original quaternion.

The matrix remains linear and multiplicative over the embedded ground field,
and its determinant is the image of the original input norm. The supplied
root exclusion is the certificate for the target field, not an assumed root.
-/
private theorem imaginary_extension_model [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (left right : Proportion K) (factor : K) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    let embedding := Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero
    let i := (Quadratic.Pair.generator : Quadratic.Pair K (1 : K))
    Matrix.toEmbeddedMatrix embedding i (Proportion.mul left right) =
        Matrix2.mul (Matrix.toEmbeddedMatrix embedding i left) (Matrix.toEmbeddedMatrix embedding i right) ∧
      Matrix.toEmbeddedMatrix embedding i (Proportion.add left right) =
        Matrix2.add (Matrix.toEmbeddedMatrix embedding i left) (Matrix.toEmbeddedMatrix embedding i right) ∧
      Matrix.toEmbeddedMatrix embedding i (Proportion.scale factor left) =
        Matrix2.scalarScale (embedding.toFun factor) (Matrix.toEmbeddedMatrix embedding i left) ∧
      Matrix2.determinant (Matrix.toEmbeddedMatrix embedding i left) = embedding.toFun left.norm ∧
      Matrix2.trace (Matrix.toEmbeddedMatrix embedding i left) = 2 * embedding.toFun left.scalar ∧
      Matrix.toEmbeddedMatrix embedding i (Proportion.conjugate left) =
        Matrix2.adjugate (Matrix.toEmbeddedMatrix embedding i left) := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  let embedding := Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero
  let i := (Quadratic.Pair.generator : Quadratic.Pair K (1 : K))
  exact ⟨Matrix.toEmbeddedMatrix_mul embedding i Quadratic.Pair.ImaginaryField.generator_square left right,
    Matrix.toEmbeddedMatrix_add embedding i left right,
    Matrix.toEmbeddedMatrix_scale embedding i factor left,
    Matrix.determinant_toEmbeddedMatrix embedding i Quadratic.Pair.ImaginaryField.generator_square left,
    Matrix.trace_toEmbeddedMatrix embedding i left, Matrix.toEmbeddedMatrix_conjugate embedding i left⟩

/-- The formal extension matrix reflects equality of the original quaternion coordinates. -/
private theorem imaginary_extension_injective [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (left right : Proportion K) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    let embedding := Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero
    let i := (Quadratic.Pair.generator : Quadratic.Pair K (1 : K))
    Matrix.toEmbeddedMatrix embedding i left = Matrix.toEmbeddedMatrix embedding i right → left = right := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  have targetTwoNonzero : (2 : Quadratic.Pair K (1 : K)) ≠ 0 :=
    Quadratic.Pair.ImaginaryField.two_ne_zero twoNonzero
  have generatorNonzero : (Quadratic.Pair.generator : Quadratic.Pair K (1 : K)) ≠ 0 :=
    Quadratic.Pair.ImaginaryField.generator_ne_zero twoNonzero
  exact Matrix.toEmbeddedMatrix_injective
    (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
    Quadratic.Pair.generator generatorNonzero targetTwoNonzero

/-- The revised trace identity holds for the original rotation in the formal extension matrix model. -/
private theorem imaginary_extension_halfSpread [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (proportion : NonNullProportion K) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    let embedding := Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero
    let i := (Quadratic.Pair.generator : Quadratic.Pair K (1 : K))
    embedding.toFun (1 - Spread.halfSpread (Action.NonNullProportion.rotation proportion)) =
      (Matrix2.trace (Matrix.toEmbeddedMatrix embedding i proportion.toProportion)) ^ 2 /
        (4 * Matrix2.determinant (Matrix.toEmbeddedMatrix embedding i proportion.toProportion)) := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  have targetTwoNonzero : (2 : Quadratic.Pair K (1 : K)) ≠ 0 :=
    Quadratic.Pair.ImaginaryField.two_ne_zero twoNonzero
  exact Action.NonNullProportion.one_sub_halfSpread_embedded_matrix_trace
    (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero) proportion
    twoNonzero targetTwoNonzero Quadratic.Pair.generator Quadratic.Pair.ImaginaryField.generator_square

/-- A supplied ground-field imaginary unit gives the same trace identity without scalar extension. -/
private theorem ground_field_matrix_halfSpread (twoNonzero : (2 : K) ≠ 0)
    (i : K) (iSquare : i ^ 2 = -1) (proportion : NonNullProportion K) :
    1 - Spread.halfSpread (Action.NonNullProportion.rotation proportion) =
      (Matrix2.trace (Matrix.toMatrix i proportion.toProportion)) ^ 2 /
        (4 * Matrix2.determinant (Matrix.toMatrix i proportion.toProportion)) :=
  Action.NonNullProportion.one_sub_halfSpread_matrix_trace proportion twoNonzero i iSquare

/-- The original scalar embedding gives exactly the revised extension matrix coordinates. -/
private theorem imaginary_matrix_coordinates [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (value : Proportion K) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    Matrix.toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
      Quadratic.Pair.generator value =
        ⟨⟨value.scalar, value.vector.s⟩, ⟨-value.vector.t, value.vector.r⟩,
          ⟨value.vector.t, value.vector.r⟩, ⟨value.scalar, -value.vector.s⟩⟩ :=
  Matrix.toEmbeddedMatrix_imaginaryField noRoot twoNonzero value

/-- The quaternion and ground-field matrix algebras have the two distinct conjugation fixed-form descriptions. -/
private theorem imaginary_matrix_forms [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (matrix : Matrix2 (Quadratic.Pair K (1 : K))) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    ((∃ value : Proportion K,
      Matrix.toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
        Quadratic.Pair.generator value = matrix) ↔
      Matrix2.mul (Matrix2.mul ⟨0, -1, 1, 0⟩ matrix) ⟨0, 1, -1, 0⟩ =
        Matrix2.map Quadratic.Pair.conjugate matrix) ∧
      (Matrix2.map Quadratic.Pair.conjugate matrix = matrix ↔
        ∃ base : Matrix2 K, Matrix2.map Quadratic.Pair.scalar base = matrix) := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  exact ⟨Matrix.imaginary_image_iff_fixed noRoot twoNonzero matrix,
    Matrix.conjugation_fixed_iff_base_matrix twoNonzero matrix⟩

/-- The displayed Pauli basis retains all three literal matrices and the original signed quaternion coordinates. -/
private theorem pauli_matrix_dictionary (i : K) (iSquare : i ^ 2 = -1) (value : Proportion K) :
    Matrix.Pauli.first = (⟨0, 1, 1, 0⟩ : Matrix2 K) ∧
      Matrix.Pauli.second i = ⟨0, -i, i, 0⟩ ∧
      Matrix.Pauli.third = (⟨1, 0, 0, -1⟩ : Matrix2 K) ∧
      Matrix.toMatrix i value = Matrix2.add (Matrix2.scalarScale value.scalar Matrix2.identity)
        (Matrix2.scalarScale i (Matrix2.add
          (Matrix2.add (Matrix2.scalarScale value.vector.r Matrix.Pauli.first)
            (Matrix2.scalarScale (-value.vector.t) (Matrix.Pauli.second i)))
          (Matrix2.scalarScale value.vector.s Matrix.Pauli.third))) :=
  ⟨rfl, rfl, rfl, Matrix.toMatrix_eq_pauli i iSquare value⟩

/-- The same original quaternion has norm one exactly when its formal-imaginary matrix is special unitary. -/
private theorem quaternion_special_unitary [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (value : Proportion K) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    let matrix := Matrix.toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
      Quadratic.Pair.generator value
    Matrix2.conjugateTranspose Quadratic.Pair.conjugate matrix = Matrix2.adjugate matrix ∧
      (value.norm = 1 ↔ Matrix2.determinant matrix = 1 ∧ Matrix2.IsUnitary Quadratic.Pair.conjugate matrix) := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  exact ⟨Matrix.conjugateTranspose_toEmbeddedMatrix noRoot twoNonzero value,
    Matrix.norm_one_iff_special_unitary noRoot twoNonzero value⟩

/-- Every special-unitary matrix in the formal extension has an original ground-field norm-one quaternion preimage. -/
private theorem special_unitary_quaternion_preimage [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (matrix : Matrix2 (Quadratic.Pair K (1 : K))) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    (Matrix2.determinant matrix = 1 ∧ Matrix2.IsUnitary Quadratic.Pair.conjugate matrix) ↔
      ∃ value : Proportion K, value.norm = 1 ∧
        Matrix.toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
          Quadratic.Pair.generator value = matrix := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  exact Matrix.special_unitary_iff_unit_quaternion noRoot twoNonzero matrix

/-- The spatial imaginary-coordinate change converts the original Lorentz quadrance into Euclidean quadrance. -/
private theorem imaginary_vector_quadrance (oneNonzero : (1 : K) ≠ 0)
    (i : K) (iSquare : i ^ 2 = -1) (vector : Vector3 K) :
    (TernaryForm.lorentz oneNonzero).quadrance ⟨vector.t, i * vector.r, i * vector.s⟩ = vector.quadrance :=
  Ternary.Lorentz.quadrance_spatial_imaginary oneNonzero i iSquare vector

/-- A ground-field square root of negative one gives two-sided matrix coordinate recovery for every matrix. -/
private theorem ground_field_matrix_bijection (twoNonzero : (2 : K) ≠ 0)
    (i : K) (iSquare : i ^ 2 = -1) (value : Proportion K) (matrix : Matrix2 K) :
    Matrix.fromMatrix i (Matrix.toMatrix i value) = value ∧
      Matrix.toMatrix i (Matrix.fromMatrix i matrix) = matrix := by
  have iNonzero : i ≠ 0 := by
    intro zero
    apply one_ne_zero_of_nonzero twoNonzero
    calc
      (1 : K) = -(i ^ 2) := by rw [iSquare]; ring1
      _ = 0 := by rw [zero]; ring1
  exact ⟨Matrix.fromMatrix_toMatrix i iNonzero twoNonzero value,
    Matrix.toMatrix_fromMatrix i iNonzero twoNonzero matrix⟩

/-- After extending the quaternion coefficients, the imaginary matrix model is onto the whole target matrix algebra. -/
private theorem imaginary_scalar_extension_bijection [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (value : Proportion (Quadratic.Pair K (1 : K))) (matrix : Matrix2 (Quadratic.Pair K (1 : K))) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    Matrix.fromMatrix Quadratic.Pair.generator (Matrix.toMatrix Quadratic.Pair.generator value) = value ∧
      Matrix.toMatrix Quadratic.Pair.generator (Matrix.fromMatrix Quadratic.Pair.generator matrix) = matrix := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  exact ground_field_matrix_bijection (Quadratic.Pair.ImaginaryField.two_ne_zero twoNonzero)
    Quadratic.Pair.generator Quadratic.Pair.ImaginaryField.generator_square value matrix

/-- The split invertible-matrix bridge retains both exact quaternion and matrix round trips. -/
private theorem invertible_quaternion_round_trips
    (split : Field.Finite.Odd.Presentation.TwoSquareRepresentation (-1 : K))
    (twoNonzero : (2 : K) ≠ 0) (value : NonNullProportion K) (matrix : Matrix2.Invertible K) :
    SplitMatrix.fromInvertible split twoNonzero (SplitMatrix.toInvertible split value) = value ∧
      SplitMatrix.toInvertible split (SplitMatrix.fromInvertible split twoNonzero matrix) = matrix :=
  ⟨SplitMatrix.fromInvertible_toInvertible split twoNonzero value,
    SplitMatrix.toInvertible_fromInvertible split twoNonzero matrix⟩

/-- The split matrix action is onto Euclidean rotations, preserves products and has exactly scalar fibers. -/
private theorem split_projective_matrix_correspondence [DecidableEq K]
    (split : Field.Finite.Odd.Presentation.TwoSquareRepresentation (-1 : K))
    (twoNonzero : (2 : K) ≠ 0) (rotation : Rotation K) (left right : Matrix2.Invertible K) :
    Projective.Matrix.rotation split twoNonzero
        (Projective.Matrix.representative split twoNonzero rotation) = rotation ∧
      Projective.Matrix.rotation split twoNonzero (Matrix2.Invertible.mul left right) =
        Rotation.mul (Projective.Matrix.rotation split twoNonzero left)
          (Projective.Matrix.rotation split twoNonzero right) ∧
      (Projective.Matrix.rotation split twoNonzero left = Projective.Matrix.rotation split twoNonzero right ↔
        left.Equivalent right) :=
  ⟨Projective.Matrix.rotation_representative split twoNonzero rotation,
    Projective.Matrix.rotation_mul split twoNonzero left right,
    Projective.Matrix.rotation_eq_iff_equivalent split twoNonzero left right⟩

section FiniteMatrices

open Purelib.Geometry.Projective.Matrix

/-- The original finite quaternion charts certify the null-proportion and rotation count formulas. -/
private theorem finite_null_and_rotation_counts
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) :
    presentation.excludedProjectiveQuadricCount =
        (presentation.carrier.length + 1) * (presentation.carrier.length + 1) ∧
      presentation.rotationCount =
        presentation.carrier.length * (presentation.carrier.length * presentation.carrier.length - 1) :=
  ⟨presentation.excludedProjectiveQuadricCount_formula, presentation.rotationCount_formula⟩

/-- The original half-turn fiber is exactly the independently enumerated non-null projective-axis carrier. -/
private theorem finite_half_turn_axis_correspondence
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) (value : NonNullProportion K) :
    value ∈ presentation.halfSpreadFiber 1 ↔ value ∈ presentation.projectiveNonNullAxisRepresentatives :=
  ⟨presentation.halfTurnProjectiveAxisBijection.forward_mem value,
    presentation.halfTurnProjectiveAxisBijection.backward_mem value⟩

/-- The five-element example retains its 36 null proportions, 120 rotations, 25 half turns and six null directions. -/
private theorem finite_five_example_counts :
    FieldCounting.CountingExamples.FieldFive.presentation.excludedProjectiveQuadricCount = 36 ∧
      FieldCounting.CountingExamples.FieldFive.presentation.rotationCount = 120 ∧
      FieldCounting.CountingExamples.FieldFive.presentation.projectiveAxisRawRepresentatives.length = 31 ∧
      FieldCounting.CountingExamples.FieldFive.presentation.projectiveNonNullAxisRepresentatives.length = 25 ∧
      (FieldCounting.CountingExamples.FieldFive.presentation.halfSpreadFiber 1).length = 25 ∧
      FieldCounting.CountingExamples.FieldFive.presentation.nullDirectionRepresentatives.length = 6 ∧
      FieldCounting.CountingExamples.FieldFive.presentation.parabolicCount = 24 :=
  ⟨FieldCounting.CountingExamples.FieldFive.excluded_projective_count,
    FieldCounting.CountingExamples.FieldFive.rotation_count, by decide, by decide, by decide,
    FieldCounting.CountingExamples.FieldFive.null_direction_count,
    FieldCounting.CountingExamples.FieldFive.parabolic_count⟩

/-- The finite PGL matrix carrier has one representative per scalar class and the claimed order. -/
private theorem finite_projective_matrix_count
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) (matrix : Matrix2.Invertible K) :
    let split := SplitMatrix.finiteSplit presentation
    (Finite.representatives presentation split).Nodup ∧
      Finite.normalize presentation split matrix ∈ Finite.representatives presentation split ∧
      matrix.Equivalent (Finite.normalize presentation split matrix) ∧
      (Finite.representatives presentation split).length =
        presentation.carrier.length * (presentation.carrier.length * presentation.carrier.length - 1) :=
  ⟨Finite.representatives_nodup presentation _, Finite.normalize_mem presentation _ matrix,
    Finite.equivalent_normalize presentation _ matrix, Finite.representatives_length presentation _⟩

/-- Equal projective classes of listed finite matrices have the same retained matrix record. -/
private theorem finite_projective_matrix_uniqueness
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (split : Field.Finite.Odd.Presentation.TwoSquareRepresentation (-1 : K))
    (left right : Matrix2.Invertible K)
    (leftMember : left ∈ Finite.representatives presentation split)
    (rightMember : right ∈ Finite.representatives presentation split)
    (equivalent : left.Equivalent right) : left = right :=
  Finite.eq_of_equivalent presentation split leftMember rightMember equivalent

end FiniteMatrices

section SingularMatrices

open Purelib.Geometry.Projective.Matrix
open Purelib.Geometry.Projective.Line (Proj)

/-- The retained projective-line charts contain exactly the q-plus-one nonzero pair classes. -/
private theorem finite_projective_line_charts
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) (point : Proj K)
    (member : point ∈ Proj.finiteRepresentatives presentation) :
    (Proj.finiteRepresentatives presentation).Nodup ∧
      (Proj.finiteRepresentatives presentation).length = presentation.carrier.length + 1 ∧ point.Nonzero :=
  ⟨Proj.finiteRepresentatives_nodup presentation, Proj.finiteRepresentatives_length presentation,
    Proj.finiteRepresentatives_nonzero presentation member⟩

/-- Canonical rank-one matrix classes are nonzero, singular and counted by the two projective-line factors. -/
private theorem finite_singular_matrix_charts
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) (matrix : Matrix2 K)
    (member : matrix ∈ Finite.singularRepresentatives presentation) :
    (Finite.singularRepresentatives presentation).Nodup ∧
      (Finite.singularRepresentatives presentation).length =
        (presentation.carrier.length + 1) * (presentation.carrier.length + 1) ∧
      matrix.IsNonzero ∧ matrix.determinant = 0 :=
  ⟨Finite.singularRepresentatives_nodup presentation, Finite.singularRepresentatives_length presentation,
    Finite.singularRepresentatives_nonzero_singular presentation member⟩

/-- A facade client computes the exact finite scalar class of any original nonzero singular matrix. -/
private def finite_singular_matrix_representative
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) (matrix : Matrix2 K)
    (nonzero : matrix.IsNonzero) (singular : matrix.determinant = 0) :
    Σ' factor : K, Σ' representative : Matrix2 K, factor ≠ 0 ∧
      representative ∈ Finite.singularRepresentatives presentation ∧
      representative = Matrix2.scalarScale factor matrix :=
  Finite.singularNormalize presentation matrix nonzero singular

/-- Listed singular matrices in the same nonzero scalar class retain the same exact matrix. -/
private theorem finite_singular_matrix_uniqueness
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) (left right : Matrix2 K)
    (leftMember : left ∈ Finite.singularRepresentatives presentation)
    (rightMember : right ∈ Finite.singularRepresentatives presentation) (factor : K) (nonzero : factor ≠ 0)
    (represents : right = Matrix2.scalarScale factor left) : left = right :=
  Finite.singularRepresentatives_eq_of_scale presentation leftMember rightMember factor nonzero represents

/-- The actual five-element charts have six projective-line points and 36 nonzero singular matrix classes. -/
private theorem finite_five_singular_chart_counts :
    (Proj.finiteRepresentatives FieldCounting.CountingExamples.FieldFive.presentation).length = 6 ∧
      (Finite.singularRepresentatives
        FieldCounting.CountingExamples.FieldFive.presentation).length = 36 := by
  constructor
  · rw [Proj.finiteRepresentatives_length]
    decide
  · rw [Finite.singularRepresentatives_length]
    decide

/-- The two computed five-element line charts retain the exact reciprocal factors and canonical pairs. -/
private theorem finite_five_line_normalizations :
    let presentation := FieldCounting.CountingExamples.FieldFive.presentation
    let affine := Proj.finiteNormalize presentation ⟨2, 4⟩ (Or.inl (by decide))
    let infinity := Proj.finiteNormalize presentation ⟨0, 4⟩ (Or.inr (by decide))
    affine.1 = 3 ∧ affine.2.1 = ⟨1, 2⟩ ∧ infinity.1 = 4 ∧ infinity.2.1 = ⟨0, 1⟩ :=
  ⟨by decide, rfl, by decide, rfl⟩

end SingularMatrices

section PrescribedAxes

open Axis
open Field.Squares

/-- The Euclidean constructor retains the same root-derived scale as the shared axis parameter family. -/
private theorem euclidean_prescribed_scale (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (Prescribed.prescribedAxisSquareValue axis amount)) :
    Prescribed.prescribedAnchorScale axis amount certificate =
      Parameters.anchorScale axis.quadrance amount certificate :=
  Prescribed.prescribedAnchorScale_eq_parameters axis amount certificate

/-- The revised prescribed-axis condition reaches the complete fixed line of the original rotation. -/
private theorem prescribed_axis_geometric_existence (axis : Vector3 K) (amount : K)
    (axisNonNull : axis.quadrance ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    (∃ rotation : Rotation K, Spread.halfSpread rotation = amount ∧
      ∀ vector : Vector3 K, Matrix3.rowMul vector rotation.matrix = vector ↔
        ∃ factor : K, vector = Vector3.scale factor axis) ↔
      Nonempty (Witness.NonzeroSquare (Prescribed.prescribedAxisSquareValue axis amount)) :=
  Prescribed.prescribedAxis_fixedLine_exists_iff axis amount axisNonNull amountNonzero amountNotOne twoNonzero

/-- The same retained root gives the alternative condition involving the full spread. -/
private theorem prescribed_axis_spread_condition (axis : Vector3 K) (amount : K)
    (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (Witness.NonzeroSquare (Prescribed.prescribedAxisSquareValue axis amount)) ↔
      Nonempty (Witness.NonzeroSquare (axis.quadrance * (4 * amount * (1 - amount)))) :=
  Prescribed.prescribedAxis_square_iff_spreadSquare axis amount twoNonzero

/-- Every retained candidate has one of the two distinct inverse matrices computed from the original root. -/
private theorem prescribed_axis_exact_pair [DecidableEq K] (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (Prescribed.prescribedAxisSquareValue axis amount))
    (axisNonNull : axis.quadrance ≠ 0) (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0)
    (candidate : Prescribed.PrescribedAxisRotation axis amount) :
    let positive := Prescribed.prescribedAxisRotationOfSquare axis amount certificate
      axisNonNull amountNotOne twoNonzero
    let negative := Prescribed.prescribedAxisRotationOfSquare axis amount certificate.neg
      axisNonNull amountNotOne twoNonzero
    positive.rotation.matrix ≠ negative.rotation.matrix ∧
      Matrix3.mul positive.rotation.matrix negative.rotation.matrix = Matrix3.identity ∧
      Matrix3.mul negative.rotation.matrix positive.rotation.matrix = Matrix3.identity ∧
      (candidate.rotation.matrix = positive.rotation.matrix ∨ candidate.rotation.matrix = negative.rotation.matrix) :=
  ⟨Prescribed.prescribedAxisRotation_pair_distinct axis amount certificate axisNonNull amountNotOne twoNonzero,
    (Prescribed.prescribedAxisRotation_pair_inverse axis amount certificate axisNonNull amountNotOne twoNonzero).1,
    (Prescribed.prescribedAxisRotation_pair_inverse axis amount certificate axisNonNull amountNotOne twoNonzero).2,
    candidate.matrix_eq_pair certificate axisNonNull amountNotOne twoNonzero⟩

/-- The two matrices have opposite handedness about the same retained anchor and perpendicular transversal. -/
private theorem prescribed_axis_opposite_handedness (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (Prescribed.prescribedAxisSquareValue axis amount))
    (axisNonNull : axis.quadrance ≠ 0) (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0)
    (transversal : Vector3 K)
    (perpendicular : transversal.Perpendicular
      (Vector3.scale (Prescribed.prescribedAnchorScale axis amount certificate) axis)) :
    Orientation.Handedness.handednessDet
        (Vector3.scale (Prescribed.prescribedAnchorScale axis amount certificate) axis) transversal
        (Prescribed.prescribedAxisRotationOfSquare axis amount certificate.neg
          axisNonNull amountNotOne twoNonzero).rotation.matrix =
      -Orientation.Handedness.handednessDet
        (Vector3.scale (Prescribed.prescribedAnchorScale axis amount certificate) axis) transversal
        (Prescribed.prescribedAxisRotationOfSquare axis amount certificate
          axisNonNull amountNotOne twoNonzero).rotation.matrix :=
  Prescribed.prescribedAxisRotation_pair_oppositeHandedness axis amount certificate
    axisNonNull amountNotOne twoNonzero transversal perpendicular

/-- Half spread one retains the original half turn and is independent of the nonzero axis scale. -/
private theorem prescribed_axis_half_turn (axis : Vector3 K) (axisNonNull : axis.quadrance ≠ 0)
    (factor : K) (factorNonzero : factor ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Reflection.halfTurnRotation axis axisNonNull) = 1 ∧
      (Reflection.halfTurnRotation (Vector3.scale factor axis)
        (Vector3.quadrance_scale_ne_zero factor axis factorNonzero axisNonNull)).matrix =
        (Reflection.halfTurnRotation axis axisNonNull).matrix :=
  ⟨Prescribed.prescribedAxis_halfTurn_halfSpread axis axisNonNull twoNonzero,
    Prescribed.prescribedAxis_halfTurn_unique axis axisNonNull factor factorNonzero⟩

/-- Half spread zero gives exactly the identity when the only null vector is zero. -/
private theorem prescribed_axis_zero_endpoint (separation : NullVectors.SumSquaresSeparate K)
    (rotation : Rotation K) (amountZero : Spread.halfSpread rotation = 0) (twoNonzero : (2 : K) ≠ 0) :
    rotation.matrix = Matrix3.identity :=
  Prescribed.rotation_eq_identity_of_halfSpread_zero separation rotation amountZero twoNonzero

/-- The revised coordinate-axis amounts are exactly the retained rational square parametrization. -/
private theorem coordinate_axis_parameter_exhaustive (amount : Rational)
    (amountNonzero : amount ≠ 0) (amountNotOne : amount ≠ 1) :
    Nonempty (Witness.NonzeroSquare
      (Prescribed.prescribedAxisSquareValue PrescribedAxes.ExampleSixtySix.coordinateAxis amount)) ↔
      ∃ parameter : Rational, parameter ≠ 0 ∧ 1 + parameter ^ 2 ≠ 0 ∧
        amount = PrescribedAxes.ExampleSixtySix.parameterHalfSpread parameter :=
  PrescribedAxes.ExampleSixtySix.coordinateAxis_condition_iff_parameter amount amountNonzero amountNotOne

/-- The same coordinate-axis parameter gives the square root, cosine coefficient and normalized Pythagorean triple. -/
private theorem coordinate_axis_pythagorean_parameter (parameter : Rational)
    (defined : 1 + parameter ^ 2 ≠ 0) :
    Prescribed.prescribedAxisSquareValue PrescribedAxes.ExampleSixtySix.coordinateAxis
        (PrescribedAxes.ExampleSixtySix.parameterHalfSpread parameter) =
      PrescribedAxes.ExampleSixtySix.parameterConditionRoot parameter ^ 2 ∧
      1 - 2 * PrescribedAxes.ExampleSixtySix.parameterHalfSpread parameter =
        (1 - parameter ^ 2) / (1 + parameter ^ 2) ∧
      ((1 - parameter ^ 2) / (1 + parameter ^ 2)) ^ 2 +
        ((2 * parameter) / (1 + parameter ^ 2)) ^ 2 = 1 ∧
      PrescribedAxes.ExampleSixtySix.parameterHalfSpread 1 = (1 : Rational) / 2 ∧
      PrescribedAxes.ExampleSixtySix.parameterHalfSpread ((1 : Rational) / 2) = (1 : Rational) / 5 :=
  ⟨PrescribedAxes.ExampleSixtySix.parameter_condition parameter defined,
    PrescribedAxes.ExampleSixtySix.parameter_one_sub_two_halfSpread parameter defined,
    PrescribedAxes.ExampleSixtySix.parameter_pythagorean parameter defined,
    PrescribedAxes.ExampleSixtySix.quarterTurn_parameter, PrescribedAxes.ExampleSixtySix.threeFourFive_parameter⟩

/-- The diagonal axis forbids a quarter turn but retains the three-quarter cap with its original root and half twist. -/
private theorem diagonal_axis_amounts :
    Prescribed.prescribedAxisSquareValue PrescribedAxes.ExampleSixtySeven.diagonalAxis
        ((1 : Rational) / 2) = 3 / 4 ∧
      ¬ Nonempty (Prescribed.PrescribedAxisRotation PrescribedAxes.ExampleSixtySeven.diagonalAxis
        ((1 : Rational) / 2)) ∧
      Prescribed.prescribedAxisSquareValue PrescribedAxes.ExampleSixtySeven.diagonalAxis
        ((3 : Rational) / 4) = 9 / 16 ∧
      PrescribedAxes.ExampleSixtySeven.threeQuarterCertificate.root = (3 : Rational) / 4 ∧
      Spread.halfSpread PrescribedAxes.ExampleSixtySeven.diagonalRotation = (3 : Rational) / 4 ∧
      PrescribedAxes.ExampleSixtySeven.diagonalAxis.quadrance = 3 ∧
      (Prescribed.prescribedAxisRotationOfSquare PrescribedAxes.ExampleSixtySeven.diagonalAxis
        ((3 : Rational) / 4) PrescribedAxes.ExampleSixtySeven.threeQuarterCertificate
        PrescribedAxes.ExampleSixtySeven.diagonalAxis_nonNull (by decide) (by decide)).rotation.matrix =
        PrescribedAxes.ExampleSixtySeven.diagonalRotation.matrix :=
  ⟨PrescribedAxes.ExampleSixtySeven.quarter_condition_value,
    PrescribedAxes.ExampleSixtySeven.no_rational_quarter_turn,
    PrescribedAxes.ExampleSixtySeven.threeQuarter_condition_value, rfl,
    PrescribedAxes.ExampleSixtySeven.diagonalRotation_halfSpread,
    PrescribedAxes.ExampleSixtySeven.diagonalRotation_halfTwist,
    PrescribedAxes.ExampleSixtySeven.constructed_threeQuarter_eq_diagonalRotation⟩

end PrescribedAxes

section QuadranceClasses

open Field.SquareClass.Basic (SquareClassRepresentative)
open Purelib.Algebra.Quaternion.Projective
open Purelib.Algebra.Quaternion.Projective.Rational
open Purelib.NumberTheory
open Purelib.NumberTheory.SquareClass.Rational.Basic.TheoremSixtyTwo (PositiveSquareClassRepresentative)
open Purelib.Geometry.Rotations.Rational.Kernel

/-- The rotation invariant agrees with the retained norm class of every original matrix representative. -/
private theorem quadrance_class_independent [DecidableEq K] (rotation : Rotation K)
    (proportion : NonNullProportion K) (twoNonzero : (2 : K) ≠ 0)
    (represents : Action.NonNullProportion.rotationMatrix proportion = rotation.matrix) :
    (SquareClass.RotationQuadranceClass.ofRotation rotation twoNonzero).Equivalent
      (Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass proportion) :=
  SquareClass.RotationQuadranceClass.ofRotation_equivalent_representative rotation proportion twoNonzero represents

/-- The original stored-rotation invariant is multiplicative through the revised facade. -/
private theorem quadrance_class_homomorphism [DecidableEq K] (left right : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    (SquareClass.RotationQuadranceClass.ofRotation (Product.rotationProduct left right) twoNonzero).Equivalent
      (SquareClassRepresentative.mul (SquareClass.RotationQuadranceClass.ofRotation left twoNonzero)
        (SquareClass.RotationQuadranceClass.ofRotation right twoNonzero)) :=
  SquareClass.RotationQuadranceClass.of_rotationProduct left right twoNonzero

/-- The non-half-turn and half-turn closed forms refer to the original rotation and original non-null axis. -/
private theorem quadrance_class_closed_forms [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (axis : Vector3 K) (axisNonNull : axis.quadrance ≠ 0) :
    (SquareClass.RotationQuadranceClass.ofRotation rotation twoNonzero).Equivalent
        ⟨1 - Spread.halfSpread rotation, Field.ExplicitField.one_sub_ne_zero_of_ne_one notHalfTurn⟩ ∧
      (SquareClass.RotationQuadranceClass.ofRotation (Reflection.halfTurnRotation axis axisNonNull)
        twoNonzero).Equivalent ⟨axis.quadrance, axisNonNull⟩ :=
  ⟨SquareClass.RotationQuadranceClass.ofRotation_one_sub_halfSpread rotation twoNonzero notHalfTurn,
    SquareClass.RotationQuadranceClass.ofRotation_halfTurn axis axisNonNull twoNonzero⟩

/-- The revised spinor-norm formula covers every original reflection product, including perpendicular normals. -/
private theorem reflection_product_spinor_norm [DecidableEq K] (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (SquareClass.RotationQuadranceClass.ofRotation
      (Reflection.reflectionProductRotation first second firstNonNull secondNonNull) twoNonzero).Equivalent
        ⟨first.quadrance * second.quadrance, Field.ExplicitField.mul_ne_zero firstNonNull secondNonNull⟩ :=
  SquareClass.RotationQuadranceClass.ofRotation_reflectionProduct
    first second firstNonNull secondNonNull twoNonzero

/-- Every positive rational target has an original rotation preimage with the same retained square class. -/
private def positive_rotation_class_preimage (target : PositiveSquareClassRepresentative) :
    Σ' rotation : Rotation Rational,
      (SquareClass.RotationQuadranceClass.ofRotation rotation (by decide)).Equivalent target.representative := by
  let algorithm := FourSquares.Rational.TheoremSixtyTwo.lagrangeAlgorithm
  let proportion := Surjectivity.TheoremSixtyTwo.preimage algorithm target
  refine ⟨Action.NonNullProportion.rotation proportion, ?_⟩
  have classes := SquareClass.RotationQuadranceClass.ofRotation_equivalent_representative
    (Action.NonNullProportion.rotation proportion) proportion (by decide) rfl
  apply SquareClassRepresentative.equivalent_trans classes
  refine ⟨1, target.representative.one_ne_zero, ?_⟩
  have realizes := Surjectivity.TheoremSixtyTwo.preimage_quadranceClass algorithm target
  change proportion.toProportion.norm = target.representative.value at realizes
  change target.representative.value = 1 ^ 2 * proportion.toProportion.norm
  rw [realizes, one_pow, one_mul]

/-- The rational norm-class image contains exactly the positive representatives. -/
private theorem rational_class_image_positive (target : SquareClassRepresentative Rational) :
    Surjectivity.TheoremSixtyTwo.InQuadranceClassImage target ↔ 0 < target.value :=
  Surjectivity.TheoremSixtyTwo.quadranceClassImage_iff_positive target

/-- Arbitrary finite requests retain distinct positive target classes and their exact quaternion preimages. -/
private def distinct_positive_class_pack (count : Nat) : Packs.SquareClassPacks.DistinctPositiveSquareClassPack count :=
  Packs.SquareClassPacks.distinctPositiveSquareClassPack count

/-- The requested positive-class pack has exact length and pairwise inequivalent retained target classes. -/
private theorem distinct_positive_class_pack_certificates (count : Nat) :
    (Packs.SquareClassPacks.distinctPositiveSquareClassPack count).entries.length = count ∧
      (Packs.SquareClassPacks.distinctPositiveSquareClassPack count).entries.Pairwise
        (fun left right => ¬ left.target.representative.Equivalent right.target.representative) :=
  ⟨(Packs.SquareClassPacks.distinctPositiveSquareClassPack count).length_eq,
    (Packs.SquareClassPacks.distinctPositiveSquareClassPack count).pairwiseInequivalent⟩

/-- Unit normalization uses the original proportion and retained factor and preserves its actual matrix. -/
private theorem certified_unit_quaternion (proportion : NonNullProportion K)
    (certificate : UnitObstruction.NonNullProportion.UnitRepresentativeCertificate proportion) :
    certificate.unitProportion.toProportion.norm = 1 ∧
      Action.NonNullProportion.rotationMatrix certificate.unitProportion =
        Action.NonNullProportion.rotationMatrix proportion :=
  ⟨certificate.unitProportion_normOne, certificate.rotationMatrix_unitProportion⟩

/-- The stored unit predicate is equivalent to an actual unit-norm preimage and to a trivial retained rotation class. -/
private theorem unit_quaternion_obstruction [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    (UnitObstruction.RotationQuadranceClass.HasUnitQuaternion rotation twoNonzero ↔
      ∃ value : NonNullProportion K, Action.NonNullProportion.rotation value = rotation ∧
        value.toProportion.norm = 1) ∧
      (UnitObstruction.RotationQuadranceClass.HasUnitQuaternion rotation twoNonzero ↔
        (SquareClass.RotationQuadranceClass.ofRotation rotation twoNonzero).Equivalent
          ⟨1, one_ne_zero_of_nonzero twoNonzero⟩) :=
  ⟨UnitObstruction.RotationQuadranceClass.hasUnitQuaternion_iff_unitPreimage rotation twoNonzero,
    UnitObstruction.RotationQuadranceClass.hasUnitQuaternion_iff_trivial rotation twoNonzero⟩

/-- Both revised square-root criteria refer to the same original unit-quaternion predicate. -/
private theorem unit_quaternion_square_criteria [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (axis : Vector3 K) (axisNonNull : axis.quadrance ≠ 0) :
    (UnitObstruction.RotationQuadranceClass.HasUnitQuaternion rotation twoNonzero ↔
      ∃ root : K, root ^ 2 = 1 - Spread.halfSpread rotation) ∧
      (UnitObstruction.RotationQuadranceClass.HasUnitQuaternion (Reflection.halfTurnRotation axis axisNonNull)
        twoNonzero ↔ ∃ root : K, root ^ 2 = axis.quadrance) :=
  ⟨UnitObstruction.RotationQuadranceClass.hasUnitQuaternion_iff_complement_square rotation twoNonzero notHalfTurn,
    UnitObstruction.RotationQuadranceClass.hasUnitQuaternion_halfTurn_iff_axis_square axis axisNonNull twoNonzero⟩

/-- The original unit-representative kernel retains identity, product and conjugate-inverse closure. -/
private theorem unit_quaternion_kernel_laws (witness : NonNullProportion K) :
    UnitObstruction.UnitQuaternionKernel.Laws witness := UnitObstruction.UnitQuaternionKernel.laws witness

/-- Arbitrary index requests return the original finite pack of pairwise separated unit-kernel cosets. -/
private def unit_kernel_coset_pack (count : Nat) : CosetPacks.KernelCosetPacks.SeparatedKernelCosetPack count :=
  CosetPacks.KernelCosetPacks.separatedKernelCosetPack count

/-- The retained coset pack has the requested size and its original relative-product separation relation. -/
private theorem unit_kernel_coset_pack_certificates (count : Nat) :
    (CosetPacks.KernelCosetPacks.separatedKernelCosetPack count).entries.length = count ∧
      (CosetPacks.KernelCosetPacks.separatedKernelCosetPack count).entries.Pairwise
        (fun left right => ¬ CosetPacks.KernelCosetPacks.SameUnitKernelCoset left.proportion right.proportion) :=
  ⟨(CosetPacks.KernelCosetPacks.separatedKernelCosetPack count).length_eq,
    (CosetPacks.KernelCosetPacks.separatedKernelCosetPack count).pairwiseSeparated⟩

/-- Both revised coordinate-axis examples retain their actual matrix, half spread and nonsquare norm class. -/
private theorem rational_unit_obstruction_examples :
    Action.NonNullProportion.rotationMatrix QuaternionObstruction.ExampleSixtyFour.quarterTurn =
        QuaternionObstruction.ExampleSixtyFour.quarterTurnDisplayed ∧
      Spread.halfSpread (Action.NonNullProportion.rotation QuaternionObstruction.ExampleSixtyFour.quarterTurn) =
        (1 : Rational) / 2 ∧
      (Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass
        QuaternionObstruction.ExampleSixtyFour.quarterTurn).value = 2 ∧
      Action.NonNullProportion.rotationMatrix QuaternionObstruction.ExampleSixtyFour.threeFourFive =
        QuaternionObstruction.ExampleSixtyFour.threeFourFiveDisplayed ∧
      Spread.halfSpread (Action.NonNullProportion.rotation QuaternionObstruction.ExampleSixtyFour.threeFourFive) =
        (1 : Rational) / 5 ∧
      (Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass
        QuaternionObstruction.ExampleSixtyFour.threeFourFive).value = 5 :=
  ⟨QuaternionObstruction.ExampleSixtyFour.quarterTurn_matrix,
    QuaternionObstruction.ExampleSixtyFour.quarterTurn_halfSpread,
    QuaternionObstruction.ExampleSixtyFour.quarterTurn_class,
    QuaternionObstruction.ExampleSixtyFour.threeFourFive_matrix,
    QuaternionObstruction.ExampleSixtyFour.threeFourFive_halfSpread,
    QuaternionObstruction.ExampleSixtyFour.threeFourFive_class⟩

/-- Neither original rational example rotation admits any unit-norm quaternion preimage. -/
private theorem rational_examples_no_unit_quaternion :
    ¬ UnitObstruction.RotationQuadranceClass.HasUnitQuaternion
        (Action.NonNullProportion.rotation QuaternionObstruction.ExampleSixtyFour.quarterTurn) (by decide) ∧
      ¬ UnitObstruction.RotationQuadranceClass.HasUnitQuaternion
        (Action.NonNullProportion.rotation QuaternionObstruction.ExampleSixtyFour.threeFourFive) (by decide) := by
  constructor
  · intro unit
    exact QuaternionObstruction.ExampleSixtyFour.quarterTurn_no_unit_quaternion
      ((UnitObstruction.RotationQuadranceClass.hasUnitQuaternion_rotation_iff
        QuaternionObstruction.ExampleSixtyFour.quarterTurn (by decide)).mp unit)
  · intro unit
    exact QuaternionObstruction.ExampleSixtyFour.threeFourFive_no_unit_quaternion
      ((UnitObstruction.RotationQuadranceClass.hasUnitQuaternion_rotation_iff
        QuaternionObstruction.ExampleSixtyFour.threeFourFive (by decide)).mp unit)

end QuadranceClasses

namespace RayCover

/-- The retained Euclidean ray operations supply exact associativity and both positive conjugate-inverse laws. -/
private theorem euclidean_ray_group {F : Type*} [RayOrderedExplicitField F] (first second third : RayProportion F) :
    RayProportion.mul (RayProportion.mul first second) third =
        RayProportion.mul first (RayProportion.mul second third) ∧
      (RayProportion.mul first first.conjugate).Equivalent RayProportion.identity ∧
      (RayProportion.mul first.conjugate first).Equivalent RayProportion.identity ∧
      0 < first.toNonNullProportion.toProportion.norm :=
  ⟨RayProportion.mul_assoc first second third, RayProportion.mul_conjugate_equivalent_identity first,
    RayProportion.conjugate_mul_equivalent_identity first, first.norm_positive⟩

/-- The retained Euclidean ray action covers every original rotation with exactly two distinct opposite rays. -/
private theorem euclidean_ray_cover {F : Type*} [RayOrderedExplicitField F]
    (rotation : Rotation F) (left right : RayProportion F) :
    (∃ ray : RayProportion F, ray.rotation.matrix = rotation.matrix) ∧
      (left.rotation.matrix = right.rotation.matrix ↔ left.Equivalent right ∨ left.neg.Equivalent right) ∧
      left.neg.rotation.matrix = left.rotation.matrix ∧ ¬ left.Equivalent left.neg ∧
      (RayProportion.mul left right).rotation.matrix = Matrix3.mul left.rotation.matrix right.rotation.matrix :=
  ⟨RayProportion.rotation_surjective rotation,
    RayProportion.rotation_eq_iff_equivalent_or_neg_equivalent left right,
    (RayProportion.rotation_fiber_has_two_distinct_rays left).1,
    (RayProportion.rotation_fiber_has_two_distinct_rays left).2, RayProportion.rotation_mul left right⟩

/-- The Euclidean ray kernel consists exactly of the retained positive and negative scalar identity rays. -/
private theorem euclidean_ray_kernel {F : Type*} [RayOrderedExplicitField F] (ray : RayProportion F) :
    ray.rotation.matrix = Matrix3.identity ↔
      RayProportion.identity.Equivalent ray ∨ RayProportion.negativeIdentity.Equivalent ray := by
  constructor
  · intro acts
    exact (RayProportion.rotation_eq_iff_equivalent_or_neg_equivalent RayProportion.identity ray).mp
      (RayProportion.identity_rotation_matrix.trans acts.symm)
  · intro rays
    have same := (RayProportion.rotation_eq_iff_equivalent_or_neg_equivalent RayProportion.identity ray).mpr rays
    exact same.symm.trans RayProportion.identity_rotation_matrix

end RayCover

namespace AnchorRays

/-- The same original Euclidean anchor vector and its inverse readback lie on distinct positive rays. -/
private theorem inverse_anchor_distinct {F : Type*} [RayOrderedExplicitField F]
    (rotation : Rotation F) (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (anchorNonzero : Axis.Recovery.rotationAnchorVector rotation notHalfTurn ≠ Vector3.zero) :
    ¬ Vector3.RayEquivalent (Axis.Recovery.rotationAnchorVector rotation notHalfTurn)
      (Axis.Recovery.rotationAnchorVector (Orientation.Handedness.inverseRotation rotation)
        (Orientation.Handedness.inverseRotation_notHalfTurn rotation notHalfTurn)) :=
  Orientation.Handedness.rotationAnchorVector_inverse_distinct_ray rotation notHalfTurn
    RayOrderedExplicitField.two_ne_zero anchorNonzero

end AnchorRays

namespace Splitting

/-- The original ordered Euclidean rotation has negative reciprocal discriminant and only the field eigenvalue one. -/
private theorem ordered_rotation_elliptic {F : Type*} [RayOrderedExplicitField F]
    (rotation : Rotation F) (law : OrderDifferenceLaw F)
    (positive : 0 < Spread.halfSpread rotation) (belowOne : Spread.halfSpread rotation < 1)
    (point : F) (witness : Matrix3.RowEigenvector rotation.matrix point) :
    Reciprocal.discriminant (1 - 2 * Spread.halfSpread rotation) < 0 ∧ point = 1 :=
  ⟨Reciprocal.discriminant_halfSpread_negative law (Spread.halfSpread rotation) positive belowOne,
    rotation.eigenvalue_eq_one_of_halfSpread_unit_interval law positive belowOne point witness⟩

/-- The rational source specialization uses the retained rational comparison and the original matrix's eigenvector. -/
private theorem rational_rotation_elliptic (rotation : Rotation Rational)
    (positive : 0 < Spread.halfSpread rotation) (belowOne : Spread.halfSpread rotation < 1)
    (point : Rational) (witness : Matrix3.RowEigenvector rotation.matrix point) : point = 1 :=
  rotation.eigenvalue_eq_one_of_halfSpread_unit_interval
    lt_iff_zero_lt_sub positive belowOne point witness

/-- The rational elliptic sentence follows for every original nonidentity rotation away from half turns. -/
private theorem rational_nonidentity_rotation_elliptic (rotation : Rotation Rational)
    (notIdentity : rotation.matrix ≠ Matrix3.identity) (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (point : Rational) (witness : Matrix3.RowEigenvector rotation.matrix point) :
    0 < Spread.halfSpread rotation ∧ Spread.halfSpread rotation < 1 ∧ point = 1 :=
  ⟨(rotation.halfSpread_unit_interval_of_nonidentity_notHalfTurn lt_iff_zero_lt_sub notIdentity notHalfTurn).1,
    (rotation.halfSpread_unit_interval_of_nonidentity_notHalfTurn lt_iff_zero_lt_sub notIdentity notHalfTurn).2,
    rotation.eigenvalue_eq_one_of_nonidentity_notHalfTurn lt_iff_zero_lt_sub notIdentity notHalfTurn point witness⟩

end Splitting

section FiniteUnitImage

open scoped Purelib.Data.Nat

/-- The original norm-one quaternion image is exactly the determinant-one split-matrix image. -/
private theorem finite_unit_matrix_image
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) (target : Rotation K) :
    let split := SplitMatrix.finiteSplit presentation
    (∃ value : NonNullProportion K, Action.NonNullProportion.rotation value = target ∧ value.toProportion.norm = 1) ↔
      ∃ matrix : Matrix2.Invertible K, Projective.Matrix.rotation split presentation.twoNonzero matrix = target ∧
        matrix.matrix.determinant = 1 :=
  Projective.Matrix.unitPreimage_iff_determinant_one _ presentation.twoNonzero target

/-- Twice the original finite norm-one projective kernel length is the complete original rotation count. -/
private theorem finite_unit_kernel_index_two
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) :
    presentation.quadranceClassKernel.length + presentation.quadranceClassKernel.length =
      presentation.rotationCount :=
  presentation.quadranceClassKernel_twice_eq_rotationCount

/-- The original finite determinant-one projective image has the exact half-group-order count. -/
private theorem finite_unit_kernel_count
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) :
    presentation.quadranceClassKernel.length =
      (presentation.carrier.length * (presentation.carrier.length * presentation.carrier.length - 1)) / 2 := by
  calc
    _ = presentation.quadranceClassKernelCount := presentation.quadranceClassKernelCount_eq_length.symm
    _ = _ := presentation.quadranceClassKernelCount_formula

end FiniteUnitImage

section FiniteAxisAmounts

open scoped Purelib.Data.Nat

/-- The original nonendpoint amount list has the exact count determined by the original negative-quadrance roots. -/
private theorem finite_axis_amount_count
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (quadrance : K) (quadranceNonzero : quadrance ≠ 0) :
    (Axis.Parameters.admissibleAmounts presentation quadrance).length =
      (presentation.carrier.length - (presentation.squareRootCount (-quadrance) + 1)) / 2 :=
  Axis.Parameters.admissibleAmounts_length presentation quadrance quadranceNonzero

/-- A square negative axis quadrance gives the source's square-character-one count. -/
private theorem finite_axis_square_amount_count
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (quadrance root : K) (quadranceNonzero : quadrance ≠ 0) (square : root ^ 2 = -quadrance) :
    (Axis.Parameters.admissibleAmounts presentation quadrance).length = (presentation.carrier.length - 3) / 2 :=
  Axis.Parameters.admissibleAmounts_length_of_square presentation quadrance root quadranceNonzero square

/-- A nonsquare negative axis quadrance gives the source's square-character-minus-one count. -/
private theorem finite_axis_nonsquare_amount_count
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (quadrance : K) (quadranceNonzero : quadrance ≠ 0) (noRoot : ∀ root : K, root ^ 2 ≠ -quadrance) :
    (Axis.Parameters.admissibleAmounts presentation quadrance).length = (presentation.carrier.length - 1) / 2 :=
  Axis.Parameters.admissibleAmounts_length_of_nonsquare presentation quadrance quadranceNonzero noRoot

/-- The enumerated amount retains the original finite field's cached square root as its exact certificate root. -/
private theorem finite_axis_amount_cached_root
    (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (quadrance amount : K) (quadranceNonzero : quadrance ≠ 0)
    (member : amount ∈ Axis.Parameters.admissibleAmounts presentation quadrance) :
    (Axis.Parameters.amountCertificate presentation quadrance amount quadranceNonzero member).root =
      presentation.squareRoot (Axis.Parameters.squareValue quadrance amount) := rfl

/-- The original three-element carrier gives one coordinate-axis amount and no diagonal-plane-axis amount. -/
private theorem finite_three_axis_amount_lists :
    Axis.Parameters.admissibleAmounts FieldCounting.CountingExamples.FieldThree.presentation 1 = [2] ∧
      Axis.Parameters.admissibleAmounts FieldCounting.CountingExamples.FieldThree.presentation 2 = [] := by
  decide

/-- The original five-element carrier gives one coordinate-axis amount and two diagonal-plane-axis amounts. -/
private theorem finite_five_axis_amount_lists :
    Axis.Parameters.admissibleAmounts FieldCounting.CountingExamples.FieldFive.presentation 1 = [3] ∧
      Axis.Parameters.admissibleAmounts FieldCounting.CountingExamples.FieldFive.presentation 2 = [2, 4] := by
  decide

end FiniteAxisAmounts

end Test.Geometry.Rotations.EuclideanPublication
