module

public import Purelib.Geometry.Rotations.Ternary.Lorentz.Cayley
public import Purelib.Algebra.Field.ExplicitOrder.Sign
import Purelib.Geometry.Rotations.Ternary.Cayley
import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.Geometry.Rotations.Ternary.Clifford
import Purelib.Geometry.Rotations.Ternary.Reflection
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Geometry.Quadratic.Ternary.Lorentz
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Composition of time-first Lorentz anchors

The source anchor product subtracts the signed Lorentz cross product.
Negating both input vectors converts it to the original form-indexed
Clifford product. Its cap law retains the same certified rotations.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField)
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- The affine Lorentz product denominator is one minus the original pairing. -/
@[expose] def anchorProductDenominator (left right : Vector3 K) : K :=
  1 - (Form.lorentz oneNonzero).bilinear left right

/-- The Lorentz product numerator subtracts the paper's signed cross product. -/
@[expose] def anchorProductNumerator (left right : Vector3 K) : Vector3 K :=
  Vector3.sub (Vector3.add left right) (Quadratic.Ternary.Lorentz.cross oneNonzero left right)

/-- The affine Lorentz anchor product retains its supplied nonzero denominator. -/
@[expose] def anchorProduct (left right : Vector3 K)
    (_defined : anchorProductDenominator oneNonzero left right ≠ 0) : Vector3 K :=
  Vector3.scale (anchorProductDenominator oneNonzero left right)⁻¹
    (anchorProductNumerator oneNonzero left right)

/-- Reversing the source anchor order preserves the affine product denominator. -/
theorem anchorProductDenominator_comm (left right : Vector3 K) :
    anchorProductDenominator oneNonzero right left = anchorProductDenominator oneNonzero left right := by
  unfold anchorProductDenominator
  rw [Form.bilinear_comm]

/-- Reversing the source anchor order adds the original signed cross product to the numerator. -/
theorem anchorProductNumerator_reverse (left right : Vector3 K) :
    anchorProductNumerator oneNonzero right left =
      Vector3.add (Vector3.add left right) (Quadratic.Ternary.Lorentz.cross oneNonzero left right) := by
  unfold anchorProductNumerator
  rw [Quadratic.Ternary.Lorentz.cross_anticomm]
  ext <;> unfold Vector3.add Vector3.sub Vector3.neg <;> ring1

/-- The opposite Lorentz anchor product uses the same denominator and the positive signed cross term. -/
theorem anchorProduct_reverse (left right : Vector3 K)
    (defined : anchorProductDenominator oneNonzero left right ≠ 0) :
    anchorProduct oneNonzero right left (by rw [anchorProductDenominator_comm]; exact defined) =
      Vector3.scale (anchorProductDenominator oneNonzero left right)⁻¹
        (Vector3.add (Vector3.add left right) (Quadratic.Ternary.Lorentz.cross oneNonzero left right)) := by
  unfold anchorProduct
  rw [anchorProductDenominator_comm, anchorProductNumerator_reverse]

/-- The Lorentz product exists exactly when the original pairing is different from one. -/
theorem anchorProductDenominator_ne_zero_iff (left right : Vector3 K) :
    anchorProductDenominator oneNonzero left right ≠ 0 ↔
      (Form.lorentz oneNonzero).bilinear left right ≠ 1 := by
  constructor
  · intro defined pairingOne
    apply defined
    unfold anchorProductDenominator
    rw [pairingOne]
    ring1
  · intro notOne denominatorZero
    apply notOne
    calc
      _ = 1 - anchorProductDenominator oneNonzero left right := by unfold anchorProductDenominator; ring1
      _ = 1 := by rw [denominatorZero]; ring1

/-- Negating both source anchors preserves their generic Clifford product denominator. -/
theorem anchorProductDenominator_neg (left right : Vector3 K) :
    Cayley.TernaryForm.anchorProductDenominator (Form.lorentz oneNonzero)
        (Vector3.neg left) (Vector3.neg right) = anchorProductDenominator oneNonzero left right := by
  unfold Cayley.TernaryForm.anchorProductDenominator anchorProductDenominator
  rw [Form.lorentz_determinant, Form.bilinear_neg_left, Form.bilinear_neg_right]
  ring1

/-- Negating both source anchors negates their Lorentz product numerator. -/
theorem anchorProductNumerator_neg (left right : Vector3 K) :
    Cayley.TernaryForm.anchorProductNumerator (Form.lorentz oneNonzero)
        (Vector3.neg left) (Vector3.neg right) =
      Vector3.neg (anchorProductNumerator oneNonzero left right) := by
  unfold Cayley.TernaryForm.anchorProductNumerator
  rw [Form.cliffordCross_neg_left, Form.cliffordCross_neg_right, Vector3.neg_neg]
  unfold anchorProductNumerator Quadratic.Ternary.Lorentz.cross
  ext <;> unfold Vector3.sub Vector3.add Vector3.neg <;> ring1

/-- The source anchor product converts to the original generic product by a single vector negation. -/
theorem anchorProduct_neg (left right : Vector3 K)
    (defined : anchorProductDenominator oneNonzero left right ≠ 0) :
    Cayley.TernaryForm.anchorProduct (Form.lorentz oneNonzero) (Vector3.neg left) (Vector3.neg right)
        (by rw [anchorProductDenominator_neg]; exact defined) =
      Vector3.neg (anchorProduct oneNonzero left right defined) := by
  unfold Cayley.TernaryForm.anchorProduct anchorProduct
  rw [anchorProductDenominator_neg, anchorProductNumerator_neg]
  ext <;> unfold Vector3.scale Vector3.neg <;> ring1

/-- The denominator square plus numerator quadrance is the product of the input cap denominators.

This identity remains valid at a zero product denominator, where the
numerator describes the half-turn direction rather than an affine anchor.
-/
theorem quadrance_anchorProductNumerator (left right : Vector3 K) :
    anchorProductDenominator oneNonzero left right ^ 2 +
      (Form.lorentz oneNonzero).quadrance (anchorProductNumerator oneNonzero left right) =
        capDenominator oneNonzero left * capDenominator oneNonzero right := by
  unfold anchorProductDenominator anchorProductNumerator capDenominator
  rw [Form.quadrance_lorentz, Form.bilinear_lorentz, Form.quadrance_lorentz,
    Form.quadrance_lorentz, Quadratic.Ternary.Lorentz.cross_coordinates]
  unfold Vector3.sub Vector3.add
  ring1

/-- The normalized Lorentz product has the exact quotient of the original cap denominators. -/
theorem capDenominator_anchorProduct (left right : Vector3 K)
    (defined : anchorProductDenominator oneNonzero left right ≠ 0) :
    capDenominator oneNonzero (anchorProduct oneNonzero left right defined) =
      capDenominator oneNonzero left * capDenominator oneNonzero right /
        anchorProductDenominator oneNonzero left right ^ 2 := by
  have generic := Cayley.TernaryForm.cayleyDenominator_anchorProduct
    (Form.lorentz oneNonzero) (Vector3.neg left) (Vector3.neg right)
    (by rw [anchorProductDenominator_neg]; exact defined)
  rw [anchorProduct_neg, cayleyDenominator_neg, cayleyDenominator_neg, cayleyDenominator_neg,
    anchorProductDenominator_neg] at generic
  exact generic

/-- Two admissible Lorentz anchors with a defined affine product produce another admissible anchor. -/
theorem capDenominator_anchorProduct_ne_zero (left right : Vector3 K)
    (leftDefined : capDenominator oneNonzero left ≠ 0)
    (rightDefined : capDenominator oneNonzero right ≠ 0)
    (productDefined : anchorProductDenominator oneNonzero left right ≠ 0) :
    capDenominator oneNonzero (anchorProduct oneNonzero left right productDefined) ≠ 0 := by
  have generic := Cayley.TernaryForm.cayleyDenominator_anchorProduct_ne_zero
    (Form.lorentz oneNonzero) (Vector3.neg left) (Vector3.neg right)
    (by rw [cayleyDenominator_neg]; exact leftDefined)
    (by rw [cayleyDenominator_neg]; exact rightDefined)
    (by rw [anchorProductDenominator_neg]; exact productDefined)
  rw [anchorProduct_neg, cayleyDenominator_neg] at generic
  exact generic

/-- Composing the original Lorentz cap rotations yields the cap of their source anchor product. -/
theorem capRotation_mul (left right : Vector3 K)
    (leftDefined : capDenominator oneNonzero left ≠ 0)
    (rightDefined : capDenominator oneNonzero right ≠ 0)
    (productDefined : anchorProductDenominator oneNonzero left right ≠ 0) :
    Basic.TernaryForm.SpecialOrthogonal.mul (capRotation oneNonzero left leftDefined)
        (capRotation oneNonzero right rightDefined) =
      capRotation oneNonzero (anchorProduct oneNonzero left right productDefined)
        (capDenominator_anchorProduct_ne_zero oneNonzero left right leftDefined rightDefined productDefined) := by
  let leftGeneric : Cayley.TernaryForm.cayleyDenominator
      (Form.lorentz oneNonzero) (Vector3.neg left) ≠ 0 := by
    rw [cayleyDenominator_neg]
    exact leftDefined
  let rightGeneric : Cayley.TernaryForm.cayleyDenominator
      (Form.lorentz oneNonzero) (Vector3.neg right) ≠ 0 := by
    rw [cayleyDenominator_neg]
    exact rightDefined
  let productGeneric : Cayley.TernaryForm.anchorProductDenominator
      (Form.lorentz oneNonzero) (Vector3.neg left) (Vector3.neg right) ≠ 0 := by
    rw [anchorProductDenominator_neg]
    exact productDefined
  have generic := Cayley.TernaryForm.capRotation_mul (Form.lorentz oneNonzero)
    (Vector3.neg left) (Vector3.neg right) leftGeneric rightGeneric productGeneric
  exact generic.trans (Cayley.TernaryForm.capRotation_eq_of_anchor_eq
    (Form.lorentz oneNonzero) _ _ _ _ (anchorProduct_neg oneNonzero left right productDefined))

/-- Equal source vectors give equal original Lorentz cap rotations with their respective domain certificates. -/
theorem capRotation_eq_of_anchor_eq (left right : Vector3 K)
    (leftDefined : capDenominator oneNonzero left ≠ 0)
    (rightDefined : capDenominator oneNonzero right ≠ 0) (equal : left = right) :
    capRotation oneNonzero left leftDefined = capRotation oneNonzero right rightDefined := by
  cases equal
  rfl

/-- At pairing one, two admissible Lorentz anchors have a non-null product numerator. -/
theorem anchorProductNumerator_nonNull_of_pairing_one (left right : Vector3 K)
    (leftDefined : capDenominator oneNonzero left ≠ 0)
    (rightDefined : capDenominator oneNonzero right ≠ 0)
    (pairingOne : (Form.lorentz oneNonzero).bilinear left right = 1) :
    (Form.lorentz oneNonzero).quadrance (anchorProductNumerator oneNonzero left right) ≠ 0 := by
  have denominatorZero : anchorProductDenominator oneNonzero left right = 0 := by
    unfold anchorProductDenominator
    rw [pairingOne]
    ring1
  intro numeratorNull
  apply ExplicitField.mul_ne_zero leftDefined rightDefined
  calc
    _ = anchorProductDenominator oneNonzero left right ^ 2 +
        (Form.lorentz oneNonzero).quadrance (anchorProductNumerator oneNonzero left right) :=
      (quadrance_anchorProductNumerator oneNonzero left right).symm
    _ = 0 := by rw [denominatorZero, numeratorNull]; ring1

/-- Two admissible Lorentz caps at pairing one compose to the half turn about their retained numerator. -/
theorem capRotation_mul_of_pairing_one (left right : Vector3 K)
    (leftDefined : capDenominator oneNonzero left ≠ 0)
    (rightDefined : capDenominator oneNonzero right ≠ 0)
    (pairingOne : (Form.lorentz oneNonzero).bilinear left right = 1) :
    Basic.TernaryForm.SpecialOrthogonal.mul (capRotation oneNonzero left leftDefined)
        (capRotation oneNonzero right rightDefined) =
      (Form.lorentz oneNonzero).halfTurnRotation (anchorProductNumerator oneNonzero left right)
        (anchorProductNumerator_nonNull_of_pairing_one oneNonzero left right leftDefined rightDefined pairingOne) := by
  let leftGeneric : Cayley.TernaryForm.cayleyDenominator
      (Form.lorentz oneNonzero) (Vector3.neg left) ≠ 0 := by
    rw [cayleyDenominator_neg]
    exact leftDefined
  let rightGeneric : Cayley.TernaryForm.cayleyDenominator
      (Form.lorentz oneNonzero) (Vector3.neg right) ≠ 0 := by
    rw [cayleyDenominator_neg]
    exact rightDefined
  let product := NonNullEvenClifford.mul
    (Cayley.TernaryForm.capValue (Form.lorentz oneNonzero) (Vector3.neg left) leftGeneric)
    (Cayley.TernaryForm.capValue (Form.lorentz oneNonzero) (Vector3.neg right) rightGeneric)
  have scalarZero : product.toEvenClifford.scalar = 0 := by
    change (EvenClifford.mul (Cayley.TernaryForm.capRepresentative (Form.lorentz oneNonzero) (Vector3.neg left))
      (Cayley.TernaryForm.capRepresentative (Form.lorentz oneNonzero) (Vector3.neg right))).scalar = 0
    rw [Cayley.TernaryForm.mul_capRepresentative, anchorProductDenominator_neg]
    unfold anchorProductDenominator
    rw [pairingOne]
    ring1
  have vectorEqual : product.toEvenClifford.vector = Vector3.neg (anchorProductNumerator oneNonzero left right) := by
    change (EvenClifford.mul (Cayley.TernaryForm.capRepresentative (Form.lorentz oneNonzero) (Vector3.neg left))
      (Cayley.TernaryForm.capRepresentative (Form.lorentz oneNonzero) (Vector3.neg right))).vector = _
    rw [Cayley.TernaryForm.mul_capRepresentative, anchorProductNumerator_neg]
  have numeratorNonNull := anchorProductNumerator_nonNull_of_pairing_one
    oneNonzero left right leftDefined rightDefined pairingOne
  calc
    _ = NonNullEvenClifford.actionRotation product := (NonNullEvenClifford.actionRotation_mul _ _).symm
    _ = (Form.lorentz oneNonzero).halfTurnRotation product.toEvenClifford.vector
        (Cayley.TernaryForm.NonNullEvenClifford.vectorNonNull_of_scalar_eq_zero product scalarZero) :=
      Cayley.TernaryForm.NonNullEvenClifford.actionRotation_eq_halfTurn_of_scalar_eq_zero product scalarZero
    _ = (Form.lorentz oneNonzero).halfTurnRotation
        (Vector3.neg (anchorProductNumerator oneNonzero left right))
        (by rw [Form.quadrance_neg]; exact numeratorNonNull) :=
      (Form.lorentz oneNonzero).halfTurnRotation_eq_of_axis_eq _ _ _ _ vectorEqual
    _ = _ := (Form.lorentz oneNonzero).halfTurnRotation_neg _ numeratorNonNull

/-- Two admissible Lorentz caps compose to a half turn exactly when their anchor pairing is one. -/
theorem capRotation_mul_isHalfTurn_iff [DecidableEq K] (left right : Vector3 K)
    (leftDefined : capDenominator oneNonzero left ≠ 0)
    (rightDefined : capDenominator oneNonzero right ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (∃ axis : Vector3 K, ∃ nonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0,
      Basic.TernaryForm.SpecialOrthogonal.mul (capRotation oneNonzero left leftDefined)
        (capRotation oneNonzero right rightDefined) = (Form.lorentz oneNonzero).halfTurnRotation axis nonNull) ↔
      (Form.lorentz oneNonzero).bilinear left right = 1 := by
  constructor
  · rintro ⟨axis, nonNull, equal⟩
    by_cases pairingOne : (Form.lorentz oneNonzero).bilinear left right = 1
    · exact pairingOne
    · have productDefined := (anchorProductDenominator_ne_zero_iff oneNonzero left right).mpr pairingOne
      have outputDefined := capDenominator_anchorProduct_ne_zero
        oneNonzero left right leftDefined rightDefined productDefined
      exact False.elim ((capRotation_ne_halfTurn oneNonzero
        (anchorProduct oneNonzero left right productDefined) axis outputDefined nonNull twoNonzero)
        ((capRotation_mul oneNonzero left right leftDefined rightDefined productDefined).symm.trans equal))
  · intro pairingOne
    exact ⟨anchorProductNumerator oneNonzero left right,
      anchorProductNumerator_nonNull_of_pairing_one oneNonzero left right leftDefined rightDefined pairingOne,
      capRotation_mul_of_pairing_one oneNonzero left right leftDefined rightDefined pairingOne⟩

/-- Parallel Lorentz anchors have denominator one minus the axis quadrance times both parameters. -/
theorem anchorProductDenominator_collinear (axis : Vector3 K) (left right : K) :
    anchorProductDenominator oneNonzero (Vector3.scale left axis) (Vector3.scale right axis) =
      1 - (Form.lorentz oneNonzero).quadrance axis * left * right := by
  unfold anchorProductDenominator
  rw [Form.bilinear_scale_left, Form.bilinear_scale_right]
  change 1 - left * (right * (Form.lorentz oneNonzero).quadrance axis) = _
  ring1

/-- Parallel Lorentz anchors have numerator equal to their summed scalar multiple of the axis. -/
theorem anchorProductNumerator_collinear (axis : Vector3 K) (left right : K) :
    anchorProductNumerator oneNonzero (Vector3.scale left axis) (Vector3.scale right axis) =
      Vector3.scale (left + right) axis := by
  unfold anchorProductNumerator
  rw [Quadratic.Ternary.Lorentz.cross_coordinates]
  ext <;> unfold Vector3.sub Vector3.add Vector3.scale <;> ring1

/-- The partial Lorentz anchor product on one axis obeys the rational tangent addition law. -/
theorem anchorProduct_collinear (axis : Vector3 K) (left right : K)
    (defined : anchorProductDenominator oneNonzero (Vector3.scale left axis) (Vector3.scale right axis) ≠ 0) :
    anchorProduct oneNonzero (Vector3.scale left axis) (Vector3.scale right axis) defined =
      Vector3.scale ((left + right) / (1 - (Form.lorentz oneNonzero).quadrance axis * left * right)) axis := by
  unfold anchorProduct
  rw [anchorProductDenominator_collinear, anchorProductNumerator_collinear, Vector3.scale_scale]
  rw [ExplicitField.div_eq_mul_inv, mul_comm]

/-- Two admissible collinear Lorentz caps give an admissible cap at the summed tangent parameter. -/
theorem capDenominator_collinear_ne_zero (axis : Vector3 K) (left right : K)
    (leftDefined : capDenominator oneNonzero (Vector3.scale left axis) ≠ 0)
    (rightDefined : capDenominator oneNonzero (Vector3.scale right axis) ≠ 0)
    (productDefined : anchorProductDenominator oneNonzero (Vector3.scale left axis) (Vector3.scale right axis) ≠ 0) :
    capDenominator oneNonzero
      (Vector3.scale ((left + right) / (1 - (Form.lorentz oneNonzero).quadrance axis * left * right)) axis) ≠ 0 := by
  have outputDefined := capDenominator_anchorProduct_ne_zero oneNonzero
    (Vector3.scale left axis) (Vector3.scale right axis) leftDefined rightDefined productDefined
  rw [anchorProduct_collinear] at outputDefined
  exact outputDefined

/-- The original collinear Lorentz caps compose by the rational tangent addition law. -/
theorem capRotation_collinear_mul (axis : Vector3 K) (left right : K)
    (leftDefined : capDenominator oneNonzero (Vector3.scale left axis) ≠ 0)
    (rightDefined : capDenominator oneNonzero (Vector3.scale right axis) ≠ 0)
    (productDefined : anchorProductDenominator oneNonzero (Vector3.scale left axis) (Vector3.scale right axis) ≠ 0) :
    Basic.TernaryForm.SpecialOrthogonal.mul
        (capRotation oneNonzero (Vector3.scale left axis) leftDefined)
        (capRotation oneNonzero (Vector3.scale right axis) rightDefined) =
      capRotation oneNonzero
        (Vector3.scale ((left + right) / (1 - (Form.lorentz oneNonzero).quadrance axis * left * right)) axis)
        (capDenominator_collinear_ne_zero oneNonzero axis left right leftDefined rightDefined productDefined) := by
  exact (capRotation_mul oneNonzero (Vector3.scale left axis) (Vector3.scale right axis)
    leftDefined rightDefined productDefined).trans (capRotation_eq_of_anchor_eq oneNonzero _ _ _ _
      (anchorProduct_collinear oneNonzero axis left right productDefined))

/-- Collinear unit-spacelike anchors add with denominator one plus the parameter product. -/
theorem anchorProduct_collinear_spacelike (axis : Vector3 K) (left right : K)
    (unitSpacelike : (Form.lorentz oneNonzero).quadrance axis = -1)
    (defined : anchorProductDenominator oneNonzero (Vector3.scale left axis) (Vector3.scale right axis) ≠ 0) :
    anchorProduct oneNonzero (Vector3.scale left axis) (Vector3.scale right axis) defined =
      Vector3.scale ((left + right) / (1 + left * right)) axis := by
  rw [anchorProduct_collinear, unitSpacelike]
  rw [show 1 - (-1 : K) * left * right = 1 + left * right by ring1]

/-- Convert a collinear boost anchor parameter to its rational physical velocity. -/
@[expose] def boostVelocity (parameter : K) : K := 2 * parameter / (1 + parameter ^ 2)

/-- Clearing the two input velocity denominators gives the sum of two parameter squares. -/
theorem boostVelocity_add_denominator (left right : K)
    (leftDefined : 1 + left ^ 2 ≠ 0) (rightDefined : 1 + right ^ 2 ≠ 0) :
    (1 + boostVelocity left * boostVelocity right) * ((1 + left ^ 2) * (1 + right ^ 2)) =
      (1 + left * right) ^ 2 + (left + right) ^ 2 := by
  have leftCancel : boostVelocity left * (1 + left ^ 2) = 2 * left :=
    ExplicitField.div_mul_cancel _ leftDefined
  have rightCancel : boostVelocity right * (1 + right ^ 2) = 2 * right :=
    ExplicitField.div_mul_cancel _ rightDefined
  calc
    _ = (1 + left ^ 2) * (1 + right ^ 2) +
        (boostVelocity left * (1 + left ^ 2)) * (boostVelocity right * (1 + right ^ 2)) := by ring1
    _ = _ := by rw [leftCancel, rightCancel]; ring1

/-- A defined collinear anchor sum has a positive Einstein velocity denominator over the owned ordered field. -/
theorem boostVelocity_add_denominator_pos {F : Type*} [RayOrderedExplicitField F] (left right : F)
    (anchorDefined : 1 + left * right ≠ 0) : 0 < 1 + boostVelocity left * boostVelocity right := by
  have leftPositive : 0 < 1 + left ^ 2 :=
    RayOrderedExplicitField.add_square_pos OrderedExplicitField.zero_lt_one_direct
  have rightPositive : 0 < 1 + right ^ 2 :=
    RayOrderedExplicitField.add_square_pos OrderedExplicitField.zero_lt_one_direct
  have inputProductPositive := OrderedExplicitField.mul_pos_direct leftPositive rightPositive
  have inputProductNonzero := RayOrderedExplicitField.positive_ne_zero_direct inputProductPositive
  have squarePositive : 0 < (1 + left * right) ^ 2 := by
    simpa only [pow_two] using OrderedExplicitField.mul_self_pos_direct anchorDefined
  have commonPositive := RayOrderedExplicitField.add_square_pos (value := left + right) squarePositive
  have cleared := boostVelocity_add_denominator left right
    (RayOrderedExplicitField.positive_ne_zero_direct leftPositive)
    (RayOrderedExplicitField.positive_ne_zero_direct rightPositive)
  have ratioPositive := OrderedExplicitField.mul_pos_direct commonPositive
    (OrderedExplicitField.inv_pos_direct inputProductPositive)
  rw [← cleared, mul_assoc, ExplicitField.mul_inv_cancel _ inputProductNonzero, mul_one] at ratioPositive
  exact ratioPositive

/-- Rational boost velocities obey Einstein addition whenever the displayed denominators are nonzero.

The collinear anchor parameter is `(left + right) / (1 + left * right)`.
Clearing the retained nonzero denominators identifies both velocity
expressions with the same numerator over the same scalar denominator.
-/
theorem boostVelocity_add (left right : K)
    (leftDefined : 1 + left ^ 2 ≠ 0) (rightDefined : 1 + right ^ 2 ≠ 0)
    (anchorDefined : 1 + left * right ≠ 0)
    (velocityDefined : 1 + boostVelocity left * boostVelocity right ≠ 0) :
    boostVelocity ((left + right) / (1 + left * right)) =
      (boostVelocity left + boostVelocity right) / (1 + boostVelocity left * boostVelocity right) := by
  let denominator := 1 + left * right
  let parameter := (left + right) / denominator
  let leftDenominator := 1 + left ^ 2
  let rightDenominator := 1 + right ^ 2
  let velocityDenominator := 1 + boostVelocity left * boostVelocity right
  let common := denominator ^ 2 + (left + right) ^ 2
  have parameterCancel : parameter * denominator = left + right :=
    ExplicitField.div_mul_cancel _ anchorDefined
  have leftCancel : boostVelocity left * leftDenominator = 2 * left :=
    ExplicitField.div_mul_cancel _ leftDefined
  have rightCancel : boostVelocity right * rightDenominator = 2 * right :=
    ExplicitField.div_mul_cancel _ rightDefined
  have commonRight : velocityDenominator * (leftDenominator * rightDenominator) = common :=
    boostVelocity_add_denominator left right leftDefined rightDefined
  have commonNonzero : common ≠ 0 := by
    rw [← commonRight]
    exact ExplicitField.mul_ne_zero velocityDefined (ExplicitField.mul_ne_zero leftDefined rightDefined)
  have commonLeft : (1 + parameter ^ 2) * denominator ^ 2 = common := by
    calc
      _ = denominator ^ 2 + (parameter * denominator) ^ 2 := by ring1
      _ = _ := by rw [parameterCancel]
  have parameterDefined : 1 + parameter ^ 2 ≠ 0 := by
    intro denominatorZero
    apply commonNonzero
    calc
      _ = (1 + parameter ^ 2) * denominator ^ 2 := commonLeft.symm
      _ = 0 := by rw [denominatorZero]; ring1
  have leftReading : boostVelocity parameter * common = 2 * (left + right) * denominator := by
    calc
      _ = (boostVelocity parameter * (1 + parameter ^ 2)) * denominator ^ 2 := by
        rw [← commonLeft]
        ring1
      _ = (2 * parameter) * denominator ^ 2 := by
        rw [show boostVelocity parameter * (1 + parameter ^ 2) = 2 * parameter from
          ExplicitField.div_mul_cancel _ parameterDefined]
      _ = 2 * (parameter * denominator) * denominator := by ring1
      _ = _ := by rw [parameterCancel]
  have rightReading :
      ((boostVelocity left + boostVelocity right) / velocityDenominator) * common =
        2 * (left + right) * denominator := by
    calc
      _ = (((boostVelocity left + boostVelocity right) / velocityDenominator) * velocityDenominator) *
          (leftDenominator * rightDenominator) := by rw [← commonRight]; ring1
      _ = (boostVelocity left + boostVelocity right) * (leftDenominator * rightDenominator) := by
        rw [ExplicitField.div_mul_cancel _ velocityDefined]
      _ = (boostVelocity left * leftDenominator) * rightDenominator +
          (boostVelocity right * rightDenominator) * leftDenominator := by ring1
      _ = _ := by rw [leftCancel, rightCancel]; unfold denominator leftDenominator rightDenominator; ring1
  exact ExplicitField.eq_of_mul_eq_mul_right commonNonzero (leftReading.trans rightReading.symm)

/-- The original Lorentz anchor product is associative when both groupings and all three input caps exist.

The four product certificates retain both intermediate anchors and both
outer domains. Each grouping reads back the same ordered composition of
the three original cap rotations, whose anchor is unique.
-/
theorem anchorProduct_associative [DecidableEq K] (first second third : Vector3 K)
    (firstDefined : capDenominator oneNonzero first ≠ 0)
    (secondDefined : capDenominator oneNonzero second ≠ 0)
    (thirdDefined : capDenominator oneNonzero third ≠ 0)
    (firstSecondDefined : anchorProductDenominator oneNonzero first second ≠ 0)
    (secondThirdDefined : anchorProductDenominator oneNonzero second third ≠ 0)
    (leftDefined : anchorProductDenominator oneNonzero
      (anchorProduct oneNonzero first second firstSecondDefined) third ≠ 0)
    (rightDefined : anchorProductDenominator oneNonzero first
      (anchorProduct oneNonzero second third secondThirdDefined) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    anchorProduct oneNonzero (anchorProduct oneNonzero first second firstSecondDefined) third leftDefined =
      anchorProduct oneNonzero first (anchorProduct oneNonzero second third secondThirdDefined) rightDefined := by
  let firstSecond := anchorProduct oneNonzero first second firstSecondDefined
  let secondThird := anchorProduct oneNonzero second third secondThirdDefined
  let firstSecondCap := capDenominator_anchorProduct_ne_zero oneNonzero first second
    firstDefined secondDefined firstSecondDefined
  let secondThirdCap := capDenominator_anchorProduct_ne_zero oneNonzero second third
    secondDefined thirdDefined secondThirdDefined
  let leftCap := capDenominator_anchorProduct_ne_zero oneNonzero firstSecond third
    firstSecondCap thirdDefined leftDefined
  let rightCap := capDenominator_anchorProduct_ne_zero oneNonzero first secondThird
    firstDefined secondThirdCap rightDefined
  have rotationsEqual : capRotation oneNonzero
      (anchorProduct oneNonzero firstSecond third leftDefined) leftCap =
      capRotation oneNonzero (anchorProduct oneNonzero first secondThird rightDefined) rightCap := by
    calc
      _ = Basic.TernaryForm.SpecialOrthogonal.mul
          (capRotation oneNonzero firstSecond firstSecondCap) (capRotation oneNonzero third thirdDefined) :=
        (capRotation_mul oneNonzero firstSecond third firstSecondCap thirdDefined leftDefined).symm
      _ = Basic.TernaryForm.SpecialOrthogonal.mul
          (Basic.TernaryForm.SpecialOrthogonal.mul (capRotation oneNonzero first firstDefined)
            (capRotation oneNonzero second secondDefined)) (capRotation oneNonzero third thirdDefined) :=
        congrArg (fun rotation => Basic.TernaryForm.SpecialOrthogonal.mul rotation
          (capRotation oneNonzero third thirdDefined))
          (capRotation_mul oneNonzero first second firstDefined secondDefined firstSecondDefined).symm
      _ = Basic.TernaryForm.SpecialOrthogonal.mul (capRotation oneNonzero first firstDefined)
          (Basic.TernaryForm.SpecialOrthogonal.mul (capRotation oneNonzero second secondDefined)
            (capRotation oneNonzero third thirdDefined)) := Basic.TernaryForm.SpecialOrthogonal.mul_assoc _ _ _
      _ = Basic.TernaryForm.SpecialOrthogonal.mul (capRotation oneNonzero first firstDefined)
          (capRotation oneNonzero secondThird secondThirdCap) :=
        congrArg (Basic.TernaryForm.SpecialOrthogonal.mul (capRotation oneNonzero first firstDefined))
          (capRotation_mul oneNonzero second third secondDefined thirdDefined secondThirdDefined)
      _ = _ := capRotation_mul oneNonzero first secondThird firstDefined secondThirdCap rightDefined
  exact cap_injective oneNonzero _ _ leftCap rightCap twoNonzero
    (congrArg (fun rotation : (Form.lorentz oneNonzero).SpecialOrthogonal => rotation.matrix) rotationsEqual)

end Purelib.Geometry.Rotations.Ternary.Lorentz
