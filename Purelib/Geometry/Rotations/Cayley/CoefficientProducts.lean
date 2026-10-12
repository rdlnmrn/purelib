module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
import Purelib.Algebra.Group.Negation
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rotations.Cayley.Product

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rotations

open Purelib.LinearAlgebra

@[expose] public section

/-!
# Conjecture 52: coefficient anchor products

The coefficient family is represented homogeneously with a constant and a
dot-product denominator coefficient.  Global nonzero rescaling of all five
coefficients leaves the same rational operation.  This exposes a missing
nondegeneracy hypothesis in Conjecture 52: the left projection belongs to
the displayed family and is associative, but is not the anchor product or
its opposite.
-/

namespace Purelib.Geometry.Rotations.Cayley.CoefficientProducts

open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- Homogeneous coefficients for `(αv+βu+γ(v×u))/(ε+δ(v·u))`. -/
@[ext]
structure CoefficientProductParameters (K : Type*) where
  /-- The scalar multiplying the left input vector. -/ leftCoefficient : K
  /-- The scalar multiplying the right input vector. -/ rightCoefficient : K
  /-- The scalar multiplying the cross product of the inputs. -/ crossCoefficient : K
  /-- The constant term of the affine denominator. -/ constantCoefficient : K
  /-- The scalar multiplying the input dot product in the denominator. -/ dotCoefficient : K

constructive_injectivity CoefficientProductParameters

section CoefficientProductParameters

/-- The displayed linear combination of the two input vectors and their cross product. -/
def CoefficientProductParameters.numerator (parameters : CoefficientProductParameters K)
    (left right : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.add
    (Coordinates3.Vector.add (Coordinates3.Vector.scale parameters.leftCoefficient left)
      (Coordinates3.Vector.scale parameters.rightCoefficient right))
    (Coordinates3.Vector.scale parameters.crossCoefficient (Coordinates3.Vector.cross left right))

/-- The denominator constant plus the dot coefficient times the input dot product. -/
def CoefficientProductParameters.denominator (parameters : CoefficientProductParameters K)
    (left right : Coordinates3.Vector K) : K :=
  parameters.constantCoefficient +
    parameters.dotCoefficient * Coordinates3.Vector.dot left right

/-- The partial coefficient product on its displayed affine domain. -/
def CoefficientProductParameters.product (parameters : CoefficientProductParameters K)
    (left right : Coordinates3.Vector K) (_defined : parameters.denominator left right ≠ 0) :
    Coordinates3.Vector K :=
  Coordinates3.Vector.scale (1 / parameters.denominator left right)
    (parameters.numerator left right)

/-- With zero as the right input, the denominator equals its constant coefficient. -/
theorem CoefficientProductParameters.denominator_zero_right
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K) (vector :
      Coordinates3.Vector K) :
    parameters.denominator vector Coordinates3.Vector.zero =
      parameters.constantCoefficient := by
  unfold Cayley.CoefficientProducts.CoefficientProductParameters.denominator
  rw [Coordinates3.Vector.dot_zero_right]
  ring1

/-- With zero as the left input, the denominator equals its constant coefficient. -/
theorem CoefficientProductParameters.denominator_zero_left
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K) (vector :
      Coordinates3.Vector K) :
    parameters.denominator Coordinates3.Vector.zero vector =
      parameters.constantCoefficient := by
  unfold Cayley.CoefficientProducts.CoefficientProductParameters.denominator
  rw [Coordinates3.Vector.dot_zero_left]
  ring1

/-- Compatibility with the anchor chart's identity: the constant denominator is explicitly nonzero, and the displayed
zero vector is a two-sided identity. The nonzero certificate makes both identity products executable data. -/
structure CoefficientProductParameters.HasZeroIdentity (parameters : CoefficientProductParameters K) :
  Prop where
  /-- The denominator constant is nonzero, so both zero-input products are defined. -/ constantNonzero :
    parameters.constantCoefficient ≠ 0
  /-- Multiplication by zero on the right fixes each input vector. -/ rightIdentity : ∀ vector : Coordinates3.Vector K,
    parameters.product vector Coordinates3.Vector.zero
      (by rwa [parameters.denominator_zero_right vector]) = vector
  /-- Multiplication by zero on the left fixes each input vector. -/ leftIdentity : ∀ vector : Coordinates3.Vector K,
    parameters.product Coordinates3.Vector.zero vector
      (by rwa [parameters.denominator_zero_left vector]) = vector

/-- A zero right identity forces the left coefficient to equal the denominator constant. -/
theorem CoefficientProductParameters.leftCoefficient_eq_constant
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (identity : parameters.HasZeroIdentity) :
    parameters.leftCoefficient = parameters.constantCoefficient := by
  let basisT : Coordinates3.Vector K := ⟨1, 0, 0⟩
  have coordinate := congrArg Coordinates3.Vector.t (identity.rightIdentity basisT)
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
    parameters.constantCoefficient identity.constantNonzero
  dsimp only [Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.product,
    Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.numerator,
    Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.denominator, basisT,
    Coordinates3.Vector.scale, Coordinates3.Vector.add,
    Coordinates3.Vector.cross, Coordinates3.Vector.zero] at coordinate
  have coordinate' : parameters.constantCoefficient⁻¹ *
      parameters.leftCoefficient = 1 := by
    simpa only [Coordinates3.Vector.dot, Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_self] using coordinate
  calc
    parameters.leftCoefficient =
        (parameters.constantCoefficient *
          parameters.constantCoefficient⁻¹) * parameters.leftCoefficient := by
      rw [cancel, one_mul]
    _ = parameters.constantCoefficient *
        (parameters.constantCoefficient⁻¹ *
          parameters.leftCoefficient) := by ring1
    _ = parameters.constantCoefficient := by rw [coordinate', mul_one]

/-- A zero left identity forces the right coefficient to equal the denominator constant. -/
theorem CoefficientProductParameters.rightCoefficient_eq_constant
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (identity : parameters.HasZeroIdentity) :
    parameters.rightCoefficient = parameters.constantCoefficient := by
  let basisT : Coordinates3.Vector K := ⟨1, 0, 0⟩
  have coordinate := congrArg Coordinates3.Vector.t (identity.leftIdentity basisT)
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
    parameters.constantCoefficient identity.constantNonzero
  dsimp only [Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.product,
    Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.numerator,
    Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.denominator, basisT,
    Coordinates3.Vector.scale, Coordinates3.Vector.add,
    Coordinates3.Vector.cross, Coordinates3.Vector.zero] at coordinate
  have coordinate' : parameters.constantCoefficient⁻¹ *
      parameters.rightCoefficient = 1 := by
    simpa only [Coordinates3.Vector.dot, Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_self] using coordinate
  calc
    parameters.rightCoefficient =
        (parameters.constantCoefficient *
          parameters.constantCoefficient⁻¹) * parameters.rightCoefficient := by
      rw [cancel, one_mul]
    _ = parameters.constantCoefficient *
        (parameters.constantCoefficient⁻¹ *
          parameters.rightCoefficient) := by ring1
    _ = parameters.constantCoefficient := by rw [coordinate', mul_one]

/-- Associativity wherever all four products in the two bracketings are defined. -/
def CoefficientProductParameters.AssociativeWhereDefined
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K) : Prop :=
  ∀ (first second third : Coordinates3.Vector K)
    (firstSecondDefined : parameters.denominator first second ≠ 0)
    (secondThirdDefined : parameters.denominator second third ≠ 0)
    (leftDefined : parameters.denominator
      (parameters.product first second firstSecondDefined) third ≠ 0)
    (rightDefined : parameters.denominator first
      (parameters.product second third secondThirdDefined) ≠ 0),
    parameters.product
        (parameters.product first second firstSecondDefined) third leftDefined =
      parameters.product first
        (parameters.product second third secondThirdDefined) rightDefined

/-- A single displayed scalar probe makes the unital associativity classification finite over any explicit field. Over
the rationals one can use `1`, except in the sole case where that denominator vanishes, and then use `2`. -/
theorem CoefficientProductParameters.constant_mul_dotCoefficient_eq_neg_crossCoefficient_sq
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (identity : parameters.HasZeroIdentity)
    (associative : parameters.AssociativeWhereDefined)
    (probe : K) (probeNonzero : probe ≠ 0)
    (probeDefined : parameters.constantCoefficient +
      parameters.dotCoefficient * probe ^ 2 ≠ 0) :
    parameters.constantCoefficient * parameters.dotCoefficient =
      -(parameters.crossCoefficient ^ 2) := by
  let first : Coordinates3.Vector K := ⟨probe, 0, 0⟩
  let third : Coordinates3.Vector K := ⟨0, 1, 0⟩
  have leftCoefficient := parameters.leftCoefficient_eq_constant identity
  have rightCoefficient := parameters.rightCoefficient_eq_constant identity
  have constantCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    parameters.constantCoefficient identity.constantNonzero
  have constantReverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := constantCancel
  have firstSecondDenominator :
      parameters.denominator first first =
        parameters.constantCoefficient +
          parameters.dotCoefficient * probe ^ 2 := by
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.denominator first Coordinates3.Vector.dot
    ring1
  let firstSecondDefined : parameters.denominator first first ≠ 0 := by
    rwa [firstSecondDenominator]
  have secondThirdDenominator :
      parameters.denominator first third =
        parameters.constantCoefficient := by
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.denominator first third Coordinates3.Vector.dot
    ring1
  let secondThirdDefined : parameters.denominator first third ≠ 0 := by
    rw [secondThirdDenominator]
    exact identity.constantNonzero
  have firstSecondProduct :
      parameters.product first first firstSecondDefined =
        ⟨(parameters.constantCoefficient +
            parameters.dotCoefficient * probe ^ 2)⁻¹ *
              (2 * parameters.constantCoefficient * probe), 0, 0⟩ := by
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.product
    rw [firstSecondDenominator]
    apply Coordinates3.Vector.ext <;>
      unfold Cayley.CoefficientProducts.CoefficientProductParameters.numerator first Coordinates3.Vector.scale
        Coordinates3.Vector.add Coordinates3.Vector.cross <;>
      simp only [leftCoefficient, rightCoefficient,
        Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul, mul_zero, zero_mul,
        add_zero, sub_self, -eq_self, -iff_self]
    all_goals ring1
  have secondThirdProduct :
      parameters.product first third secondThirdDefined =
        ⟨probe, 1,
          parameters.constantCoefficient⁻¹ *
            parameters.crossCoefficient * probe⟩ := by
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.product
    rw [secondThirdDenominator]
    apply Coordinates3.Vector.ext
    · unfold Cayley.CoefficientProducts.CoefficientProductParameters.numerator first third Coordinates3.Vector.scale
        Coordinates3.Vector.add Coordinates3.Vector.cross
      simp only [leftCoefficient, rightCoefficient,
        Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul, mul_zero,
        add_zero, sub_self, -eq_self, -iff_self]
      rw [← mul_assoc, constantReverseCancel, one_mul]
    · unfold Cayley.CoefficientProducts.CoefficientProductParameters.numerator first third Coordinates3.Vector.scale
        Coordinates3.Vector.add Coordinates3.Vector.cross
      simp only [leftCoefficient, rightCoefficient,
        Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul, mul_zero, zero_mul,
        mul_one, add_zero, zero_add, sub_self, -eq_self, -iff_self]
      exact constantReverseCancel
    · unfold Cayley.CoefficientProducts.CoefficientProductParameters.numerator first third Coordinates3.Vector.scale
        Coordinates3.Vector.add Coordinates3.Vector.cross
      simp only [leftCoefficient, rightCoefficient,
        Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul, mul_zero,
        add_zero, -eq_self, -iff_self]
      rw [SubNegMonoid.sub_eq_add_neg,
        SubtractionMonoid.neg_eq_of_add (0 : K) 0 (AddZeroClass.add_zero 0),
        AddZeroClass.add_zero]
      ring1
  have leftOuterDenominator :
      parameters.denominator
          (parameters.product first first firstSecondDefined) third =
        parameters.constantCoefficient := by
    rw [firstSecondProduct]
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.denominator third Coordinates3.Vector.dot
    ring1
  let leftDefined : parameters.denominator
      (parameters.product first first firstSecondDefined) third ≠ 0 := by
    rw [leftOuterDenominator]
    exact identity.constantNonzero
  have rightOuterDenominator :
      parameters.denominator first
          (parameters.product first third secondThirdDefined) =
        parameters.constantCoefficient +
          parameters.dotCoefficient * probe ^ 2 := by
    rw [secondThirdProduct]
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.denominator first Coordinates3.Vector.dot
    ring1
  let rightDefined : parameters.denominator first
      (parameters.product first third secondThirdDefined) ≠ 0 := by
    rwa [rightOuterDenominator]
  have association := associative first first third firstSecondDefined
    secondThirdDefined leftDefined rightDefined
  have coordinate := congrArg Coordinates3.Vector.r association
  have leftCoordinate :
      (parameters.product
          (parameters.product first first firstSecondDefined) third
            leftDefined).r = 1 := by
    change (Coordinates3.Vector.scale
      (1 / parameters.denominator
        (parameters.product first first firstSecondDefined) third)
      (parameters.numerator
        (parameters.product first first firstSecondDefined) third)).r = 1
    rw [leftOuterDenominator, firstSecondProduct]
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.numerator third Coordinates3.Vector.scale
      Coordinates3.Vector.add Coordinates3.Vector.cross
    simp only [leftCoefficient, rightCoefficient,
      Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_self, -eq_self, -iff_self]
    exact constantReverseCancel
  have rightCoordinate :
      (parameters.product first
          (parameters.product first third secondThirdDefined)
            rightDefined).r =
        (parameters.constantCoefficient +
          parameters.dotCoefficient * probe ^ 2)⁻¹ *
            (parameters.constantCoefficient -
              parameters.constantCoefficient⁻¹ *
                parameters.crossCoefficient ^ 2 * probe ^ 2) := by
    change (Coordinates3.Vector.scale
      (1 / parameters.denominator first
        (parameters.product first third secondThirdDefined))
      (parameters.numerator first
        (parameters.product first third secondThirdDefined))).r = _
    rw [rightOuterDenominator, secondThirdProduct]
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.numerator first Coordinates3.Vector.scale
      Coordinates3.Vector.add Coordinates3.Vector.cross
    rw [leftCoefficient, rightCoefficient]
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul, -eq_self, -iff_self]
    ring1
  rw [leftCoordinate, rightCoordinate] at coordinate
  have firstSecondCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (parameters.constantCoefficient +
      parameters.dotCoefficient * probe ^ 2) probeDefined
  have probeSquareNonzero : probe ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      Algebra.Field.ExplicitField.mul_ne_zero probeNonzero probeNonzero
  have relationTimesProbeSquare :
      (parameters.constantCoefficient * parameters.dotCoefficient +
        parameters.crossCoefficient ^ 2) * probe ^ 2 = 0 := by
    have cleared :
        parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) =
          parameters.constantCoefficient *
            (parameters.constantCoefficient -
              parameters.constantCoefficient⁻¹ *
                parameters.crossCoefficient ^ 2 * probe ^ 2) := by
      calc
        parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) =
          parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) * 1 := by rw [mul_one]
        _ = parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) *
              ((parameters.constantCoefficient +
                  parameters.dotCoefficient * probe ^ 2)⁻¹ *
                (parameters.constantCoefficient -
                  parameters.constantCoefficient⁻¹ *
                    parameters.crossCoefficient ^ 2 * probe ^ 2)) := by
              rw [coordinate]
        _ = parameters.constantCoefficient *
            (parameters.constantCoefficient -
              parameters.constantCoefficient⁻¹ *
                parameters.crossCoefficient ^ 2 * probe ^ 2) := by
              calc
                parameters.constantCoefficient *
                    (parameters.constantCoefficient +
                      parameters.dotCoefficient * probe ^ 2) *
                      ((parameters.constantCoefficient +
                          parameters.dotCoefficient * probe ^ 2)⁻¹ *
                        (parameters.constantCoefficient -
                          parameters.constantCoefficient⁻¹ *
                            parameters.crossCoefficient ^ 2 * probe ^ 2)) =
                  parameters.constantCoefficient *
                    (((parameters.constantCoefficient +
                        parameters.dotCoefficient * probe ^ 2) *
                      (parameters.constantCoefficient +
                        parameters.dotCoefficient * probe ^ 2)⁻¹) *
                      (parameters.constantCoefficient -
                        parameters.constantCoefficient⁻¹ *
                          parameters.crossCoefficient ^ 2 * probe ^ 2)) := by
                            ring1
                _ = _ := by rw [firstSecondCancel, one_mul]
    calc
      (parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) * probe ^ 2 =
        (parameters.constantCoefficient * parameters.dotCoefficient +
          (parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹) *
              parameters.crossCoefficient ^ 2) * probe ^ 2 := by
                rw [constantCancel, one_mul]
      _ =
        parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) -
          parameters.constantCoefficient *
            (parameters.constantCoefficient -
              parameters.constantCoefficient⁻¹ *
                parameters.crossCoefficient ^ 2 * probe ^ 2) := by
                  ring1
      _ = 0 := by rw [cleared]; ring1
  have relationZero :
      parameters.constantCoefficient * parameters.dotCoefficient +
        parameters.crossCoefficient ^ 2 = 0 := by
    have probeSquareCancel := Algebra.Field.ExplicitField.mul_inv_cancel
      (probe ^ 2) probeSquareNonzero
    calc
      parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2 =
        (parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) * 1 := by rw [mul_one]
      _ = (parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) *
            ((probe ^ 2) * (probe ^ 2)⁻¹) := by rw [probeSquareCancel]
      _ = ((parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) * probe ^ 2) *
            (probe ^ 2)⁻¹ := by ring1
      _ = 0 := by rw [relationTimesProbeSquare, zero_mul]
  calc
    parameters.constantCoefficient * parameters.dotCoefficient =
        (parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) -
            parameters.crossCoefficient ^ 2 := by ring1
    _ = -(parameters.crossCoefficient ^ 2) := by rw [relationZero]; ring1

/-- The coefficient equalities forced by a zero identity are also sufficient for that identity. -/
theorem CoefficientProductParameters.hasZeroIdentity_of_coefficients
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient) :
    parameters.HasZeroIdentity := by
  have constantReverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  refine
    { constantNonzero := constantNonzero
      rightIdentity := ?_
      leftIdentity := ?_ }
  · intro vector
    apply Coordinates3.Vector.ext <;>
      unfold Cayley.CoefficientProducts.CoefficientProductParameters.product
        Cayley.CoefficientProducts.CoefficientProductParameters.numerator
        Cayley.CoefficientProducts.CoefficientProductParameters.denominator Coordinates3.Vector.zero
        Coordinates3.Vector.scale Coordinates3.Vector.add
        Coordinates3.Vector.cross Coordinates3.Vector.dot <;>
      simp only [leftCoefficient, rightCoefficient,
        Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul, mul_zero, zero_mul,
        add_zero, sub_self] <;>
      rw [← mul_assoc, constantReverseCancel, one_mul]
  · intro vector
    apply Coordinates3.Vector.ext <;>
      unfold Cayley.CoefficientProducts.CoefficientProductParameters.product
        Cayley.CoefficientProducts.CoefficientProductParameters.numerator
        Cayley.CoefficientProducts.CoefficientProductParameters.denominator Coordinates3.Vector.zero
        Coordinates3.Vector.scale Coordinates3.Vector.add
        Coordinates3.Vector.cross Coordinates3.Vector.dot <;>
      simp only [leftCoefficient, rightCoefficient,
        Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul, mul_zero, zero_mul,
        add_zero, zero_add, sub_self] <;>
      rw [← mul_assoc, constantReverseCancel, one_mul]

/-- The affine-coordinate dilation attached to homogeneous unital coefficients. -/
def CoefficientProductParameters.dilationFactor (parameters : CoefficientProductParameters K) : K :=
  parameters.crossCoefficient * parameters.constantCoefficient⁻¹

/-- Multiplying the dilation factor by the nonzero denominator constant recovers the cross coefficient. -/
theorem CoefficientProductParameters.dilationFactor_mul_constant
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0) :
    parameters.dilationFactor * parameters.constantCoefficient =
      parameters.crossCoefficient := by
  have reverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  unfold Cayley.CoefficientProducts.CoefficientProductParameters.dilationFactor
  calc
    parameters.crossCoefficient * parameters.constantCoefficient⁻¹ *
        parameters.constantCoefficient =
      parameters.crossCoefficient *
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) := by ring1
    _ = parameters.crossCoefficient := by rw [reverseCancel, mul_one]

/-- The normalized dot coefficient is the negative square of the dilation factor under the classification equation. -/
private theorem
  CoefficientProductParameters.normalized_dotCoefficient
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2)) :
    parameters.constantCoefficient⁻¹ * parameters.dotCoefficient =
      -(parameters.dilationFactor ^ 2) := by
  have reverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  have inverseSquaredTimesConstant :
      parameters.constantCoefficient⁻¹ ^ 2 *
          parameters.constantCoefficient =
        parameters.constantCoefficient⁻¹ := by
    calc
      parameters.constantCoefficient⁻¹ ^ 2 *
          parameters.constantCoefficient =
        parameters.constantCoefficient⁻¹ *
          (parameters.constantCoefficient⁻¹ *
            parameters.constantCoefficient) := by ring1
      _ = parameters.constantCoefficient⁻¹ := by
        rw [reverseCancel, mul_one]
  calc
    parameters.constantCoefficient⁻¹ * parameters.dotCoefficient =
        (parameters.constantCoefficient⁻¹ ^ 2 *
          parameters.constantCoefficient) *
            parameters.dotCoefficient := by rw [inverseSquaredTimesConstant]
    _ = parameters.constantCoefficient⁻¹ ^ 2 *
        (parameters.constantCoefficient *
          parameters.dotCoefficient) := by ring1
    _ = parameters.constantCoefficient⁻¹ ^ 2 *
        (-(parameters.crossCoefficient ^ 2)) := by rw [coefficientRelation]
    _ = -(parameters.dilationFactor ^ 2) := by
      unfold Cayley.CoefficientProducts.CoefficientProductParameters.dilationFactor
      ring1

/-- Dilation transports the coefficient denominator to the anchor denominator by the inverse constant factor. -/
theorem CoefficientProductParameters.dilation_denominator
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2))
    (left right : Coordinates3.Vector K) :
    Cayley.Product.anchorProductDenominator
        (Coordinates3.Vector.scale parameters.dilationFactor left)
        (Coordinates3.Vector.scale parameters.dilationFactor right) =
      parameters.constantCoefficient⁻¹ *
        parameters.denominator left right := by
  have reverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  have normalized :=
    Purelib.Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.normalized_dotCoefficient
    parameters constantNonzero
    coefficientRelation
  unfold Cayley.Product.anchorProductDenominator Cayley.CoefficientProducts.CoefficientProductParameters.denominator
  rw [Coordinates3.Vector.dot_scale_left, Coordinates3.Vector.dot_scale_right]
  calc
    1 - parameters.dilationFactor *
        (parameters.dilationFactor * Coordinates3.Vector.dot left right) =
      parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient +
        (parameters.constantCoefficient⁻¹ *
          parameters.dotCoefficient) * Coordinates3.Vector.dot left right := by
            rw [reverseCancel, normalized]
            ring1
    _ = parameters.constantCoefficient⁻¹ *
        (parameters.constantCoefficient +
          parameters.dotCoefficient * Coordinates3.Vector.dot left right) := by ring1

/-- The dilated anchor product is defined whenever the classified coefficient product is defined. -/
theorem CoefficientProductParameters.dilationProductDefined
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2))
    (left right : Coordinates3.Vector K)
    (defined : parameters.denominator left right ≠ 0) :
    Cayley.Product.anchorProductDenominator
      (Coordinates3.Vector.scale parameters.dilationFactor left)
      (Coordinates3.Vector.scale parameters.dilationFactor right) ≠ 0 := by
  rw [parameters.dilation_denominator constantNonzero coefficientRelation]
  exact Algebra.Field.ExplicitField.mul_ne_zero
    (Algebra.Field.ExplicitField.inv_ne_zero constantNonzero) defined

/-- After multiplying the output by the dilation factor, every nondegenerate member of the classified family is
literally the opposite anchor product on dilated inputs. -/
theorem CoefficientProductParameters.dilation_product
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2))
    (left right : Coordinates3.Vector K)
    (defined : parameters.denominator left right ≠ 0) :
    Coordinates3.Vector.scale parameters.dilationFactor
        (parameters.product left right defined) =
      Cayley.Product.oppositeAnchorProduct
        (Coordinates3.Vector.scale parameters.dilationFactor left)
        (Coordinates3.Vector.scale parameters.dilationFactor right)
        (parameters.dilationProductDefined constantNonzero
          coefficientRelation left right defined) := by
  have denominatorRelation := parameters.dilation_denominator
    constantNonzero coefficientRelation left right
  have dilatedDefined := parameters.dilationProductDefined constantNonzero
    coefficientRelation left right defined
  have denominatorCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (parameters.denominator left right) defined
  have constantReverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  have dilatedInverse :
      (Cayley.Product.anchorProductDenominator
        (Coordinates3.Vector.scale parameters.dilationFactor left)
        (Coordinates3.Vector.scale parameters.dilationFactor right))⁻¹ =
      parameters.constantCoefficient *
        (parameters.denominator left right)⁻¹ := by
    apply
      Purelib.Algebra.Field.Inverse.inverse_eq_of_mul_eq_one
      dilatedDefined
    rw [denominatorRelation]
    calc
      parameters.constantCoefficient⁻¹ *
          parameters.denominator left right *
          (parameters.constantCoefficient *
            (parameters.denominator left right)⁻¹) =
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) *
          (parameters.denominator left right *
            (parameters.denominator left right)⁻¹) := by ring1
      _ = 1 := by rw [constantReverseCancel, denominatorCancel, one_mul]
  have factorTimesConstant := parameters.dilationFactor_mul_constant
    constantNonzero
  unfold Cayley.CoefficientProducts.CoefficientProductParameters.product Cayley.Product.oppositeAnchorProduct
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul]
  rw [dilatedInverse]
  apply Coordinates3.Vector.ext <;>
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.numerator
      Cayley.Product.oppositeAnchorProductNumerator Coordinates3.Vector.scale Coordinates3.Vector.add
      Coordinates3.Vector.cross <;>
    rw [leftCoefficient, rightCoefficient, ← factorTimesConstant] <;>
    ring1

/-- The nonzero-cross members of the homogeneous classified family are associative because dilation transports them to
the opposite anchor product. All domain certificates are transported by explicit denominator equalities. -/
theorem CoefficientProductParameters.associativeWhereDefined_of_coefficients_of_crossCoefficient_ne_zero
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (crossNonzero : parameters.crossCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2)) :
    parameters.AssociativeWhereDefined := by
  have factorNonzero : parameters.dilationFactor ≠ 0 := by
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.dilationFactor
    exact Algebra.Field.ExplicitField.mul_ne_zero crossNonzero
      (Algebra.Field.ExplicitField.inv_ne_zero constantNonzero)
  intro first second third firstSecondDefined secondThirdDefined leftDefined
    rightDefined
  let firstSecondDilatedDefined := parameters.dilationProductDefined
    constantNonzero coefficientRelation first second firstSecondDefined
  let secondThirdDilatedDefined := parameters.dilationProductDefined
    constantNonzero coefficientRelation second third secondThirdDefined
  let leftDilatedDefined : Cayley.Product.anchorProductDenominator
      (Cayley.Product.oppositeAnchorProduct
        (Coordinates3.Vector.scale parameters.dilationFactor first)
        (Coordinates3.Vector.scale parameters.dilationFactor second)
        firstSecondDilatedDefined)
      (Coordinates3.Vector.scale parameters.dilationFactor third) ≠ 0 := by
    have transported := parameters.dilationProductDefined constantNonzero
      coefficientRelation
      (parameters.product first second firstSecondDefined) third leftDefined
    rw [parameters.dilation_product constantNonzero leftCoefficient
      rightCoefficient coefficientRelation first second firstSecondDefined]
      at transported
    exact transported
  let rightDilatedDefined : Cayley.Product.anchorProductDenominator
      (Coordinates3.Vector.scale parameters.dilationFactor first)
      (Cayley.Product.oppositeAnchorProduct
        (Coordinates3.Vector.scale parameters.dilationFactor second)
        (Coordinates3.Vector.scale parameters.dilationFactor third)
        secondThirdDilatedDefined) ≠ 0 := by
    have transported := parameters.dilationProductDefined constantNonzero
      coefficientRelation first
      (parameters.product second third secondThirdDefined) rightDefined
    rw [parameters.dilation_product constantNonzero leftCoefficient
      rightCoefficient coefficientRelation second third secondThirdDefined]
      at transported
    exact transported
  have dilatedAssociation := Cayley.Product.oppositeAnchorProduct_associative
    (Coordinates3.Vector.scale parameters.dilationFactor first)
    (Coordinates3.Vector.scale parameters.dilationFactor second)
    (Coordinates3.Vector.scale parameters.dilationFactor third)
    firstSecondDilatedDefined secondThirdDilatedDefined leftDilatedDefined
    rightDilatedDefined
  have firstSecondDilated := parameters.dilation_product constantNonzero
    leftCoefficient rightCoefficient coefficientRelation first second
    firstSecondDefined
  have secondThirdDilated := parameters.dilation_product constantNonzero
    leftCoefficient rightCoefficient coefficientRelation second third
    secondThirdDefined
  have leftOuterDilated := parameters.dilation_product constantNonzero
    leftCoefficient rightCoefficient coefficientRelation
    (parameters.product first second firstSecondDefined) third leftDefined
  have rightOuterDilated := parameters.dilation_product constantNonzero
    leftCoefficient rightCoefficient coefficientRelation first
    (parameters.product second third secondThirdDefined) rightDefined
  apply
    Purelib.LinearAlgebra.Coordinates3.Vector.eq_of_scale_eq_scale
    factorNonzero
  calc
    Coordinates3.Vector.scale parameters.dilationFactor
        (parameters.product
          (parameters.product first second firstSecondDefined) third
            leftDefined) =
      Cayley.Product.oppositeAnchorProduct
        (Coordinates3.Vector.scale parameters.dilationFactor
          (parameters.product first second firstSecondDefined))
        (Coordinates3.Vector.scale parameters.dilationFactor third) _ := leftOuterDilated
    _ = Cayley.Product.oppositeAnchorProduct
        (Cayley.Product.oppositeAnchorProduct
          (Coordinates3.Vector.scale parameters.dilationFactor first)
          (Coordinates3.Vector.scale parameters.dilationFactor second)
          firstSecondDilatedDefined)
        (Coordinates3.Vector.scale parameters.dilationFactor third)
          leftDilatedDefined :=

        Purelib.Geometry.Rotations.Cayley.Product.oppositeAnchorProduct_congr_left
        firstSecondDilated _ _
    _ = Cayley.Product.oppositeAnchorProduct
        (Coordinates3.Vector.scale parameters.dilationFactor first)
        (Cayley.Product.oppositeAnchorProduct
          (Coordinates3.Vector.scale parameters.dilationFactor second)
          (Coordinates3.Vector.scale parameters.dilationFactor third)
          secondThirdDilatedDefined)
        rightDilatedDefined := dilatedAssociation
    _ = Cayley.Product.oppositeAnchorProduct
        (Coordinates3.Vector.scale parameters.dilationFactor first)
        (Coordinates3.Vector.scale parameters.dilationFactor
          (parameters.product second third secondThirdDefined)) _ :=

        Purelib.Geometry.Rotations.Cayley.Product.oppositeAnchorProduct_congr_right
        secondThirdDilated.symm _ _
    _ = Coordinates3.Vector.scale parameters.dilationFactor
        (parameters.product first
          (parameters.product second third secondThirdDefined)
            rightDefined) := rightOuterDilated.symm

/-- A unital coefficient product with zero cross and dot coefficients is vector addition. -/
private theorem
  CoefficientProductParameters.product_eq_add_of_cross_and_dot_zero
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient)
    (crossZero : parameters.crossCoefficient = 0)
    (dotZero : parameters.dotCoefficient = 0)
    (left right : Coordinates3.Vector K)
    (defined : parameters.denominator left right ≠ 0) :
    parameters.product left right defined = Coordinates3.Vector.add left right := by
  have reverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  apply Coordinates3.Vector.ext <;>
    unfold Cayley.CoefficientProducts.CoefficientProductParameters.product
      Cayley.CoefficientProducts.CoefficientProductParameters.numerator
      Cayley.CoefficientProducts.CoefficientProductParameters.denominator Coordinates3.Vector.scale
      Coordinates3.Vector.add Coordinates3.Vector.cross
      Coordinates3.Vector.dot <;>
    rw [leftCoefficient, rightCoefficient, crossZero, dotZero] <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul, zero_mul, add_zero, -eq_self, -iff_self]
  · calc
      parameters.constantCoefficient⁻¹ *
          (parameters.constantCoefficient * left.t +
            parameters.constantCoefficient * right.t) =
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * left.t +
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * right.t := by ring1
      _ = left.t + right.t := by simp only [reverseCancel, one_mul, -eq_self, -iff_self] ; rfl
  · calc
      parameters.constantCoefficient⁻¹ *
          (parameters.constantCoefficient * left.r +
            parameters.constantCoefficient * right.r) =
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * left.r +
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * right.r := by ring1
      _ = left.r + right.r := by simp only [reverseCancel, one_mul, -eq_self, -iff_self] ; rfl
  · calc
      parameters.constantCoefficient⁻¹ *
          (parameters.constantCoefficient * left.s +
            parameters.constantCoefficient * right.s) =
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * left.s +
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * right.s := by ring1
      _ = left.s + right.s := by simp only [reverseCancel, one_mul, -eq_self, -iff_self] ; rfl

/-- Complete sufficiency: with decidable equality, the zero-cross case is ordinary vector addition and the nonzero-cross
case is transported to the opposite anchor product by dilation. -/
theorem CoefficientProductParameters.associativeWhereDefined_of_coefficients [DecidableEq K]
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2)) :
    parameters.AssociativeWhereDefined := by
  by_cases crossZero : parameters.crossCoefficient = 0
  · have productRelation :
        parameters.constantCoefficient * parameters.dotCoefficient = 0 := by
      calc
        parameters.constantCoefficient * parameters.dotCoefficient =
            -(parameters.crossCoefficient ^ 2) := coefficientRelation
        _ = 0 := by rw [crossZero]; ring1
    have dotZero : parameters.dotCoefficient = 0 := by
      have constantCancel := Algebra.Field.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
      have reverseCancel : parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient = 1 := by
        calc
          parameters.constantCoefficient⁻¹ *
              parameters.constantCoefficient =
            parameters.constantCoefficient *
              parameters.constantCoefficient⁻¹ := by ring1
          _ = 1 := constantCancel
      calc
        parameters.dotCoefficient = 1 * parameters.dotCoefficient := by
          rw [one_mul]
        _ = (parameters.constantCoefficient⁻¹ *
            parameters.constantCoefficient) *
              parameters.dotCoefficient := by rw [reverseCancel]
        _ = parameters.constantCoefficient⁻¹ *
            (parameters.constantCoefficient *
              parameters.dotCoefficient) := by ring1
        _ = 0 := by rw [productRelation, mul_zero]
    intro first second third firstSecondDefined secondThirdDefined leftDefined
      rightDefined
    have firstSecondValue :=
      CoefficientProductParameters.product_eq_add_of_cross_and_dot_zero
      parameters
      constantNonzero leftCoefficient rightCoefficient crossZero dotZero first
      second firstSecondDefined
    have secondThirdValue :=
      CoefficientProductParameters.product_eq_add_of_cross_and_dot_zero
      parameters
      constantNonzero leftCoefficient rightCoefficient crossZero dotZero second
      third secondThirdDefined
    calc
      parameters.product
          (parameters.product first second firstSecondDefined) third
            leftDefined =
        Coordinates3.Vector.add (parameters.product first second firstSecondDefined) third :=

            CoefficientProductParameters.product_eq_add_of_cross_and_dot_zero
            parameters constantNonzero
            leftCoefficient rightCoefficient crossZero dotZero _ _ _
      _ = Coordinates3.Vector.add (Coordinates3.Vector.add first second) third :=
        congrArg (fun value => Coordinates3.Vector.add value third) firstSecondValue
      _ = Coordinates3.Vector.add first (Coordinates3.Vector.add second third) := by
        apply Coordinates3.Vector.ext <;> unfold Coordinates3.Vector.add <;> ring1
      _ = Coordinates3.Vector.add first
          (parameters.product second third secondThirdDefined) :=
        congrArg (Coordinates3.Vector.add first) secondThirdValue.symm
      _ = parameters.product first
          (parameters.product second third secondThirdDefined) rightDefined :=

          (CoefficientProductParameters.product_eq_add_of_cross_and_dot_zero
          parameters constantNonzero
          leftCoefficient rightCoefficient crossZero dotZero _ _ _).symm
  · exact
      parameters.associativeWhereDefined_of_coefficients_of_crossCoefficient_ne_zero
        constantNonzero crossZero leftCoefficient rightCoefficient
          coefficientRelation

/-- Hardened Conjecture 52 / Problem 68 over the paper's primary field. A homogeneous five-coefficient product is unital
and associative exactly when its two linear coefficients equal the nonzero denominator constant and its dot and cross
coefficients satisfy `ιδ = -γ²`. The necessity proof tests only the displayed probes `1` and, in the exceptional
denominator case, `2`. -/
theorem CoefficientProductParameters.rational_hardenedAssociativityClassification
    (parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters
      Fraction.Rational) :
    (parameters.HasZeroIdentity ∧ parameters.AssociativeWhereDefined) ↔
      parameters.constantCoefficient ≠ 0 ∧
      parameters.leftCoefficient = parameters.constantCoefficient ∧
      parameters.rightCoefficient = parameters.constantCoefficient ∧
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2) := by
  constructor
  · rintro ⟨identity, associative⟩
    refine ⟨identity.constantNonzero,
      parameters.leftCoefficient_eq_constant identity,
      parameters.rightCoefficient_eq_constant identity, ?_⟩
    by_cases firstProbeDefined :
        parameters.constantCoefficient +
          parameters.dotCoefficient * (1 :
            Fraction.Rational) ^ 2 ≠ 0
    · exact parameters.constant_mul_dotCoefficient_eq_neg_crossCoefficient_sq
        identity associative 1 (by decide) firstProbeDefined
    · have firstProbeZero :
          parameters.constantCoefficient +
            parameters.dotCoefficient * (1 :
              Fraction.Rational) ^ 2 = 0 := by
        exact Decidable.not_not.mp firstProbeDefined
      have secondProbeDefined :
          parameters.constantCoefficient +
            parameters.dotCoefficient * (2 :
              Fraction.Rational) ^ 2 ≠ 0 := by
        intro secondProbeZero
        have tripleConstantZero :
            (3 : Fraction.Rational) *
              parameters.constantCoefficient = 0 := by
          calc
            (3 : Fraction.Rational) *
                parameters.constantCoefficient =
              4 * (parameters.constantCoefficient +
                parameters.dotCoefficient * 1 ^ 2) -
              (parameters.constantCoefficient +
                parameters.dotCoefficient * 2 ^ 2) := by ring1
            _ = 0 := by rw [firstProbeZero, secondProbeZero]; ring1
        exact Algebra.Field.ExplicitField.mul_ne_zero (by decide)
          identity.constantNonzero tripleConstantZero
      exact parameters.constant_mul_dotCoefficient_eq_neg_crossCoefficient_sq
        identity associative 2 (by decide) secondProbeDefined
  · rintro ⟨constantNonzero, leftCoefficient, rightCoefficient,
      coefficientRelation⟩
    exact
      ⟨parameters.hasZeroIdentity_of_coefficients constantNonzero
          leftCoefficient rightCoefficient,
        parameters.associativeWhereDefined_of_coefficients constantNonzero
          leftCoefficient rightCoefficient coefficientRelation⟩

/-- Equality up to global nonzero rescaling of the five homogeneous coefficients. -/
def CoefficientProductParameters.Equivalent (left right : CoefficientProductParameters K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    right.leftCoefficient = factor * left.leftCoefficient ∧
    right.rightCoefficient = factor * left.rightCoefficient ∧
    right.crossCoefficient = factor * left.crossCoefficient ∧
    right.constantCoefficient = factor * left.constantCoefficient ∧
    right.dotCoefficient = factor * left.dotCoefficient

/-- The anchor product `(v+u-v×u)/(1-v·u)`. -/
def CoefficientProductParameters.anchorParameters : CoefficientProductParameters K :=
  ⟨1, 1, -1, 1, -1⟩

/-- The opposite product `(v+u+v×u)/(1-v·u)`. -/
def CoefficientProductParameters.oppositeParameters : CoefficientProductParameters K :=
  ⟨1, 1, 1, 1, -1⟩

/-- The literal statement of Conjecture 52 (and Problem 68) in homogeneous coefficient form. -/
def CoefficientProductParameters.AssociativityConjecture : Prop :=
  ∀ parameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K,
    parameters.AssociativeWhereDefined →
      parameters.Equivalent Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.anchorParameters
        ∨
        parameters.Equivalent
          Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.oppositeParameters

/-- A degenerate member of the displayed family: `v ⋆ u = v`. -/
def CoefficientProductParameters.leftProjectionParameters : CoefficientProductParameters K :=
  ⟨1, 0, 0, 1, 0⟩

open Purelib.Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters
/-- The left-projection coefficient family has constant denominator one. -/
theorem CoefficientProductParameters.leftProjection_denominator (left right : Coordinates3.Vector K) :
    leftProjectionParameters.denominator left right = 1 := by
  unfold leftProjectionParameters Cayley.CoefficientProducts.CoefficientProductParameters.denominator
  ring1

/-- The left-projection coefficient product returns its left input. -/
theorem CoefficientProductParameters.leftProjection_product (left right : Coordinates3.Vector K)
    (defined : leftProjectionParameters.denominator left right ≠ 0) :
    leftProjectionParameters.product left right defined = left := by
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (leftProjectionParameters.denominator left right) defined
  rw [Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_denominator] at cancel
  have inverseOne : (1 : K)⁻¹ = 1 := by
    simpa only [one_mul] using cancel
  unfold Cayley.CoefficientProducts.CoefficientProductParameters.product
  rw [Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_denominator,
    Algebra.Field.ExplicitField.div_eq_mul_inv,
    one_mul, inverseOne]
  apply Coordinates3.Vector.ext <;> unfold Cayley.CoefficientProducts.CoefficientProductParameters.numerator
    leftProjectionParameters Coordinates3.Vector.scale
    Coordinates3.Vector.add Coordinates3.Vector.cross <;> ring1

/-- The left-projection coefficient product is associative wherever defined. -/
theorem CoefficientProductParameters.leftProjection_associative :
    Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.AssociativeWhereDefined
      (leftProjectionParameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K) := by
  intro first second third firstSecondDefined secondThirdDefined leftDefined
    rightDefined
  rw [Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_product,
    Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_product,
    Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_product]

/-- The left-projection coefficients cannot be a nonzero homogeneous rescaling of the anchor coefficients. -/
theorem CoefficientProductParameters.leftProjection_not_equivalent_anchor (twoNonzero : (2 : K) ≠ 0) :
    ¬ (leftProjectionParameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters
      K).Equivalent
      anchorParameters := by
  rintro ⟨factor, _, _, rightCoefficient, _⟩
  apply
    Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero
    twoNonzero
  calc
    (1 : K) = factor * 0 := rightCoefficient
    _ = 0 := by ring1

/-- The left-projection coefficients cannot be a nonzero homogeneous rescaling of the opposite anchor coefficients. -/
theorem CoefficientProductParameters.leftProjection_not_equivalent_opposite
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ (leftProjectionParameters : Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters
      K).Equivalent
      oppositeParameters := by
  rintro ⟨factor, _, _, rightCoefficient, _⟩
  apply
    Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero
    twoNonzero
  calc
    (1 : K) = factor * 0 := rightCoefficient
    _ = 0 := by ring1

/-- Conjecture 52 is false as printed unless degenerate coefficient families such as projections are excluded. -/
theorem CoefficientProductParameters.associativityConjecture_false (twoNonzero : (2 : K) ≠ 0) :
    ¬ (@Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.AssociativityConjecture K _) := by
  intro conjecture
  rcases conjecture leftProjectionParameters leftProjection_associative with
    anchorCase | oppositeCase
  · exact
      Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_not_equivalent_anchor
      twoNonzero anchorCase
  · exact
      Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_not_equivalent_opposite
      twoNonzero oppositeCase

end CoefficientProductParameters

/-! ### The exact normalized family printed in Conjecture 52 -/

set_option genInjectivity false in
/-- The four coefficients in the paper's normalized expression `(αv + βu + γ(v × u)) / (1 + δ(v · u))`. -/
@[ext]
structure NormalizedCoefficientProductParameters (K : Type*) where
  /-- The scalar multiplying the left input vector. -/ leftCoefficient : K
  /-- The scalar multiplying the right input vector. -/ rightCoefficient : K
  /-- The scalar multiplying the cross product of the inputs. -/ crossCoefficient : K
  /-- The scalar multiplying the input dot product in the denominator. -/ dotCoefficient : K

constructive_injectivity NormalizedCoefficientProductParameters

section NormalizedCoefficientProductParameters

/-- Embed the paper's constant-denominator-one family into the homogeneous five-coefficient family. -/
def NormalizedCoefficientProductParameters.toHomogeneous (parameters : NormalizedCoefficientProductParameters K)
  :
    Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters K :=
  ⟨parameters.leftCoefficient, parameters.rightCoefficient,
    parameters.crossCoefficient, 1, parameters.dotCoefficient⟩

/-- The exact normalized form of Conjecture 52 and Problem 68. -/
def NormalizedCoefficientProductParameters.AssociativityConjecture : Prop :=
  ∀ parameters : Geometry.Rotations.Cayley.CoefficientProducts.NormalizedCoefficientProductParameters K,
    parameters.toHomogeneous.AssociativeWhereDefined →
      parameters.toHomogeneous.Equivalent
          Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.anchorParameters ∨
        parameters.toHomogeneous.Equivalent
          Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.oppositeParameters

/-- The normalized left projection `v ⋆ u = v`; unlike a counterexample with zero constant denominator, this lies
literally in the family printed in the paper. -/
def NormalizedCoefficientProductParameters.leftProjection : NormalizedCoefficientProductParameters K :=
  ⟨1, 0, 0, 0⟩

open Purelib.Geometry.Rotations.Cayley.CoefficientProducts.NormalizedCoefficientProductParameters
/-- Embedding the normalized left projection gives the homogeneous left-projection coefficients. -/
theorem NormalizedCoefficientProductParameters.leftProjection_toHomogeneous :
    (leftProjection : Geometry.Rotations.Cayley.CoefficientProducts.NormalizedCoefficientProductParameters
      K).toHomogeneous =
      CoefficientProductParameters.leftProjectionParameters := rfl

/-- The left-projection coefficient product is associative wherever defined. -/
theorem NormalizedCoefficientProductParameters.leftProjection_associative :
    Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.AssociativeWhereDefined
      (leftProjection : Geometry.Rotations.Cayley.CoefficientProducts.NormalizedCoefficientProductParameters
        K).toHomogeneous := by
  rw [Geometry.Rotations.Cayley.CoefficientProducts.NormalizedCoefficientProductParameters.leftProjection_toHomogeneous]
  exact Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_associative

/-- Conjecture 52 and Problem 68 are false in their exact normalized four-coefficient form. -/
theorem NormalizedCoefficientProductParameters.associativityConjecture_false (twoNonzero : (2 : K) ≠ 0) :
    ¬ (@Geometry.Rotations.Cayley.CoefficientProducts.NormalizedCoefficientProductParameters.AssociativityConjecture K
      _) := by
  intro conjecture
  rcases conjecture leftProjection leftProjection_associative with
    anchorCase | oppositeCase
  · rw
      [leftProjection_toHomogeneous]
      at anchorCase
    exact
      Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_not_equivalent_anchor
      twoNonzero anchorCase
  · rw
      [leftProjection_toHomogeneous]
      at oppositeCase
    exact
      Geometry.Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.leftProjection_not_equivalent_opposite
      twoNonzero oppositeCase

end NormalizedCoefficientProductParameters

section ConjectureFiftyTwoNumerics

/-- The constructive rational field of the displayed coefficient-product examples. -/
abbrev ConjectureFiftyTwoNumerics.Scalar := Fraction.Rational

/-- The displayed rational vector `(1,2,3)`. -/
def ConjectureFiftyTwoNumerics.first : Coordinates3.Vector Scalar := ⟨1, 2, 3⟩
/-- The displayed rational vector `(5,1,2)`. -/
def ConjectureFiftyTwoNumerics.second : Coordinates3.Vector Scalar := ⟨5, 1, 2⟩
/-- The displayed rational vector `(-3,4,1)`. -/
def ConjectureFiftyTwoNumerics.third : Coordinates3.Vector Scalar := ⟨-3, 4, 1⟩

/-- The paper's variant with denominator `1+v·u`. -/
def ConjectureFiftyTwoNumerics.plusDenominator : CoefficientProductParameters Scalar :=
  ⟨1, 1, -1, 1, 1⟩

section
open Purelib.Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics
/-- The first and second displayed vectors have a defined product for the positive-dot-denominator coefficient family.
-/
theorem ConjectureFiftyTwoNumerics.plus_firstSecond_defined :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.denominator first second ≠
      0 := by decide

/-- The second and third displayed vectors have a defined product for the positive-dot-denominator coefficient family.
-/
theorem ConjectureFiftyTwoNumerics.plus_secondThird_defined :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.denominator second third ≠
      0 := by decide

/-- The left-nested product of the three displayed vectors is defined for the positive-dot-denominator coefficient
family. -/
theorem ConjectureFiftyTwoNumerics.plus_left_defined :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.denominator
      (Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.product first second
        Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plus_firstSecond_defined) third ≠
        0 := by decide

/-- The right-nested product of the three displayed vectors is defined for the positive-dot-denominator coefficient
family. -/
theorem ConjectureFiftyTwoNumerics.plus_right_defined :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.denominator first
      (Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.product second third
        Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plus_secondThird_defined) ≠ 0 := by
  decide

/-- The coefficient family with denominator `1 + v·u` fails associativity on the three displayed rational vectors. -/
theorem ConjectureFiftyTwoNumerics.plusDenominator_not_associative_on_displayed_triple :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.product
        (Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.product first second
          Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plus_firstSecond_defined) third
          Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plus_left_defined ≠
      Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.product first
        (Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plusDenominator.product second third
          Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.plus_secondThird_defined)
          plus_right_defined := by decide

end

/-- The paper's variant with cross coefficient two. -/
def ConjectureFiftyTwoNumerics.doubleCross : CoefficientProductParameters Scalar :=
  ⟨1, 1, 2, 1, -1⟩

open Purelib.Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics
/-- The first and second displayed vectors have a defined product for the doubled-cross coefficient family. -/
theorem ConjectureFiftyTwoNumerics.double_firstSecond_defined :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.denominator first second ≠ 0 :=
      by decide

/-- The second and third displayed vectors have a defined product for the doubled-cross coefficient family. -/
theorem ConjectureFiftyTwoNumerics.double_secondThird_defined :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.denominator second third ≠ 0 :=
      by decide

/-- The left-nested product of the three displayed vectors is defined for the doubled-cross coefficient family. -/
theorem ConjectureFiftyTwoNumerics.double_left_defined :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.denominator
      (Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.product first second
        Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.double_firstSecond_defined) third ≠ 0
        := by
  decide

/-- The right-nested product of the three displayed vectors is defined for the doubled-cross coefficient family. -/
theorem ConjectureFiftyTwoNumerics.double_right_defined :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.denominator first
      (Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.product second third
        Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.double_secondThird_defined) ≠ 0 := by
  decide

/-- The coefficient family with doubled cross term fails associativity on the three displayed rational vectors. -/
theorem ConjectureFiftyTwoNumerics.doubleCross_not_associative_on_displayed_triple :
    Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.product
        (Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.product first second
          Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.double_firstSecond_defined) third
          Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.double_left_defined ≠
      Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.product first
        (Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.doubleCross.product second third
          Geometry.Rotations.Cayley.CoefficientProducts.ConjectureFiftyTwoNumerics.double_secondThird_defined)
          double_right_defined := by decide

end ConjectureFiftyTwoNumerics

end Purelib.Geometry.Rotations.Cayley.CoefficientProducts
