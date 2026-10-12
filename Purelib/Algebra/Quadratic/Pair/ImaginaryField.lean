module

public import Purelib.Algebra.Quadratic.Pair.Basic
public import Purelib.Algebra.Field.Squares
public import Purelib.Algebra.Field.Embedding
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Inverse
import Purelib.Tactic.Ring

/-!
# The quadratic field with a formal square root of negative one

The carrier and ring operations are the original two-coordinate `Pair K 1`.
A supplied exclusion of square roots of negative one certifies its nonzero
norms. Its computed conjugate-over-norm inverse extends those same operations.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.ImaginaryField

open Purelib.Algebra.Field
open Purelib.Algebra.Field.Characteristic.Nonzero (one_ne_zero_of_nonzero)

variable {K : Type*} [ExplicitField K]

/-- Every nonzero imaginary quadratic pair has nonzero quadrance when negative one has no square root.

A nonzero imaginary coordinate would turn zero quadrance into a square root
of negative one by division. Otherwise its nonzero real coordinate has a
nonzero square.
-/
theorem quadrance_ne_zero [DecidableEq K] (noRoot : Squares.NoSquareRootOfNegativeOne (K := K))
    (value : Pair K (1 : K)) (nonzero : value ≠ 0) : value.quadrance ≠ 0 := by
  intro null
  by_cases imaginaryZero : value.im = 0
  · have realNonzero : value.re ≠ 0 := by
      intro realZero
      exact nonzero (Pair.ext realZero imaginaryZero)
    have realSquareZero : value.re ^ 2 = 0 := by
      calc
        value.re ^ 2 = value.quadrance := by unfold Pair.quadrance; rw [imaginaryZero]; ring1
        _ = 0 := null
    exact ExplicitField.square_nonzero_of_nonzero realNonzero realSquareZero
  · apply noRoot (value.re / value.im)
    have cancel := ExplicitField.mul_inv_cancel value.im imaginaryZero
    have realSquare : value.re ^ 2 = -(value.im ^ 2) := by
      calc
        value.re ^ 2 = value.quadrance - value.im ^ 2 := by unfold Pair.quadrance; ring1
        _ = -(value.im ^ 2) := by rw [null]; ring1
    rw [ExplicitField.div_eq_mul_inv]
    calc
      (value.re * value.im⁻¹) ^ 2 = value.re ^ 2 * (value.im⁻¹) ^ 2 := by ring1
      _ = -(value.im ^ 2 * (value.im⁻¹) ^ 2) := by rw [realSquare]; ring1
      _ = -((value.im * value.im⁻¹) ^ 2) := by ring1
      _ = -1 := by rw [cancel]; ring1

/-- Compute the inverse of an imaginary quadratic pair by scaling its conjugate by inverse quadrance. -/
@[expose] def inverse (value : Pair K (1 : K)) : Pair K (1 : K) :=
  Pair.scale value.quadrance⁻¹ value.conjugate

/-- A nonzero imaginary quadratic pair times its computed inverse is one. -/
theorem mul_inverse [DecidableEq K] (noRoot : Squares.NoSquareRootOfNegativeOne (K := K))
    (value : Pair K (1 : K)) (nonzero : value ≠ 0) : value * inverse value = 1 := by
  have cancel := ExplicitField.mul_inv_cancel value.quadrance (quadrance_ne_zero noRoot value nonzero)
  apply Pair.ext
  · change value.re * (value.quadrance⁻¹ * value.re) -
        1 * value.im * (value.quadrance⁻¹ * -value.im) = 1
    calc
      _ = value.quadrance * value.quadrance⁻¹ := by unfold Pair.quadrance; ring1
      _ = 1 := cancel
  · change value.re * (value.quadrance⁻¹ * -value.im) +
      value.im * (value.quadrance⁻¹ * value.re) = 0
    ring1

/-- Products of nonzero imaginary quadratic pairs remain nonzero.

The original pair quadrance is multiplicative. Its two input quadrances are
nonzero, so a zero product would contradict the base field's nonzero-product law.
-/
theorem mul_ne_zero [DecidableEq K] (noRoot : Squares.NoSquareRootOfNegativeOne (K := K))
    {left right : Pair K (1 : K)} (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) : left * right ≠ 0 := by
  have normsNonzero := ExplicitField.mul_ne_zero
    (quadrance_ne_zero noRoot left leftNonzero) (quadrance_ne_zero noRoot right rightNonzero)
  intro productZero
  apply normsNonzero
  calc
    left.quadrance * right.quadrance = (left * right).quadrance := (Pair.quadrance_mul left right).symm
    _ = (0 : Pair K (1 : K)).quadrance := congrArg Pair.quadrance productZero
    _ = 0 := by change (0 : K) ^ 2 + 0 ^ 2 = 0; ring1

/-- Inverting a nonzero imaginary quadratic pair gives a nonzero pair. -/
theorem inverse_ne_zero [DecidableEq K] (noRoot : Squares.NoSquareRootOfNegativeOne (K := K))
    (twoNonzero : (2 : K) ≠ 0) {value : Pair K (1 : K)} (nonzero : value ≠ 0) : inverse value ≠ 0 := by
  intro inverseZero
  have cancel := mul_inverse noRoot value nonzero
  rw [inverseZero, mul_zero] at cancel
  exact one_ne_zero_of_nonzero twoNonzero (congrArg Pair.re cancel).symm

/-- Negating an imaginary quadratic pair leaves its quadrance unchanged. -/
theorem quadrance_neg (value : Pair K (1 : K)) : (-value).quadrance = value.quadrance := by
  unfold Pair.quadrance
  simp only [Pair.neg_re, Pair.neg_im, -eq_self, -iff_self]
  ring1

/-- The computed imaginary quadratic inverse commutes with negation. -/
theorem inverse_neg (value : Pair K (1 : K)) : inverse (-value) = -inverse value := by
  apply Pair.ext <;>
    simp only [inverse, Pair.scale, Pair.conjugate, Pair.neg_re, Pair.neg_im, quadrance_neg,
      -eq_self, -iff_self] <;> ring1

/-- Equip the original imaginary quadratic pair ring with its certified explicit field operations.

The original commutative-ring record is retained literally. Inverse is the
computed conjugate-over-quadrance function, and division multiplies by it.
The root exclusion and nonzero two certify these operations without a global
replacement instance.
-/
@[expose, implicit_reducible] def explicitField [DecidableEq K] (noRoot : Squares.NoSquareRootOfNegativeOne (K := K))
    (twoNonzero : (2 : K) ≠ 0) : ExplicitField (Pair K (1 : K)) where
  toCommRing := Pair.instCommRing
  toInv := ⟨inverse⟩
  toDiv := ⟨fun left right => left * inverse right⟩
  div_eq_mul_inv := fun _ _ => rfl
  mul_inv_cancel := mul_inverse noRoot
  mul_ne_zero := mul_ne_zero noRoot
  inv_ne_zero := inverse_ne_zero noRoot twoNonzero
  inv_neg := inverse_neg

/-- Scalar pairs preserve the total inverse of the base field when two is nonzero.

At zero, the inverse-negation law forces the base inverse to vanish. At a
nonzero scalar, square inversion and scalar cancellation identify the real
coordinate of the original conjugate-over-quadrance inverse.
-/
theorem scalar_inverse [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) (value : K) :
    Pair.scalar value⁻¹ = inverse (Pair.scalar value : Pair K (1 : K)) := by
  by_cases zero : value = 0
  · rw [zero, ExplicitField.inverse_zero_of_two_ne_zero twoNonzero]
    apply Pair.ext <;> unfold Pair.scalar inverse Pair.scale Pair.conjugate <;> ring1
  · have cancel := ExplicitField.mul_inv_cancel value zero
    have norm : (Pair.scalar value : Pair K (1 : K)).quadrance = value ^ 2 := by
      unfold Pair.scalar Pair.quadrance
      ring1
    apply Pair.ext
    · change value⁻¹ = (Pair.scalar value : Pair K (1 : K)).quadrance⁻¹ * value
      rw [norm, Inverse.inverse_square zero]
      calc
        value⁻¹ = (value * value⁻¹) * value⁻¹ := by rw [cancel]; ring1
        _ = value⁻¹ ^ 2 * value := by ring1
    · change (0 : K) = (Pair.scalar value : Pair K (1 : K)).quadrance⁻¹ * -0
      ring1

/-- The original scalar-pair map embeds the base field in its imaginary quadratic field.

The map is injective by real-coordinate readback and preserves all retained
field operations, including total inverse. The target field is the explicitly
supplied field on the original pair carrier.
-/
@[expose] def scalarEmbedding [DecidableEq K] (noRoot : Squares.NoSquareRootOfNegativeOne (K := K))
    (twoNonzero : (2 : K) ≠ 0) :
    letI := explicitField noRoot twoNonzero
    Embedding K (Pair K (1 : K)) := by
  letI := explicitField noRoot twoNonzero
  exact
    { toFun := Pair.scalar
      injective := fun _ _ equal => congrArg Pair.re equal
      map_zero := Pair.scalar_zero
      map_one := Pair.scalar_one
      map_add := Pair.scalar_add
      map_neg := Pair.scalar_neg
      map_mul := Pair.scalar_mul
      map_inv := scalar_inverse twoNonzero }

/-- The original pair generator squares to negative one. -/
theorem generator_square : (Pair.generator : Pair K (1 : K)) ^ 2 = -1 := by
  calc
    (Pair.generator : Pair K (1 : K)) ^ 2 = Pair.scalar (-1) := Pair.generator_square
    _ = -(Pair.scalar 1 : Pair K (1 : K)) := Pair.scalar_neg 1
    _ = -1 := congrArg Neg.neg Pair.scalar_one

/-- The imaginary generator is distinct from every embedded scalar when two is nonzero. -/
theorem generator_ne_scalar (twoNonzero : (2 : K) ≠ 0) (value : K) :
    (Pair.generator : Pair K (1 : K)) ≠ Pair.scalar value := by
  intro equal
  exact one_ne_zero_of_nonzero twoNonzero (congrArg Pair.im equal)

/-- Nonzero two in the base field remains nonzero in the original pair ring. -/
theorem two_ne_zero (twoNonzero : (2 : K) ≠ 0) : (2 : Pair K (1 : K)) ≠ 0 := by
  intro zero
  have realZero := congrArg Pair.re zero
  rw [Pair.two_eq_scalar] at realZero
  exact twoNonzero realZero

/-- The imaginary pair generator is nonzero when two in the base field is nonzero. -/
theorem generator_ne_zero (twoNonzero : (2 : K) ≠ 0) : (Pair.generator : Pair K (1 : K)) ≠ 0 := by
  intro zero
  exact one_ne_zero_of_nonzero twoNonzero (congrArg Pair.im zero)

end Purelib.Algebra.Quadratic.Pair.ImaginaryField
