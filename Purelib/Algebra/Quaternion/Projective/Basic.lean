module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.ExplicitOrder.Sign
public import Purelib.Algebra.Field.Embedding
import Purelib.Algebra.Group.Negation
public import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Displayed projective quaternion proportions

Quaternion coordinates retain a scalar and a three-vector over the supplied
explicit field. Homogeneous equivalence keeps its exact nonzero scale witness,
and non-null proportions retain the norm certificates used by their operations.
-/

namespace Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Algebra.Field
open Purelib.Algebra.Field.ExplicitOrder.Basic
open Purelib.Algebra.Field.ExplicitOrder.Sign
open Purelib.Algebra.Quaternion
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

public section

variable {K : Type*} [ExplicitField K]

@[expose] public section

set_option genInjectivity false in
/-- Four displayed quaternion coordinates stored as a scalar and three-vector.

The record represents homogeneous coordinates without forming a quotient or choosing a normalization. -/
@[ext]
structure Proportion (K : Type*) where
  /-- The retained scalar quaternion coordinate. -/ scalar : K
  /-- The retained three imaginary quaternion coordinates. -/ vector : Vector3 K
deriving DecidableEq

constructive_injectivity Proportion

end

namespace Proportion

/-- The quaternion proportion with all four coordinates zero. -/
@[expose] def zero : Proportion K := ⟨0, Vector3.zero⟩

/-- Compute the sum of the four quaternion coordinate squares.

The scalar square is added to the retained vector quadrance. -/
@[expose] def norm (proportion : Proportion K) : K :=
  proportion.scalar ^ 2 + proportion.vector.quadrance

/-- The displayed proportion differs from the zero quadruple. -/
@[expose] def IsNonzero (proportion : Proportion K) : Prop := proportion ≠ zero

/-- The displayed proportion has zero quaternion norm. -/
@[expose] def IsNull (proportion : Proportion K) : Prop := proportion.norm = 0

/-- Multiply all four displayed quaternion coordinates by the supplied scalar. -/
@[expose] def scale (factor : K) (proportion : Proportion K) : Proportion K :=
  ⟨factor * proportion.scalar, Vector3.scale factor proportion.vector⟩

/-- Two proportions differ by a displayed nonzero homogeneous scale.

The existential retains the scale, its nonzero certificate, and the exact equality of the scaled coordinates. -/
@[expose] def Equivalent (left right : Proportion K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧ right = Proportion.scale factor left

/-- Scaling a proportion by one preserves its coordinates.

Left-unit multiplication preserves the scalar coordinate, and vector scaling
by one preserves the retained three-coordinate vector. -/
@[simp] theorem one_scale (proportion : Proportion K) :
    Proportion.scale 1 proportion = proportion := by
  apply Proportion.ext
  · exact one_mul proportion.scalar
  · exact Vector3.one_scale proportion.vector

/-- Two successive homogeneous scalings combine by multiplying their factors.

Scalar associativity identifies the scalar coordinate, and the same factor identity applies to each retained vector
coordinate. -/
theorem scale_scale (first second : K) (proportion : Proportion K) :
    Proportion.scale first (Proportion.scale second proportion) =
      Proportion.scale (first * second) proportion := by
  apply Proportion.ext
  · unfold Proportion.scale
    ring1
  · unfold Proportion.scale
    rw [Vector3.scale_scale]

/-- The zero quaternion proportion has zero norm. -/
theorem norm_zero : Proportion.norm (zero : Proportion K) = 0 := by
  unfold Proportion.norm zero
  rw [Vector3.quadrance_zero]
  ring1

/-- Scaling a proportion multiplies its norm by the square of the scale.

The scalar square and the three vector coordinate squares share the same scale factor. Their sum is multiplied by its
square. -/
theorem norm_scale (factor : K) (proportion : Proportion K) :
    Proportion.norm (Proportion.scale factor proportion) = factor ^ 2 * Proportion.norm proportion := by
  unfold Proportion.norm Proportion.scale
  rw [Vector3.quadrance_scale]
  ring1

/-- Multiply displayed quaternion proportions in scalar-vector coordinates.

The scalar part subtracts the vector dot product, while the vector part combines the scalar multiples and subtracts the
left-right cross product. -/
@[expose] def mul (left right : Proportion K) : Proportion K :=
  ⟨left.scalar * right.scalar - Vector3.dot left.vector right.vector,
    Vector3.sub
      (Vector3.add
        (Vector3.scale left.scalar right.vector)
        (Vector3.scale right.scalar left.vector))
      (Vector3.cross left.vector right.vector)⟩

/-- Quaternion norm preserves the displayed proportion product.

The equality is the four-square product identity in the eight input coordinates. -/
theorem norm_mul (left right : Proportion K) :
    Proportion.norm (Proportion.mul left right) = Proportion.norm left * Proportion.norm right := by
  unfold Proportion.norm Proportion.mul Vector3.quadrance Vector3.dot Vector3.sub Vector3.add
    Vector3.scale Vector3.cross
  ring1

/-- Scaling both product inputs scales the result by the product of the factors.

The left and right homogeneous scales are independent. -/
theorem mul_scale_both (leftFactor rightFactor : K)
    (left right : Proportion K) :
    Proportion.mul (Proportion.scale leftFactor left) (Proportion.scale rightFactor right) =
      Proportion.scale (leftFactor * rightFactor) (Proportion.mul left right) := by
  apply Proportion.ext
  · unfold Proportion.mul Proportion.scale
    simp only [Vector3.dot_scale_left, Vector3.dot_scale_right]
    ring1
  · apply Vector3.ext <;> unfold Proportion.mul Proportion.scale Vector3.scale Vector3.sub Vector3.add
      Vector3.cross <;> ring1

/-- Multiplication of displayed quaternion proportions is associative.

The scalar-vector multiplication law gives the same four coordinates for both associations, using the finite dot and
cross product identities. -/
theorem mul_assoc (first second third : Proportion K) :
    Proportion.mul (Proportion.mul first second) third = Proportion.mul first (Proportion.mul second third) := by
  apply Proportion.ext
  · unfold Proportion.mul Vector3.dot Vector3.sub Vector3.add Vector3.scale Vector3.cross
    ring1
  · apply Vector3.ext <;> unfold Proportion.mul Vector3.dot Vector3.sub Vector3.add
      Vector3.scale Vector3.cross <;> ring1

/-- The unit quaternion proportion has scalar one and zero vector. -/
@[expose] def identity : Proportion K := ⟨1, Vector3.zero⟩

/-- The unit proportion is a left identity for quaternion multiplication. -/
@[simp] theorem identity_mul (proportion : Proportion K) :
    Proportion.mul Proportion.identity proportion = proportion := by
  apply Proportion.ext
  · unfold Proportion.mul Proportion.identity
    rw [Vector3.dot_zero_left]
    ring1
  · apply Vector3.ext <;> unfold Proportion.mul Proportion.identity Vector3.zero Vector3.sub
      Vector3.add Vector3.scale Vector3.cross <;> ring1

/-- The unit proportion is a right identity for quaternion multiplication. -/
@[simp] theorem mul_identity (proportion : Proportion K) :
    Proportion.mul proportion Proportion.identity = proportion := by
  apply Proportion.ext
  · unfold Proportion.mul Proportion.identity
    rw [Vector3.dot_zero_right]
    ring1
  · apply Vector3.ext <;> unfold Proportion.mul Proportion.identity Vector3.zero Vector3.sub
      Vector3.add Vector3.scale Vector3.cross <;> ring1

/-- Conjugate a quaternion proportion by negating its vector coordinate. -/
@[expose] def conjugate (proportion : Proportion K) : Proportion K :=
  ⟨proportion.scalar, Vector3.neg proportion.vector⟩

/-- Conjugating a quaternion proportion twice returns the original coordinates. -/
@[simp] theorem conjugate_conjugate (proportion : Proportion K) :
    Proportion.conjugate (Proportion.conjugate proportion) = proportion := by
  apply Proportion.ext
  · rfl
  · apply Vector3.ext <;> unfold Proportion.conjugate Vector3.neg <;> ring1

/-- Quaternion conjugation reverses the order of multiplication.

Negating the vector coordinate changes the sign of the cross product. The scalar coordinate is preserved, giving the
displayed reversed product. -/
theorem conjugate_mul_reverse (left right : Proportion K) :
    Proportion.conjugate (Proportion.mul left right) = Proportion.mul (Proportion.conjugate right) (Proportion.conjugate
      left) := by
  apply Proportion.ext
  · unfold Proportion.conjugate Proportion.mul Vector3.dot Vector3.neg
    ring1
  · apply Vector3.ext <;>
      unfold Proportion.conjugate Proportion.mul Vector3.dot Vector3.neg Vector3.sub Vector3.add
        Vector3.scale Vector3.cross <;> ring1

/-- Quaternion conjugation preserves the norm.

The scalar coordinate is unchanged and each vector coordinate is negated. Their four squares therefore have the same
sum. -/
theorem norm_conjugate (proportion : Proportion K) :
    Proportion.norm (Proportion.conjugate proportion) = Proportion.norm proportion := by
  unfold Proportion.norm Proportion.conjugate
  rw [Vector3.quadrance_neg]

/-- A proportion times its conjugate is its norm times the unit proportion.

The product has the sum of the four coordinate squares as scalar coordinate and zero vector coordinate. -/
theorem mul_conjugate (proportion : Proportion K) :
    Proportion.mul proportion (Proportion.conjugate proportion) =
      Proportion.scale (Proportion.norm proportion) identity := by
  apply Proportion.ext
  · unfold Proportion.mul Proportion.conjugate Proportion.scale Proportion.identity Proportion.norm Vector3.quadrance
      Vector3.dot
      Vector3.neg
    ring1
  · apply Vector3.ext <;> unfold Proportion.mul Proportion.conjugate Proportion.scale Proportion.identity
      Proportion.norm
      Vector3.quadrance Vector3.dot Vector3.zero Vector3.neg Vector3.sub Vector3.add
      Vector3.scale Vector3.cross <;> ring1

/-- A conjugate times its original proportion is the norm times the unit proportion.

The reversed conjugate product has the same scalar norm and zero vector coordinate, with no division or normalization.
-/
theorem conjugate_mul (proportion : Proportion K) :
    Proportion.mul (Proportion.conjugate proportion) proportion =
      Proportion.scale (Proportion.norm proportion) identity := by
  apply Proportion.ext
  · unfold Proportion.mul Proportion.conjugate Proportion.scale Proportion.identity Proportion.norm Vector3.quadrance
      Vector3.dot
      Vector3.neg
    ring1
  · apply Vector3.ext <;> unfold Proportion.mul Proportion.conjugate Proportion.scale Proportion.identity
      Proportion.norm
      Vector3.quadrance Vector3.dot Vector3.zero Vector3.neg Vector3.sub Vector3.add
      Vector3.scale Vector3.cross <;> ring1

/-- Add two quaternion coordinate vectors componentwise. -/
@[expose] def add (left right : Proportion K) : Proportion K :=
  ⟨left.scalar + right.scalar, Vector3.add left.vector right.vector⟩

/-- Embed a scalar as a quaternion with zero vector coordinate. -/
@[expose] def ofScalar (scalar : K) : Proportion K := ⟨scalar, Vector3.zero⟩

/-- Embed a three-vector as a pure quaternion with zero scalar coordinate. -/
@[expose] def ofVector (vector : Vector3 K) : Proportion K := ⟨0, vector⟩

/-- Map all original quaternion coordinates through a supplied field embedding. -/
@[expose] def map {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (value : Proportion K) : Proportion L :=
  ⟨embedding.toFun value.scalar,
    ⟨embedding.toFun value.vector.t, embedding.toFun value.vector.r, embedding.toFun value.vector.s⟩⟩

/-- Quaternion coordinate transport preserves the original product.

The supplied embedding preserves each scalar field operation in the dot and
cross formulas. The image product uses the same row-action convention.
-/
theorem map_mul {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (left right : Proportion K) :
    map embedding (mul left right) = mul (map embedding left) (map embedding right) := by
  apply Proportion.ext
  · simp only [map, mul, Vector3.dot, embedding.map_sub, embedding.map_add, embedding.map_mul,
      -eq_self, -iff_self]
    rfl
  · apply Vector3.ext <;>
      simp only [map, mul, Vector3.scale, Vector3.sub, Vector3.add, Vector3.cross,
        embedding.map_sub, embedding.map_add, embedding.map_mul, -eq_self, -iff_self] <;> rfl

/-- Quaternion coordinate transport preserves its original additive law. -/
theorem map_add {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (left right : Proportion K) :
    map embedding (add left right) = add (map embedding left) (map embedding right) := by
  apply Proportion.ext
  · exact embedding.map_add left.scalar right.scalar
  · apply Vector3.ext <;> exact embedding.map_add _ _

/-- Quaternion coordinate transport preserves scaling by the same embedded scalar. -/
theorem map_scale {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (factor : K) (value : Proportion K) :
    map embedding (scale factor value) = scale (embedding.toFun factor) (map embedding value) := by
  apply Proportion.ext
  · exact embedding.map_mul factor value.scalar
  · apply Vector3.ext <;> exact embedding.map_mul _ _

/-- The original quaternion norm maps to the norm of the embedded coordinates. -/
theorem map_norm {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (value : Proportion K) :
    (map embedding value).norm = embedding.toFun value.norm := by
  simp only [map, norm, Vector3.quadrance, Vector3.dot, pow_two,
    embedding.map_add, embedding.map_mul, -eq_self, -iff_self]
  rfl

/-- Quaternion coordinate transport commutes with the original conjugate. -/
theorem map_conjugate {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (value : Proportion K) :
    map embedding (conjugate value) = conjugate (map embedding value) := by
  apply Proportion.ext
  · rfl
  · apply Vector3.ext <;> exact embedding.map_neg _

/-- Equal embedded quaternion coordinates imply equal original quaternions. -/
theorem map_injective {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) {left right : Proportion K} (equal : map embedding left = map embedding right) :
    left = right := by
  apply Proportion.ext
  · exact embedding.injective (congrArg Proportion.scalar equal)
  · apply Vector3.ext
    · exact embedding.injective (congrArg (fun value => value.vector.t) equal)
    · exact embedding.injective (congrArg (fun value => value.vector.r) equal)
    · exact embedding.injective (congrArg (fun value => value.vector.s) equal)

/-- The pure quaternion on the first coordinate axis. -/
@[expose] def i : Proportion K := ofVector ⟨1, 0, 0⟩

/-- The pure quaternion on the second coordinate axis. -/
@[expose] def j : Proportion K := ofVector ⟨0, 1, 0⟩

/-- The pure quaternion on the third coordinate axis. -/
@[expose] def k : Proportion K := ofVector ⟨0, 0, 1⟩

/-- The three pure coordinate quaternions have the original row-action multiplication table.

Each basis square is minus one. The products in reverse coordinate order are
positive, and the other cyclic products are their negatives.
-/
theorem basis_products :
    mul (i : Proportion K) i = ofScalar (-1) ∧ mul (j : Proportion K) j = ofScalar (-1) ∧
      mul (k : Proportion K) k = ofScalar (-1) ∧ mul (j : Proportion K) i = k ∧
      mul (k : Proportion K) j = i ∧ mul (i : Proportion K) k = j ∧
      mul (i : Proportion K) j = scale (-1) k ∧ mul (j : Proportion K) k = scale (-1) i ∧
      mul (k : Proportion K) i = scale (-1) j := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply Proportion.ext
    · simp only [mul, i, j, k, ofScalar, ofVector, scale, Vector3.dot, Vector3.zero, -eq_self, -iff_self]
      ring1
    · apply Vector3.ext <;>
        simp only [mul, i, j, k, ofScalar, ofVector, scale, Vector3.zero,
          Vector3.sub, Vector3.add, Vector3.scale, Vector3.cross, -eq_self, -iff_self] <;> ring1

/-- Every quaternion is the sum of its scalar and three scaled pure basis coordinates. -/
theorem basis_decomposition (value : Proportion K) :
    value = add (ofScalar value.scalar)
      (add (scale value.vector.t i) (add (scale value.vector.r j) (scale value.vector.s k))) := by
  apply Proportion.ext
  · unfold add ofScalar scale i j k ofVector
    ring1
  · apply Vector3.ext <;> unfold add ofScalar scale i j k ofVector Vector3.zero Vector3.add Vector3.scale <;> ring1

/-- Quaternion multiplication distributes over addition in its right input.

The scalar pairing and vector cross product are bilinear for the original
scalar-vector coordinates and multiplication convention.
-/
theorem mul_add (first second third : Proportion K) :
    mul first (add second third) = add (mul first second) (mul first third) := by
  apply Proportion.ext
  · unfold mul add Vector3.add Vector3.dot
    ring1
  · apply Vector3.ext <;> unfold mul add Vector3.add Vector3.sub Vector3.scale Vector3.cross <;> ring1

/-- Quaternion multiplication distributes over addition in its left input.

The two products on the right retain the original order of their operands.
-/
theorem add_mul (first second third : Proportion K) :
    mul (add first second) third = add (mul first third) (mul second third) := by
  apply Proportion.ext
  · unfold mul add Vector3.add Vector3.dot
    ring1
  · apply Vector3.ext <;> unfold mul add Vector3.add Vector3.sub Vector3.scale Vector3.cross <;> ring1

/-- Invert a quaternion with a supplied nonzero norm.

The original conjugate is scaled by the inverse of its norm. Both multiplication
orders recover the original unit quaternion.
-/
@[expose] def inverse (proportion : Proportion K) (_nonNull : proportion.norm ≠ 0) : Proportion K :=
  scale proportion.norm⁻¹ (conjugate proportion)

/-- A non-null quaternion times its computed inverse is the unit quaternion. -/
theorem mul_inverse (proportion : Proportion K) (nonNull : proportion.norm ≠ 0) :
    mul proportion (inverse proportion nonNull) = identity := by
  have scaled := mul_scale_both 1 proportion.norm⁻¹ proportion (conjugate proportion)
  rw [one_scale, mul_conjugate, scale_scale] at scaled
  have cancel : proportion.norm⁻¹ * proportion.norm = 1 := by
    calc
      proportion.norm⁻¹ * proportion.norm = proportion.norm * proportion.norm⁻¹ := by ring1
      _ = 1 := ExplicitField.mul_inv_cancel _ nonNull
  rw [show (1 : K) * proportion.norm⁻¹ = proportion.norm⁻¹ by ring1, cancel, one_scale] at scaled
  exact scaled

/-- The computed inverse times its non-null quaternion is the unit quaternion. -/
theorem inverse_mul (proportion : Proportion K) (nonNull : proportion.norm ≠ 0) :
    mul (inverse proportion nonNull) proportion = identity := by
  have scaled := mul_scale_both proportion.norm⁻¹ 1 (conjugate proportion) proportion
  rw [one_scale, conjugate_mul, scale_scale] at scaled
  have cancel : proportion.norm⁻¹ * proportion.norm = 1 := by
    calc
      proportion.norm⁻¹ * proportion.norm = proportion.norm * proportion.norm⁻¹ := by ring1
      _ = 1 := ExplicitField.mul_inv_cancel _ nonNull
  rw [show proportion.norm⁻¹ * (1 : K) = proportion.norm⁻¹ by ring1, cancel, one_scale] at scaled
  exact scaled

/-- A null quaternion has no right inverse over a field with nonzero unit.

Multiplicativity of the original norm would equate zero with the unit norm
if a right inverse existed. This includes the zero quaternion.
-/
theorem null_no_right_inverse (proportion : Proportion K) (null : proportion.IsNull)
    (oneNonzero : (1 : K) ≠ 0) (candidate : Proportion K) : mul proportion candidate ≠ identity := by
  intro inverseEquation
  have normEquation := norm_mul proportion candidate
  rw [inverseEquation] at normEquation
  have identityNorm : norm (identity : Proportion K) = 1 := by
    unfold norm identity Vector3.quadrance Vector3.dot Vector3.zero
    ring1
  rw [identityNorm, null] at normEquation
  have zeroProduct : (0 : K) * candidate.norm = 0 := by ring1
  exact oneNonzero (normEquation.trans zeroProduct)

/-- A null quaternion has no left inverse over a field with nonzero unit.

The same multiplicative norm obstruction applies when the candidate is the
left operand, independently of any projective equivalence.
-/
theorem null_no_left_inverse (proportion : Proportion K) (null : proportion.IsNull)
    (oneNonzero : (1 : K) ≠ 0) (candidate : Proportion K) : mul candidate proportion ≠ identity := by
  intro inverseEquation
  have normEquation := norm_mul candidate proportion
  rw [inverseEquation] at normEquation
  have identityNorm : norm (identity : Proportion K) = 1 := by
    unfold norm identity Vector3.quadrance Vector3.dot Vector3.zero
    ring1
  rw [identityNorm, null] at normEquation
  have zeroProduct : candidate.norm * (0 : K) = 0 := by ring1
  exact oneNonzero (normEquation.trans zeroProduct)

/-- A quaternion admits an exact two-sided inverse precisely when its norm is nonzero.

The unit must be nonzero. The reverse implication returns the computed
conjugate-over-norm inverse, while the forward implication uses the original
multiplicative norm obstruction.
-/
theorem exists_inverse_iff (proportion : Proportion K) (oneNonzero : (1 : K) ≠ 0) :
    (∃ candidate : Proportion K, mul proportion candidate = identity ∧
      mul candidate proportion = identity) ↔ proportion.norm ≠ 0 := by
  constructor
  · rintro ⟨candidate, rightInverse, _⟩ null
    exact null_no_right_inverse proportion null oneNonzero candidate rightInverse
  · intro nonNull
    exact ⟨inverse proportion nonNull, mul_inverse proportion nonNull, inverse_mul proportion nonNull⟩

end Proportion

@[expose] public section

/-- A certificate that a zero sum of four squares has four zero entries.

The property is supplied directly for the explicit field, without assuming a general ordered-field hierarchy. -/
structure SumFourSquaresSeparate (K : Type*) [ExplicitField K] where
  /-- A zero sum of the four displayed squares forces each root to be zero. -/ separate : ∀ scalar t r s : K,
    scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 = 0 →
      scalar = 0 ∧ t = 0 ∧ r = 0 ∧ s = 0

end

/-- Four-square separation forces a zero-norm proportion to be the zero quadruple.

The supplied certificate applies to its scalar and three vector coordinates. -/
theorem proportion_eq_zero_of_norm_eq_zero
    (certificate : SumFourSquaresSeparate K) (proportion : Proportion K)
    (null : proportion.norm = 0) : proportion = Proportion.zero := by
  have coordinates := certificate.separate proportion.scalar
    proportion.vector.t proportion.vector.r proportion.vector.s (by
      unfold Proportion.norm Vector3.quadrance Vector3.dot at null
      simpa only [pow_two, add_assoc] using null)
  apply Proportion.ext
  · exact coordinates.1
  · exact Vector3.ext coordinates.2.1 coordinates.2.2.1 coordinates.2.2.2

/-- Four-square separation makes every nonzero proportion non-null.

A zero norm would force equality with the excluded zero quadruple. -/
theorem proportion_norm_ne_zero_of_isNonzero
    (certificate : SumFourSquaresSeparate K) (proportion : Proportion K)
    (nonzero : proportion.IsNonzero) : proportion.norm ≠ 0 := by
  intro null
  exact nonzero (Projective.Basic.proportion_eq_zero_of_norm_eq_zero certificate proportion null)

/-- A sum of four ordered-field squares is nonzero when its first root is nonzero.

Starting with that positive square, each of the remaining squares preserves
positivity. The retained positive cone supplies the nonzero conclusion.
-/
private theorem fourSquares_nonzero_of_first {F : Type*} [RayOrderedExplicitField F]
    (scalar t r s : F) (nonzero : scalar ≠ 0) : scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 ≠ 0 := by
  have squarePositive : 0 < scalar ^ 2 := by
    have positive := OrderedExplicitField.mul_self_pos_direct nonzero
    have square : scalar * scalar = scalar ^ 2 := by ring1
    exact square ▸ positive
  exact RayOrderedExplicitField.positive_ne_zero_direct
    (RayOrderedExplicitField.add_square_pos
      (RayOrderedExplicitField.add_square_pos (RayOrderedExplicitField.add_square_pos squarePositive)))

/-- Four squares over a ray-ordered field sum to zero only when all roots vanish.

Each nonzero coordinate would give a strictly positive sum, using the original
positive cone and its nonzero certificate. The returned certificate keeps the
original field operations and all four coordinate equalities.
-/
theorem orderedSumFourSquaresSeparate {F : Type*} [RayOrderedExplicitField F] : SumFourSquaresSeparate F where
  separate := by
    intro scalar t r s sumZero
    letI : DecidableEq F := OrderedExplicitField.eq_decidable
    have scalarZero : scalar = 0 := by
      by_cases zero : scalar = 0
      · exact zero
      · exact False.elim (fourSquares_nonzero_of_first scalar t r s zero sumZero)
    have tZero : t = 0 := by
      by_cases zero : t = 0
      · exact zero
      · apply False.elim
        apply fourSquares_nonzero_of_first t scalar r s zero
        calc
          t ^ 2 + scalar ^ 2 + r ^ 2 + s ^ 2 = scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 := by ring1
          _ = 0 := sumZero
    have rZero : r = 0 := by
      by_cases zero : r = 0
      · exact zero
      · apply False.elim
        apply fourSquares_nonzero_of_first r scalar t s zero
        calc
          r ^ 2 + scalar ^ 2 + t ^ 2 + s ^ 2 = scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 := by ring1
          _ = 0 := sumZero
    have sZero : s = 0 := by
      by_cases zero : s = 0
      · exact zero
      · apply False.elim
        apply fourSquares_nonzero_of_first s scalar t r zero
        calc
          s ^ 2 + scalar ^ 2 + t ^ 2 + r ^ 2 = scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 := by ring1
          _ = 0 := sumZero
    exact ⟨scalarZero, tZero, rZero, sZero⟩

/-- Four rational squares sum to zero only when all four roots vanish.

The certificate uses the direct order and square laws of the executable rational field. -/
theorem rationalSumFourSquaresSeparate :
    SumFourSquaresSeparate Fraction.Rational where
  separate := by
    intro scalar t r s sumZero
    have scalarNonnegative :=
      Fraction.Order.Arithmetic.sq_nonneg_direct scalar
    have tNonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct t
    have rNonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct r
    have sNonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct s
    have scalarUpper : scalar ^ 2 ≤ 0 := by
      have remainingNonnegative : 0 ≤ t ^ 2 + r ^ 2 + s ^ 2 :=
        add_nonneg (add_nonneg tNonnegative rNonnegative) sNonnegative
      have bounded : scalar ^ 2 ≤
          scalar ^ 2 + (t ^ 2 + r ^ 2 + s ^ 2) :=
        le_add_of_nonneg_right remainingNonnegative
      rwa [← add_assoc, ← add_assoc, sumZero] at bounded
    have tUpper : t ^ 2 ≤ 0 := by
      have remainingNonnegative : 0 ≤ scalar ^ 2 + r ^ 2 + s ^ 2 :=
        add_nonneg (add_nonneg scalarNonnegative rNonnegative) sNonnegative
      have bounded : t ^ 2 ≤
          t ^ 2 + (scalar ^ 2 + r ^ 2 + s ^ 2) :=
        le_add_of_nonneg_right remainingNonnegative
      calc
        t ^ 2 ≤ t ^ 2 + (scalar ^ 2 + r ^ 2 + s ^ 2) := bounded
        _ = scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 := by ring1
        _ = 0 := sumZero
    have rUpper : r ^ 2 ≤ 0 := by
      have remainingNonnegative : 0 ≤ scalar ^ 2 + t ^ 2 + s ^ 2 :=
        add_nonneg (add_nonneg scalarNonnegative tNonnegative) sNonnegative
      have bounded : r ^ 2 ≤
          r ^ 2 + (scalar ^ 2 + t ^ 2 + s ^ 2) :=
        le_add_of_nonneg_right remainingNonnegative
      calc
        r ^ 2 ≤ r ^ 2 + (scalar ^ 2 + t ^ 2 + s ^ 2) := bounded
        _ = scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 := by ring1
        _ = 0 := sumZero
    have sUpper : s ^ 2 ≤ 0 := by
      have remainingNonnegative : 0 ≤ scalar ^ 2 + t ^ 2 + r ^ 2 :=
        add_nonneg (add_nonneg scalarNonnegative tNonnegative) rNonnegative
      have bounded : s ^ 2 ≤
          s ^ 2 + (scalar ^ 2 + t ^ 2 + r ^ 2) :=
        le_add_of_nonneg_right remainingNonnegative
      calc
        s ^ 2 ≤ s ^ 2 + (scalar ^ 2 + t ^ 2 + r ^ 2) := bounded
        _ = scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 := by ring1
        _ = 0 := sumZero
    exact
      ⟨(Fraction.Order.Arithmetic.sq_eq_zero_direct scalar).mp
          (le_antisymm scalarUpper scalarNonnegative),
        (Fraction.Order.Arithmetic.sq_eq_zero_direct t).mp
          (le_antisymm tUpper tNonnegative),
        (Fraction.Order.Arithmetic.sq_eq_zero_direct r).mp
          (le_antisymm rUpper rNonnegative),
        (Fraction.Order.Arithmetic.sq_eq_zero_direct s).mp
          (le_antisymm sUpper sNonnegative)⟩

/-- Every nonzero rational proportion has nonzero norm.

The rational four-square separation certificate excludes nonzero null quadruples. -/
theorem rational_proportion_norm_ne_zero (proportion :
    Proportion Fraction.Rational)
    (nonzero : proportion.IsNonzero) : proportion.norm ≠ 0 :=
  Projective.Basic.proportion_norm_ne_zero_of_isNonzero Projective.Basic.rationalSumFourSquaresSeparate
    proportion nonzero

@[expose] public section

set_option genInjectivity false in
/-- A quaternion proportion with a retained nonzero norm certificate.

The retained scalar and vector coordinates are preserved, and the certificate supports the divisions used by its
projective operations. -/
@[ext]
structure NonNullProportion (K : Type*) [ExplicitField K]
    extends Proportion K where
  /-- The retained quaternion norm is nonzero. -/ normNonzero : toProportion.norm ≠ 0

constructive_injectivity NonNullProportion

end

namespace NonNullProportion

/-- Certify an original nonzero quaternion using a supplied four-square separation law.

The retained scalar and vector coordinates are the original input. The
separation certificate supplies its nonzero norm without normalizing them.
-/
@[expose] def ofNonzero (certificate : SumFourSquaresSeparate K) (proportion : Proportion K)
    (nonzero : proportion.IsNonzero) : NonNullProportion K where
  toProportion := proportion
  normNonzero := proportion_norm_ne_zero_of_isNonzero certificate proportion nonzero

/-- A non-null quaternion proportion is not the zero quadruple. -/
theorem isNonzero (proportion : NonNullProportion K) :
    proportion.toProportion.IsNonzero := by
  intro equalZero
  apply proportion.normNonzero
  rw [equalZero]
  exact Proportion.norm_zero

/-- A non-null quaternion proportion forces the field unit to be nonzero.

If the unit vanished, the retained norm would vanish by multiplication by zero, contradicting the non-nullness
certificate. -/
theorem one_ne_zero (proportion : NonNullProportion K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply proportion.normNonzero
  calc
    proportion.toProportion.norm =
        proportion.toProportion.norm * 1 := by rw [mul_one]
    _ = proportion.toProportion.norm * 0 := by rw [oneZero]
    _ = 0 := by rw [mul_zero]

/-- Rescale a non-null quaternion proportion by a supplied nonzero factor.

The homogeneous scaling is retained with the nonzero norm certificate transported through the factor square. -/
@[expose] def scale (factor : K) (factorNonzero : factor ≠ 0)
    (proportion : NonNullProportion K) : NonNullProportion K where
  toProportion := Proportion.scale factor proportion.toProportion
  normNonzero := by
    rw [Proportion.norm_scale]
    exact ExplicitField.mul_ne_zero
      (by
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero factorNonzero factorNonzero)
      proportion.normNonzero

/-- Non-null proportions are equivalent when their original proportions differ by a nonzero scale.

The relation retains the exact scale, its nonzero witness and equality of the underlying homogeneous coordinates. -/
@[expose] def Equivalent (left right : NonNullProportion K) : Prop :=
  left.toProportion.Equivalent right.toProportion

/-- Each non-null proportion is equivalent to itself using unit scale. -/
theorem equivalent_refl (proportion : NonNullProportion K) :
    proportion.Equivalent proportion := by
  exact ⟨1, proportion.one_ne_zero, (Proportion.one_scale _).symm⟩

/-- Reverse a projective equivalence by inverting its retained nonzero scale.

The inverse scale is nonzero. Multiplication by the inverse recovers the first retained proportion from the second. -/
theorem equivalent_symm {left right : NonNullProportion K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
  have reverseCancel : factor⁻¹ * factor = 1 := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := cancel
  refine ⟨factor⁻¹, ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  calc
    left.toProportion = Proportion.scale 1 left.toProportion := by
      rw [Proportion.one_scale]
    _ = Proportion.scale (factor⁻¹ * factor) left.toProportion := by
      rw [reverseCancel]
    _ = Proportion.scale factor⁻¹
        (Proportion.scale factor left.toProportion) := by
      rw [Proportion.scale_scale]
    _ = Proportion.scale factor⁻¹ right.toProportion := by
      rw [← rightValue]

/-- Compose projective equivalences by multiplying their retained nonzero scales.

The two retained coordinate equalities compose through successive scaling. The product scale is nonzero by the supplied
witnesses. -/
theorem equivalent_trans {first second third : NonNullProportion K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with ⟨firstFactor, firstFactorNonzero, secondValue⟩
  rcases secondThird with ⟨secondFactor, secondFactorNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    ExplicitField.mul_ne_zero secondFactorNonzero firstFactorNonzero, ?_⟩
  calc
    third.toProportion =
        Proportion.scale secondFactor second.toProportion := thirdValue
    _ = Proportion.scale secondFactor
        (Proportion.scale firstFactor first.toProportion) := by rw [secondValue]
    _ = Proportion.scale (secondFactor * firstFactor)
        first.toProportion := Proportion.scale_scale _ _ _

/-- A nonzero rescaling represents the same projective quaternion proportion.

The supplied factor and its nonzero certificate witness the homogeneous relation to the displayed rescaled coordinates.
-/
theorem equivalent_scale (factor : K) (factorNonzero : factor ≠ 0)
    (proportion : NonNullProportion K) :
    proportion.Equivalent (NonNullProportion.scale factor factorNonzero proportion) := by
  exact ⟨factor, factorNonzero, rfl⟩

/-- Multiply non-null quaternion proportions with their nonzero norm certificate.

The product retains the original coordinate multiplication and certifies its norm from the two input certificates. -/
@[expose] def mul (left right : NonNullProportion K) : NonNullProportion K where
  toProportion := Proportion.mul left.toProportion right.toProportion
  normNonzero := by
    rw [Proportion.norm_mul]
    exact ExplicitField.mul_ne_zero left.normNonzero right.normNonzero

/-- The retained norm of a product is the product of the two input norms.

The scalar-vector product identity applies to the underlying coordinates of both non-null proportions. Their norm
certificates remain attached to the inputs. -/
theorem mul_norm (left right : NonNullProportion K) :
    (NonNullProportion.mul left right).toProportion.norm =
      left.toProportion.norm * right.toProportion.norm :=
  Proportion.norm_mul _ _

/-- Multiplication of certified non-null quaternion proportions is associative.

Associativity of the underlying displayed product identifies the retained coordinates. Proof irrelevance identifies the
corresponding nonzero norm certificates. -/
theorem mul_assoc (first second third : NonNullProportion K) :
    NonNullProportion.mul (NonNullProportion.mul first second) third = NonNullProportion.mul first
      (NonNullProportion.mul second third) := by
  have raw := Proportion.mul_assoc
    first.toProportion second.toProportion third.toProportion
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

/-- The non-null quaternion product respects equivalence in both arguments.

The product of the supplied homogeneous scales witnesses the output equivalence. -/
theorem mul_respects_equivalent
    {left left' right right' : NonNullProportion K}
    (leftEquivalent : left.Equivalent left')
    (rightEquivalent : right.Equivalent right') :
    (NonNullProportion.mul left right).Equivalent (NonNullProportion.mul left' right') := by
  rcases leftEquivalent with ⟨leftFactor, leftFactorNonzero, leftValue⟩
  rcases rightEquivalent with ⟨rightFactor, rightFactorNonzero, rightValue⟩
  refine ⟨leftFactor * rightFactor,
    ExplicitField.mul_ne_zero leftFactorNonzero rightFactorNonzero, ?_⟩
  change Proportion.mul left'.toProportion right'.toProportion =
    Proportion.scale (leftFactor * rightFactor)
      (Proportion.mul left.toProportion right.toProportion)
  rw [leftValue, rightValue, Proportion.mul_scale_both]

/-- Construct the non-null unit proportion from a supplied non-null witness.

The witness certifies that one is nonzero; the returned coordinates are scalar one and zero vector. -/
@[expose] def identity (witness : NonNullProportion K) : NonNullProportion K where
  toProportion := Proportion.identity
  normNonzero := by
    unfold Proportion.norm Proportion.identity
    rw [Vector3.quadrance_zero]
    simpa only [one_pow, add_zero] using witness.one_ne_zero

/-- The certified unit proportion is a left multiplicative identity. -/
@[simp] theorem identity_mul (witness proportion : NonNullProportion K) :
    NonNullProportion.mul (NonNullProportion.identity witness) proportion = proportion := by
  have raw := Proportion.identity_mul proportion.toProportion
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

/-- The certified unit proportion is a right multiplicative identity. -/
@[simp] theorem mul_identity (proportion witness : NonNullProportion K) :
    NonNullProportion.mul proportion (NonNullProportion.identity witness) = proportion := by
  have raw := Proportion.mul_identity proportion.toProportion
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

/-- Conjugate a non-null proportion and retain its unchanged nonzero norm certificate.

The vector coordinate is negated and the scalar coordinate is preserved. Norm invariance transports the supplied
non-nullness witness. -/
@[expose] def conjugate (proportion : NonNullProportion K) : NonNullProportion K where
  toProportion := Proportion.conjugate proportion.toProportion
  normNonzero := by
    rw [Proportion.norm_conjugate]
    exact proportion.normNonzero

/-- Conjugating a certified non-null proportion twice returns the original proportion.

Double negation recovers the retained coordinates, and the nonzero norm proof does not add executable data. -/
@[simp] theorem conjugate_conjugate (proportion : NonNullProportion K) :
    NonNullProportion.conjugate (NonNullProportion.conjugate proportion) = proportion := by
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar
      (Proportion.conjugate_conjugate proportion.toProportion)
  · exact congrArg Proportion.vector
      (Proportion.conjugate_conjugate proportion.toProportion)

/-- Conjugation reverses the certified non-null product exactly.

The equality retains the same two input proportions and their reversed displayed product. The nonzero norm certificates
agree by proof irrelevance. -/
theorem conjugate_mul_reverse (left right : NonNullProportion K) :
    NonNullProportion.conjugate (NonNullProportion.mul left right) = NonNullProportion.mul (NonNullProportion.conjugate
      right) (NonNullProportion.conjugate left) := by
  have raw := Proportion.conjugate_mul_reverse left.toProportion
    right.toProportion
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

/-- A non-null proportion times its conjugate is projectively equivalent to the unit.

The retained nonzero norm supplies the homogeneous equivalence factor. -/
theorem mul_conjugate_equivalent_identity (proportion : NonNullProportion K) :
    (NonNullProportion.mul proportion (NonNullProportion.conjugate proportion)).Equivalent
      (NonNullProportion.identity proportion) := by
  apply NonNullProportion.equivalent_symm
  refine ⟨proportion.toProportion.norm, proportion.normNonzero, ?_⟩
  exact Proportion.mul_conjugate proportion.toProportion

/-- A conjugate times its original non-null proportion is projectively equivalent to the unit.

The retained nonzero norm supplies the homogeneous equivalence factor. -/
theorem conjugate_mul_equivalent_identity (proportion : NonNullProportion K) :
    (NonNullProportion.mul (NonNullProportion.conjugate proportion) proportion).Equivalent
      (NonNullProportion.identity proportion) := by
  apply NonNullProportion.equivalent_symm
  refine ⟨proportion.toProportion.norm, proportion.normNonzero, ?_⟩
  exact Proportion.conjugate_mul proportion.toProportion

/-- Construct the pure-vector quaternion proportion of a non-null axis.

The scalar coordinate is zero and the supplied vector quadrance certificate certifies the quaternion norm. -/
@[expose] def ofNonNullVector (axis : Vector3 K) (axisNonNull : axis.quadrance ≠ 0) :
    NonNullProportion K where
  scalar := 0
  vector := axis
  normNonzero := by
    unfold Proportion.norm
    simpa only [pow_two, zero_mul, zero_add] using axisNonNull

end NonNullProportion

end

end Purelib.Algebra.Quaternion.Projective.Basic
