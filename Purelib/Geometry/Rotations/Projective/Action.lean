module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
public import Purelib.Geometry.Rotations.Cayley.Charts
public import Purelib.Geometry.Rotations.Spread

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quaternion.Projective.Basic
public import Purelib.Algebra.Quaternion.Matrix
import Purelib.Geometry.Rotations.Basic
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Geometry.Rotations.Reflection
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.LinearAlgebra.Coordinates3.Matrix
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

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Geometry

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Cayley

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

section
/-!
# Rational rotations, section 11: the projective rotation map

The map is proved special orthogonal and multiplicative by explicit
denominator-cleared polynomial identities.  In particular, no density of
rational points, root counting, infinite carrier, or polynomial identity
transfer is used in place of the paper's Lemma 59.
-/

@[expose] public section

namespace Purelib.Geometry.Rotations.Projective.Action

open Purelib.LinearAlgebra.Coordinates3.Antisymmetric
open Purelib.Geometry.Rotations.Cayley.Cap

variable {K : Type*} [ExplicitField K]

/-- The homogeneous quadratic numerator of Definition 55. -/
def proportionRotationNumerator (proportion : Projective.Basic.Proportion K) : Coordinates3.Matrix3 K :=
  ⟨proportion.scalar ^ 2 + proportion.vector.t ^ 2 -
      proportion.vector.r ^ 2 - proportion.vector.s ^ 2,
    2 * (proportion.scalar * proportion.vector.s +
      proportion.vector.r * proportion.vector.t),
    2 * (-proportion.scalar * proportion.vector.r +
      proportion.vector.s * proportion.vector.t),
    2 * (-proportion.scalar * proportion.vector.s +
      proportion.vector.r * proportion.vector.t),
    proportion.scalar ^ 2 - proportion.vector.t ^ 2 +
      proportion.vector.r ^ 2 - proportion.vector.s ^ 2,
    2 * (proportion.scalar * proportion.vector.t +
      proportion.vector.r * proportion.vector.s),
    2 * (proportion.scalar * proportion.vector.r +
      proportion.vector.s * proportion.vector.t),
    2 * (-proportion.scalar * proportion.vector.t +
      proportion.vector.r * proportion.vector.s),
    proportion.scalar ^ 2 - proportion.vector.t ^ 2 -
      proportion.vector.r ^ 2 + proportion.vector.s ^ 2⟩

/-- Scaling homogeneous coordinates scales the rotation numerator by the scalar square. -/
theorem proportionRotationNumerator_scale (factor : K)
    (proportion : Projective.Basic.Proportion K) :
    Projective.Action.proportionRotationNumerator (Proportion.scale factor proportion) =
      Matrix3.scale (factor ^ 2)
        (Projective.Action.proportionRotationNumerator proportion) := by
  apply Matrix3.ext <;> unfold Projective.Action.proportionRotationNumerator Proportion.scale
    Matrix3.scale Coordinates3.Vector.scale <;> ring1

/-- The denominator-cleared multiplicativity identity behind Theorem 58. -/
theorem proportionRotationNumerator_mul (left right : Projective.Basic.Proportion K) :
    Matrix3.mul (Projective.Action.proportionRotationNumerator left)
        (Projective.Action.proportionRotationNumerator right) =
      Projective.Action.proportionRotationNumerator (Proportion.mul left right) := by
  apply Matrix3.ext <;> unfold Projective.Action.proportionRotationNumerator Proportion.mul
    Matrix3.mul Coordinates3.Vector.dot Coordinates3.Vector.sub Coordinates3.Vector.add Coordinates3.Vector.scale
      Coordinates3.Vector.cross <;>
    ring1

/-- The rotation numerator times its transpose is the norm square times the identity. -/
theorem proportionRotationNumerator_mul_transpose
    (proportion : Projective.Basic.Proportion K) :
    Matrix3.mul (Projective.Action.proportionRotationNumerator proportion)
        (Matrix3.transpose (Projective.Action.proportionRotationNumerator proportion)) =
      Matrix3.scale (proportion.norm ^ 2) Matrix3.identity := by
  apply Matrix3.ext <;> unfold Projective.Action.proportionRotationNumerator Proportion.norm
    Matrix3.mul Matrix3.transpose Matrix3.scale Matrix3.identity
    Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;> ring1

/-- The homogeneous rotation numerator has determinant equal to the proportion norm cubed. -/
theorem determinant_proportionRotationNumerator
    (proportion : Projective.Basic.Proportion K) :
    Matrix3.determinant (Projective.Action.proportionRotationNumerator proportion) =
      proportion.norm ^ 3 := by
  unfold Projective.Action.proportionRotationNumerator Proportion.norm Matrix3.determinant
    Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  ring1

/-- The homogeneous rotation numerator has trace `3x² - Q(v)`. -/
theorem trace_proportionRotationNumerator (proportion : Projective.Basic.Proportion K) :
    Matrix3.trace (Projective.Action.proportionRotationNumerator proportion) =
      3 * proportion.scalar ^ 2 - proportion.vector.quadrance := by
  unfold Projective.Action.proportionRotationNumerator Matrix3.trace
    Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  ring1

namespace NonNullProportion

/-- Compute the rotation matrix represented by a non-null quaternion proportion.

The scalar and vector coordinates enter the quadratic reciprocal-anchor formula, with the retained nonzero norm
certifying its denominator (Definition 55). -/
def rotationMatrix (proportion : Projective.Basic.NonNullProportion K) : Coordinates3.Matrix3 K :=
  Charts.reciprocalAnchorPath proportion.scalar proportion.vector
    proportion.normNonzero

/-- Express a represented rotation matrix as its homogeneous numerator divided by norm.

The non-null proportion supplies the nonzero norm, so scaling its quadratic rotation numerator by the inverse norm
recovers the stored matrix (Definition 55). -/
theorem rotationMatrix_eq_scaled_numerator
    (proportion : Projective.Basic.NonNullProportion K) :
    (Projective.Action.NonNullProportion.rotationMatrix proportion) =
      Matrix3.scale proportion.toProportion.norm⁻¹
        (Geometry.Rotations.Projective.Action.proportionRotationNumerator proportion.toProportion) := by
  have cancel := ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  have expandedCancel :
      (proportion.scalar ^ 2 +
          (proportion.vector.t * proportion.vector.t +
            proportion.vector.r * proportion.vector.r +
            proportion.vector.s * proportion.vector.s)) *
        (proportion.scalar ^ 2 +
          (proportion.vector.t * proportion.vector.t +
            proportion.vector.r * proportion.vector.r +
            proportion.vector.s * proportion.vector.s))⁻¹ = 1 := by
    simpa only [Proportion.norm, Coordinates3.Vector.quadrance, Coordinates3.Vector.dot] using cancel
  apply Matrix3.ext <;> unfold Projective.Action.NonNullProportion.rotationMatrix Charts.reciprocalAnchorPath
    Charts.reciprocalAnchorPathDenominator Geometry.Rotations.Projective.Action.proportionRotationNumerator
    Proportion.norm Matrix3.add Matrix3.scale Matrix3.identity Matrix3.mul
    Antisymmetric.anchor Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
    simp only [ExplicitField.div_eq_mul_inv] <;>
    (try rw [← expandedCancel]) <;> ring1

/-- Conjugating a non-null quaternion transposes its represented rotation matrix.

The scalar coordinate is retained and the vector coordinate is negated. The
original norm and normalized quadratic numerator give the same transpose,
with no change of the retained projective representative.
-/
theorem rotationMatrix_conjugate (proportion : Projective.Basic.NonNullProportion K) :
    rotationMatrix (Projective.Basic.NonNullProportion.conjugate proportion) =
      Matrix3.transpose (rotationMatrix proportion) := by
  rw [rotationMatrix_eq_scaled_numerator, rotationMatrix_eq_scaled_numerator, Matrix3.transpose_scale]
  change Matrix3.scale (Proportion.conjugate proportion.toProportion).norm⁻¹
      (proportionRotationNumerator (Proportion.conjugate proportion.toProportion)) =
    Matrix3.scale proportion.toProportion.norm⁻¹
      (Matrix3.transpose (proportionRotationNumerator proportion.toProportion))
  rw [Proportion.norm_conjugate]
  apply Matrix3.ext <;> unfold proportionRotationNumerator Proportion.conjugate
    Coordinates3.Vector.neg Matrix3.transpose Matrix3.scale <;> ring1

/-- The original quaternion sandwich is the represented row-vector rotation.

Conjugate the retained quaternion on the left, multiply the pure input vector,
then multiply the original quaternion on the right and divide by its norm.
The resulting quaternion is pure and has the original rotation readback.
-/
theorem sandwich_formula (proportion : Projective.Basic.NonNullProportion K) (vector : Coordinates3.Vector K) :
    Proportion.scale proportion.toProportion.norm⁻¹
      (Proportion.mul (Proportion.mul (Proportion.conjugate proportion.toProportion) ⟨0, vector⟩)
        proportion.toProportion) =
      ⟨0, Matrix3.rowMul vector (rotationMatrix proportion)⟩ := by
  rw [rotationMatrix_eq_scaled_numerator, Matrix3.rowMul_scale]
  apply Proportion.ext
  · unfold Proportion.scale Proportion.mul Proportion.conjugate
      Coordinates3.Vector.dot Coordinates3.Vector.scale Coordinates3.Vector.sub
      Coordinates3.Vector.add Coordinates3.Vector.neg Coordinates3.Vector.cross
    ring1
  · apply Coordinates3.Vector.ext <;>
      unfold Proportion.scale Proportion.mul Proportion.conjugate proportionRotationNumerator
        Coordinates3.Vector.dot Coordinates3.Vector.scale Coordinates3.Vector.sub Coordinates3.Vector.add
        Coordinates3.Vector.neg Coordinates3.Vector.cross Matrix3.rowMul <;> ring1

/-- The original non-null unit quaternion represents the identity rotation matrix. -/
theorem rotationMatrix_identity (witness : Projective.Basic.NonNullProportion K) :
    rotationMatrix (Projective.Basic.NonNullProportion.identity witness) = Matrix3.identity := by
  apply Matrix3.ext <;>
    unfold rotationMatrix Charts.reciprocalAnchorPath Projective.Basic.NonNullProportion.identity
      Proportion.identity Coordinates3.Vector.zero Antisymmetric.anchor Matrix3.add Matrix3.identity
      Matrix3.scale Matrix3.mul <;> ring1

/-- The normalized projective rotation matrix is orthogonal. -/
theorem rotationMatrix_isOrthogonal (proportion : Projective.Basic.NonNullProportion K) :
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix proportion).IsOrthogonal := by
  have cancel := ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  have reverseCancel :
      proportion.toProportion.norm⁻¹ * proportion.toProportion.norm = 1 := by
    calc
      proportion.toProportion.norm⁻¹ * proportion.toProportion.norm =
          proportion.toProportion.norm * proportion.toProportion.norm⁻¹ := by
        ring1
      _ = 1 := cancel
  have squareCancel :
      proportion.toProportion.norm⁻¹ ^ 2 *
          proportion.toProportion.norm ^ 2 = 1 := by
    calc
      proportion.toProportion.norm⁻¹ ^ 2 *
          proportion.toProportion.norm ^ 2 =
        (proportion.toProportion.norm⁻¹ *
          proportion.toProportion.norm) ^ 2 := by ring1
      _ = 1 := by rw [reverseCancel]; ring1
  unfold Matrix3.IsOrthogonal
  rw [Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix_eq_scaled_numerator,
    Matrix3.transpose_scale,
    Matrix3.mul_scale_left, Matrix3.mul_scale_right, Matrix3.scale_scale,
    proportionRotationNumerator_mul_transpose, Matrix3.scale_scale,
    show proportion.toProportion.norm⁻¹ *
        proportion.toProportion.norm⁻¹ =
      proportion.toProportion.norm⁻¹ ^ 2 by ring1,
    squareCancel, Matrix3.one_scale]

/-- The normalized projective rotation matrix has determinant one. -/
theorem determinant_rotationMatrix (proportion : Projective.Basic.NonNullProportion K) :
    Matrix3.determinant (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix proportion) = 1 := by
  have cancel := ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  have reverseCancel :
      proportion.toProportion.norm⁻¹ * proportion.toProportion.norm = 1 := by
    calc
      proportion.toProportion.norm⁻¹ * proportion.toProportion.norm =
          proportion.toProportion.norm * proportion.toProportion.norm⁻¹ := by
        ring1
      _ = 1 := cancel
  have cubeCancel :
      proportion.toProportion.norm⁻¹ ^ 3 *
          proportion.toProportion.norm ^ 3 = 1 := by
    calc
      proportion.toProportion.norm⁻¹ ^ 3 *
          proportion.toProportion.norm ^ 3 =
        (proportion.toProportion.norm⁻¹ *
          proportion.toProportion.norm) ^ 3 := by ring1
      _ = 1 := by rw [reverseCancel]; ring1
  rw [Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix_eq_scaled_numerator,
    Matrix3.determinant_scale,
    determinant_proportionRotationNumerator, cubeCancel]

/-- Definition 55 bundled as an executable member of `SO(3)`. -/
def rotation (proportion : Projective.Basic.NonNullProportion K) : Rotations.Basic.Rotation K where
  matrix := (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix proportion)
  orthogonal := (rotationMatrix_isOrthogonal proportion)
  determinantOne := (determinant_rotationMatrix proportion)

/-- Definition 55 is invariant under nonzero homogeneous rescaling. -/
theorem rotationMatrix_scale (factor : K) (factorNonzero : factor ≠ 0)
    (proportion : Projective.Basic.NonNullProportion K) :
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix (NonNullProportion.scale factor factorNonzero
      proportion)) =
      (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix proportion) := by
  have factorSquareNonzero : factor ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero factorNonzero factorNonzero
  have factorSquareCancel := ExplicitField.mul_inv_cancel
    (factor ^ 2) factorSquareNonzero
  have reverseFactorSquareCancel : (factor ^ 2)⁻¹ * factor ^ 2 = 1 := by
    calc
      (factor ^ 2)⁻¹ * factor ^ 2 =
          factor ^ 2 * (factor ^ 2)⁻¹ := by ring1
      _ = 1 := factorSquareCancel
  have coefficient :
      (factor ^ 2 * proportion.toProportion.norm)⁻¹ * factor ^ 2 =
        proportion.toProportion.norm⁻¹ := by
    rw [(fun {K : Type _} [ExplicitField K] {left right : K} (leftNonzero : left ≠ 0)
      (rightNonzero : right ≠ 0) => (Purelib.Algebra.Field.Inverse.inverse_product (K := K) (left := left) (right :=
      right) leftNonzero rightNonzero : (left * right)⁻¹ = left⁻¹ * right⁻¹)) factorSquareNonzero
      proportion.normNonzero]
    calc
      ((factor ^ 2)⁻¹ * proportion.toProportion.norm⁻¹) *
          factor ^ 2 =
        ((factor ^ 2)⁻¹ * factor ^ 2) *
          proportion.toProportion.norm⁻¹ := by ring1
      _ = proportion.toProportion.norm⁻¹ := by
        rw [reverseFactorSquareCancel, one_mul]
  rw [Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix_eq_scaled_numerator,
    Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix_eq_scaled_numerator]
  change Matrix3.scale
      (Proportion.norm (Proportion.scale factor proportion.toProportion))⁻¹
      (Geometry.Rotations.Projective.Action.proportionRotationNumerator
        (Proportion.scale factor proportion.toProportion)) =
    Matrix3.scale proportion.toProportion.norm⁻¹
      (Geometry.Rotations.Projective.Action.proportionRotationNumerator proportion.toProportion)
  rw [
    Proportion.norm_scale, proportionRotationNumerator_scale,
    Matrix3.scale_scale, coefficient]

/-- Equivalent non-null homogeneous proportions give the same rotation matrix. -/
theorem rotationMatrix_respects_equivalent
    {left right : Projective.Basic.NonNullProportion K} (equivalent : left.Equivalent right) :
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix left) =
      (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix right) := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have rightScaled : right = NonNullProportion.scale factor factorNonzero left := by
    apply NonNullProportion.ext (K := K)
    · exact congrArg Proportion.scalar rightValue
    · exact congrArg Proportion.vector rightValue
  rw [rightScaled, rotationMatrix_scale]

/-- On the affine chart, Definition 55 is the cap of the normalized anchor. -/
theorem rotationMatrix_eq_cap (proportion : Projective.Basic.NonNullProportion K)
    (scalarNonzero : proportion.scalar ≠ 0) :
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix proportion) =
      Cap.cap (Coordinates3.Vector.scale proportion.scalar⁻¹ proportion.vector)
        (Charts.reciprocalAnchorCapDefined proportion.scalar proportion.vector
          scalarNonzero proportion.normNonzero) :=
  Charts.reciprocalAnchorPath_eq_cap proportion.scalar proportion.vector
    scalarNonzero proportion.normNonzero

/-- A non-null proportion with zero scalar coordinate has non-null vector part. -/
theorem vector_nonNull_of_scalar_eq_zero
    (proportion : Projective.Basic.NonNullProportion K) (scalarZero : proportion.scalar = 0) :
    proportion.vector.quadrance ≠ 0 := by
  intro vectorNull
  apply proportion.normNonzero
  unfold Proportion.norm
  rw [scalarZero, vectorNull]
  ring1

/-- At infinity, Definition 55 is exactly the half turn about the represented non-null line. -/
theorem rotationMatrix_eq_halfTurn (proportion : Projective.Basic.NonNullProportion K)
    (scalarZero : proportion.scalar = 0) :
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix proportion) =
      Reflection.halfTurn proportion.vector
        (vector_nonNull_of_scalar_eq_zero proportion scalarZero)
          := by
  let vectorNonNull := vector_nonNull_of_scalar_eq_zero
    proportion scalarZero
  simpa only [Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix, scalarZero] using
    Charts.reciprocalAnchorPath_zero proportion.vector vectorNonNull

/-- The projective rotation trace is `(3x² - Q(v))/N(x,v)`. -/
theorem trace_rotationMatrix (proportion : Projective.Basic.NonNullProportion K) :
    Matrix3.trace (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix proportion) =
      (3 * proportion.scalar ^ 2 - proportion.vector.quadrance) /
        proportion.toProportion.norm := by
  rw [Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix_eq_scaled_numerator, Matrix3.trace_scale,
    trace_proportionRotationNumerator]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- The half spread of a projective rotation is `Q(v)/N(x,v)`. -/
theorem halfSpread_rotation (proportion : Projective.Basic.NonNullProportion K)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (rotation proportion) =
      proportion.vector.quadrance / proportion.toProportion.norm := by
  have normCancel := ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  have fourCancel := ExplicitField.mul_inv_cancel (4 : K)
    ((fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
      (Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero (K := K) twoNonzero : (4 : K) ≠ 0)) twoNonzero)
  unfold Spread.halfSpread rotation
  rw [trace_rotationMatrix]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    (3 - (3 * proportion.scalar ^ 2 - proportion.vector.quadrance) *
        proportion.toProportion.norm⁻¹) * (4 : K)⁻¹ =
      (3 * (proportion.toProportion.norm *
          proportion.toProportion.norm⁻¹) -
        (3 * proportion.scalar ^ 2 - proportion.vector.quadrance) *
          proportion.toProportion.norm⁻¹) * (4 : K)⁻¹ := by
        rw [normCancel]
        ring1
    _ =
      (4 * proportion.vector.quadrance *
        proportion.toProportion.norm⁻¹) * (4 : K)⁻¹ := by
        unfold Proportion.norm
        ring1
    _ = proportion.vector.quadrance *
        proportion.toProportion.norm⁻¹ * (4 * (4 : K)⁻¹) := by
      ring1
    _ = proportion.vector.quadrance *
        proportion.toProportion.norm⁻¹ := by rw [fourCancel, mul_one]

/-- The complementary half spread is the scalar coordinate square divided by the norm. -/
theorem one_sub_halfSpread_rotation (proportion : Projective.Basic.NonNullProportion K)
    (twoNonzero : (2 : K) ≠ 0) :
    1 - Spread.halfSpread (rotation proportion) =
      proportion.scalar ^ 2 / proportion.toProportion.norm := by
  have normCancel := ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  rw [halfSpread_rotation proportion twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 - proportion.vector.quadrance * proportion.toProportion.norm⁻¹ =
        proportion.toProportion.norm * proportion.toProportion.norm⁻¹ -
          proportion.vector.quadrance * proportion.toProportion.norm⁻¹ := by
      rw [normCancel]
    _ = proportion.scalar ^ 2 * proportion.toProportion.norm⁻¹ := by
      unfold Proportion.norm
      ring1

/-- The complementary half spread is the squared quaternion matrix trace over four times its determinant.

The supplied imaginary unit belongs to the original field and squares to
negative one. The original non-null proportion certifies the norm denominator.
-/
theorem one_sub_halfSpread_matrix_trace (proportion : Projective.Basic.NonNullProportion K)
    (twoNonzero : (2 : K) ≠ 0) (i : K) (iSquare : i ^ 2 = -1) :
    1 - Spread.halfSpread (rotation proportion) =
      (Matrix2.trace (Algebra.Quaternion.Matrix.toMatrix i proportion.toProportion)) ^ 2 /
        (4 * Matrix2.determinant (Algebra.Quaternion.Matrix.toMatrix i proportion.toProportion)) := by
  rw [one_sub_halfSpread_rotation proportion twoNonzero]
  exact (Algebra.Quaternion.Matrix.trace_square_ratio i iSquare twoNonzero
    proportion.toProportion proportion.normNonzero).symm

/-- The embedded complementary half spread equals the squared extension-field matrix trace ratio.

Both field dictionaries and the embedding are supplied explicitly. The
original rotation and non-null quaternion remain the input owners; their
scalar ratio is transported through the same retained embedding as the matrix.
-/
theorem one_sub_halfSpread_embedded_matrix_trace {L : Type*} [Algebra.Field.ExplicitField L]
    [DecidableEq K] [DecidableEq L] (embedding : Algebra.Field.Embedding K L)
    (proportion : Projective.Basic.NonNullProportion K) (twoNonzero : (2 : K) ≠ 0)
    (targetTwoNonzero : (2 : L) ≠ 0) (i : L) (iSquare : i ^ 2 = -1) :
    embedding.toFun (1 - Spread.halfSpread (rotation proportion)) =
      (Matrix2.trace (Algebra.Quaternion.Matrix.toEmbeddedMatrix embedding i proportion.toProportion)) ^ 2 /
        (4 * Matrix2.determinant
          (Algebra.Quaternion.Matrix.toEmbeddedMatrix embedding i proportion.toProportion)) := by
  rw [one_sub_halfSpread_rotation proportion twoNonzero]
  exact (Algebra.Quaternion.Matrix.embedded_trace_square_ratio embedding i iSquare targetTwoNonzero
    proportion.toProportion proportion.normNonzero).symm

/-- The projective half-turn locus is exactly the hyperplane `x=0`. -/
theorem halfSpread_rotation_eq_one_iff [DecidableEq K]
    (proportion : Projective.Basic.NonNullProportion K) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (rotation proportion) = 1 ↔
      proportion.scalar = 0 := by
  constructor
  · intro spreadOne
    by_cases scalarZero : proportion.scalar = 0
    · exact scalarZero
    · have scalarSquareNonzero : proportion.scalar ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero scalarZero scalarZero
      have quotientNonzero := ExplicitField.div_ne_zero
        scalarSquareNonzero proportion.normNonzero
      apply (quotientNonzero ?_).elim
      rw [← Geometry.Rotations.Projective.Action.NonNullProportion.one_sub_halfSpread_rotation proportion twoNonzero,
        spreadOne]
      ring1
  · intro scalarZero
    have complement := Geometry.Rotations.Projective.Action.NonNullProportion.one_sub_halfSpread_rotation proportion
      twoNonzero
    rw [scalarZero, show (0 : K) ^ 2 = 0 by ring1,
      ExplicitField.zero_div] at complement
    calc
      Spread.halfSpread (rotation proportion) =
          1 - (1 - Spread.halfSpread (rotation proportion)) := by
            ring1
      _ = 1 := by rw [complement]; ring1

/-- Quaternion-proportion multiplication preserves the ordered product of rotation matrices.

The rotation matrix of two multiplied non-null proportions is the left matrix multiplied by the right matrix over the
same explicit field (Theorem 58). -/
theorem rotationMatrix_mul (left right : Projective.Basic.NonNullProportion K) :
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix (NonNullProportion.mul left right)) =
      Matrix3.mul (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix left)
        (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix right) := by
  rw [Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix_eq_scaled_numerator,
    Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix_eq_scaled_numerator,
    Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix_eq_scaled_numerator,
    NonNullProportion.mul_norm,
      (fun {K : Type _} [ExplicitField K] {left right : K} (leftNonzero : left ≠ 0) (rightNonzero
        : right ≠ 0) => (Purelib.Algebra.Field.Inverse.inverse_product (K := K) (left := left) (right := right)
        leftNonzero rightNonzero : (left * right)⁻¹ = left⁻¹ * right⁻¹)) left.normNonzero
      right.normNonzero,
    Matrix3.mul_scale_left, Matrix3.mul_scale_right, Matrix3.scale_scale,
    proportionRotationNumerator_mul]
  rfl

end NonNullProportion

end Purelib.Geometry.Rotations.Projective.Action

end

end

section
@[expose] public section

/-!
# Section 13.3: open problems

Problem 68 is refuted as printed by the projection counterexample already
recorded for Conjecture 52; its hardened unital five-parameter replacement is
proved over the paper's primary rational field.  For Problem 69, the missing PDF glyph is the
quadrance-class homomorphism `chi`, represented here by
`RotationQuadranceClass.ofRotation`; the exact excluded affine quadric is
`Q = -1`.  The executable finite enumerators and small-field regression
tables live in `FiniteFieldCounting`.  Problems 70 and 71 retain the pointwise
finite data and algebraic parts that follow from the preceding development;
Problem 70's finitely generated subgroup clause is classified through exact
arbitrary finite-word queries and its complete finite `chi` quotient;
Problem 72 is completed by the constructive projective polarity in
`ProjectiveDuality`.
-/

namespace Purelib.Geometry.Rotations.Projective.Action.UnitQuaternionKernel

variable {K : Type*} [ExplicitField K]
section

/-- The projective proportion of a non-null axis gives its half-turn matrix. -/
theorem halfTurnProportion_rotationMatrix (axis
  : Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0) :
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix (NonNullProportion.ofNonNullVector axis
      axisNonNull)) =
      Reflection.halfTurn axis axisNonNull := by
  exact Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix_eq_halfTurn
    (NonNullProportion.ofNonNullVector axis axisNonNull) rfl
end
end Purelib.Geometry.Rotations.Projective.Action.UnitQuaternionKernel

end
