module

public import Purelib.Geometry.Quadratic.Ternary.Lorentz
public import Purelib.Geometry.Rotations.Ternary.Reflection
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.LinearAlgebra.Coordinates3.Independence
import Purelib.Tactic.Ring

/-!
# Time-first Lorentz reflections and half turns

The reflection and half-turn operations remain those of the original
ternary form. The metrical adjoint and coordinate readbacks identify their
time-first realization, while cross-product axes use the signed Lorentz
convention.
-/

public section

namespace Purelib.Geometry.Quadratic.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- The Lorentz reflection uses the time-first dual vector and coordinate quadrance. -/
theorem reflection_coordinates (normal : Vector3 K)
    (nonNull : (Form.lorentz oneNonzero).quadrance normal ≠ 0) :
    (Form.lorentz oneNonzero).reflection normal nonNull =
      Matrix3.sub Matrix3.identity
        (Matrix3.scale (2 / (normal.t ^ 2 - normal.r ^ 2 - normal.s ^ 2))
          (Matrix3.outer ⟨normal.t, -normal.r, -normal.s⟩ normal)) := by
  unfold Form.reflection
  rw [Form.dual_lorentz, Form.quadrance_lorentz]

/-- Every non-null Lorentz reflection equals its metrical adjoint. -/
theorem adjoint_reflection (normal : Vector3 K)
    (nonNull : (Form.lorentz oneNonzero).quadrance normal ≠ 0) :
    adjoint oneNonzero ((Form.lorentz oneNonzero).reflection normal nonNull) =
      (Form.lorentz oneNonzero).reflection normal nonNull := by
  rw [reflection_coordinates, adjoint_coordinates]
  ext <;> unfold Matrix3.sub Matrix3.identity Matrix3.scale Matrix3.outer <;> ring1

/-- A Lorentz half turn is the negative identity plus twice the normal projection. -/
theorem halfTurn_coordinates (axis : Vector3 K)
    (nonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) :
    (Form.lorentz oneNonzero).halfTurn axis nonNull =
      Matrix3.add (Matrix3.scale (-1) Matrix3.identity)
        (Matrix3.scale (2 / (axis.t ^ 2 - axis.r ^ 2 - axis.s ^ 2))
          (Matrix3.outer ⟨axis.t, -axis.r, -axis.s⟩ axis)) := by
  unfold Form.halfTurn
  rw [reflection_coordinates]
  ext <;> unfold Matrix3.neg Matrix3.add Matrix3.sub Matrix3.scale Matrix3.identity <;> ring1

/-- Every non-null Lorentz half turn equals its metrical adjoint. -/
theorem adjoint_halfTurn (axis : Vector3 K)
    (nonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) :
    adjoint oneNonzero ((Form.lorentz oneNonzero).halfTurn axis nonNull) =
      (Form.lorentz oneNonzero).halfTurn axis nonNull := by
  unfold Form.halfTurn
  rw [adjoint_neg, adjoint_reflection]

/-- Independent Lorentz vectors have a nonzero signed cross.

The Lorentz adjugate is the metric itself. Cancelling this invertible metric
reduces a vanished signed cross to a vanished ordinary coordinate cross.
-/
theorem cross_ne_zero_of_independent (first second : Vector3 K)
    (independent : Vector3.Independent first second) : cross oneNonzero first second ≠ Vector3.zero := by
  intro signedCrossZero
  have cliffordZero : (Form.lorentz oneNonzero).cliffordCross first second = Vector3.zero := by
    calc
      _ = Vector3.neg (cross oneNonzero first second) := (Vector3.neg_neg _).symm
      _ = Vector3.neg Vector3.zero := congrArg Vector3.neg signedCrossZero
      _ = Vector3.zero := Vector3.neg_zero
  have coordinateCrossZero : Vector3.cross first second = Vector3.zero := by
    apply (Form.lorentz oneNonzero).eq_zero_of_rowMul_matrix_eq_zero
    unfold Form.cliffordCross at cliffordZero
    rw [Form.lorentz_adjugate] at cliffordZero
    exact cliffordZero
  exact independent coordinateCrossZero

/-- The product of two Lorentz reflections fixes the signed cross of their normals.

Each reflection fixes this cross because it is perpendicular to its normal.
The statement also applies when the cross is null, and requires no quadrance
division for the retained fixed vector itself.
-/
theorem rowMul_reflection_product_cross (first second : Vector3 K)
    (firstNonNull : (Form.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (Form.lorentz oneNonzero).quadrance second ≠ 0) :
    Matrix3.rowMul (cross oneNonzero first second)
        (Matrix3.mul ((Form.lorentz oneNonzero).reflection first firstNonNull)
          ((Form.lorentz oneNonzero).reflection second secondNonNull)) =
      cross oneNonzero first second := by
  rw [← Matrix3.rowMul_mul,
    (Form.lorentz oneNonzero).rowMul_reflection_of_perpendicular first firstNonNull _
      (cross_perpendicular_left oneNonzero first second),
    (Form.lorentz oneNonzero).rowMul_reflection_of_perpendicular second secondNonNull _
      (cross_perpendicular_right oneNonzero first second)]

/-- Every scalar multiple of the cross of two normals is fixed by their reflection product. -/
theorem rowMul_reflection_product_cross_scale (scalar : K) (first second : Vector3 K)
    (firstNonNull : (Form.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (Form.lorentz oneNonzero).quadrance second ≠ 0) :
    Matrix3.rowMul (Vector3.scale scalar (cross oneNonzero first second))
        (Matrix3.mul ((Form.lorentz oneNonzero).reflection first firstNonNull)
          ((Form.lorentz oneNonzero).reflection second secondNonNull)) =
      Vector3.scale scalar (cross oneNonzero first second) := by
  rw [Matrix3.rowMul_vector_scale,
    rowMul_reflection_product_cross oneNonzero first second firstNonNull secondNonNull]

end Purelib.Geometry.Quadratic.Ternary.Lorentz
