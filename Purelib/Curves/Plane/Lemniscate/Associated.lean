module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Lemniscate.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane.Lemniscate

open Purelib.Geometry

@[expose] public section

namespace Purelib.Curves.Plane.Lemniscate.Associated

section Lemniscate

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The associated equation after setting `X=x²`, `Y=y²`. -/
def AssociatedContains (parameter : K) (point :
  Geometry.Plane.Point K) : Prop :=
  (point.x + point.y) ^ 2 =
    2 * parameter * (point.x - point.y)

/-- Squaring a lemniscate point gives a point of its associated equation. -/
theorem squarePoint_associated
    (parameter : K) (point : Geometry.Plane.Point K)
    (onLemniscate : Contains parameter point) :
    AssociatedContains parameter ⟨point.x ^ 2, point.y ^ 2⟩ := by
  unfold Lemniscate.Contains Lemniscate.evaluate at onLemniscate
  unfold AssociatedContains
  calc
    (point.x ^ 2 + point.y ^ 2) ^ 2 =
        2 * parameter * (point.x ^ 2 - point.y ^ 2) := by
      calc
        (point.x ^ 2 + point.y ^ 2) ^ 2 =
            ((point.x ^ 2 + point.y ^ 2) ^ 2 -
                2 * parameter * (point.x ^ 2 - point.y ^ 2)) +
              2 * parameter * (point.x ^ 2 - point.y ^ 2) := by ring1
        _ = 2 * parameter * (point.x ^ 2 - point.y ^ 2) := by
          rw [onLemniscate]
          ring1

/-- The associated parametrization printed in §19.5. -/
def associatedParameterPoint (parameter slope : K) :
  Geometry.Plane.Point K :=
  let denominator := (1 + slope) ^ 2
  ⟨(2 * parameter * (1 - slope)) / denominator,
    (2 * parameter * slope * (1 - slope)) / denominator⟩

/-- Every allowed slope supplies a point of the associated equation. -/
theorem associatedParameterPoint_contains
    (parameter slope : K) (onePlusSlopeNonzero : 1 + slope ≠ 0) :
    AssociatedContains parameter
      (associatedParameterPoint parameter slope) := by
  let denominator := (1 + slope) ^ 2
  have denominatorNonzero : denominator ≠ 0 := by
    unfold denominator
    simpa only [pow_two] using
      Algebra.Field.ExplicitField.mul_ne_zero onePlusSlopeNonzero onePlusSlopeNonzero
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold AssociatedContains
    associatedParameterPoint
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  change
    ((2 * parameter * (1 - slope)) * denominator⁻¹ +
        (2 * parameter * slope * (1 - slope)) * denominator⁻¹) ^ 2 =
      2 * parameter *
        ((2 * parameter * (1 - slope)) * denominator⁻¹ -
          (2 * parameter * slope * (1 - slope)) * denominator⁻¹)
  calc
    ((2 * parameter * (1 - slope)) * denominator⁻¹ +
          (2 * parameter * slope * (1 - slope)) * denominator⁻¹) ^ 2 =
        4 * parameter ^ 2 * (1 - slope) ^ 2 *
          denominator⁻¹ * (denominator * denominator⁻¹) := by
      unfold denominator
      ring1
    _ = 4 * parameter ^ 2 * (1 - slope) ^ 2 * denominator⁻¹ := by
      rw [cancel]
      ring1
    _ = 2 * parameter *
        ((2 * parameter * (1 - slope)) * denominator⁻¹ -
          (2 * parameter * slope * (1 - slope)) * denominator⁻¹) := by
      unfold denominator
      ring1
end Lemniscate

end Purelib.Curves.Plane.Lemniscate.Associated

end
