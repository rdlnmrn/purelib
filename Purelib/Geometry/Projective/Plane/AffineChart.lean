module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic

public import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.LinearAlgebra

@[expose] public section
namespace Purelib.Geometry.Projective.Plane.AffineChart
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Embed a Cartesian point as the homogeneous triple `[x:y:1]`. -/
def ofPoint (point : Plane.Point K) : Coordinates3.Vector K :=
  ⟨point.x, point.y, 1⟩

/-- Read the affine chart by dividing the first two coordinates by the third.

The operation is defined for every triple; the chart laws state the required nonzero denominator explicitly. -/
def affineChart (point : Coordinates3.Vector K) : Plane.Point K :=
  ⟨point.t / point.s, point.r / point.s⟩

/-- Reading the affine chart of an embedded point recovers its coordinates. -/
theorem affineChart_ofPoint [Nontrivial K] (point : Plane.Point K) :
    affineChart (ofPoint point) = point := by
  have oneInverse : (1 : K)⁻¹ = 1 := by
    simpa only [one_mul] using
      (Algebra.Field.ExplicitField.mul_inv_cancel (1 : K) one_ne_zero)
  apply Plane.Point.ext
  · change point.x / (1 : K) = point.x
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv, oneInverse, mul_one]
  · change point.y / (1 : K) = point.y
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv, oneInverse, mul_one]

/-- The affine chart is invariant under a displayed nonzero homogeneous scaling. -/
theorem affineChart_scale
    (factor : K) (point : Coordinates3.Vector K)
    (factorNonzero : factor ≠ 0) (zNonzero : point.s ≠ 0) :
    affineChart (Coordinates3.Vector.scale factor point) = affineChart point := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel factor factorNonzero
  have productInverse :
      (factor * point.s)⁻¹ = point.s⁻¹ * factor⁻¹ := by
    have candidateCancel :
        (factor * point.s) * (point.s⁻¹ * factor⁻¹) = (1 : K) := by
      calc
        _ = (factor * factor⁻¹) * (point.s * point.s⁻¹) := by ring1
        _ = 1 := by
          rw [factorCancel,
            Algebra.Field.ExplicitField.mul_inv_cancel point.s zNonzero]
          exact one_mul 1
    have canonicalCancel :
        (factor * point.s) * (factor * point.s)⁻¹ = (1 : K) :=
      Algebra.Field.ExplicitField.mul_inv_cancel _
        (Algebra.Field.ExplicitField.mul_ne_zero factorNonzero zNonzero)
    calc
      (factor * point.s)⁻¹ = (factor * point.s)⁻¹ * 1 := by rw [mul_one]
      _ = (factor * point.s)⁻¹ *
          ((factor * point.s) * (point.s⁻¹ * factor⁻¹)) := by rw [candidateCancel]
      _ = ((factor * point.s) * (factor * point.s)⁻¹) *
          (point.s⁻¹ * factor⁻¹) := by ring1
      _ = point.s⁻¹ * factor⁻¹ := by rw [canonicalCancel]; exact one_mul _
  apply Plane.Point.ext
  · change (factor * point.t) / (factor * point.s) = point.t / point.s
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, productInverse]
    calc
      factor * point.t * (point.s⁻¹ * factor⁻¹) =
          (factor * factor⁻¹) * (point.t * point.s⁻¹) := by ring1
      _ = point.t * point.s⁻¹ := by rw [factorCancel, one_mul]
  · change (factor * point.r) / (factor * point.s) = point.r / point.s
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, productInverse]
    calc
      factor * point.r * (point.s⁻¹ * factor⁻¹) =
          (factor * factor⁻¹) * (point.r * point.s⁻¹) := by ring1
      _ = point.r * point.s⁻¹ := by rw [factorCancel, one_mul]

end Purelib.Geometry.Projective.Plane.AffineChart
end
