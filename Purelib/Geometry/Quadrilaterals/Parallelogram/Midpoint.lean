module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Quadrilaterals.Parallelogram.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Quadrilaterals

@[expose] public section

/-!
# Divine Proportions, §§3.7–3.8: affine combinations

All parameters and witnesses are field elements.  Membership and uniqueness
are proved by finite coordinate algebra, with the nonzero coordinate selected
by decidable equality rather than by choice.
-/

namespace Purelib.Geometry.Quadrilaterals.Parallelogram.Midpoint

variable {K : Type*} [ExplicitField K]

/-- The midpoint quadrilateral has parallel opposite sides for any four displayed points. This is the division-free core
of Exercise 3.17 (often called Varignon's theorem). -/
theorem midpoint_quadrilateral_side_conditions
    (first second third fourth : Plane.Point K) :
    Parallelogram.Basic.ParallelogramSideConditions
      (Affine.midpoint first second) (Affine.midpoint second third)
      (Affine.midpoint third fourth) (Affine.midpoint first fourth) := by
  unfold Parallelogram.Basic.ParallelogramSideConditions Affine.midpoint
  simp only [ExplicitField.div_eq_mul_inv]
  constructor <;> ring1

/-- If the two diagonal midpoints of four points agree, then the two diagonal midpoints of their side-midpoint
quadrilateral agree with that same point. -/
theorem midpoint_quadrilateral_same_center
    (first second third fourth : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (originalCenter : Affine.midpoint first third = Affine.midpoint second fourth) :
    Affine.midpoint (Affine.midpoint first second) (Affine.midpoint third fourth) =
        Affine.midpoint first third ∧
      Affine.midpoint (Affine.midpoint second third) (Affine.midpoint first fourth) =
        Affine.midpoint first third := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  have centerX := congrArg Plane.Point.x originalCenter
  have centerY := congrArg Plane.Point.y originalCenter
  simp only [Affine.midpoint, ExplicitField.div_eq_mul_inv] at centerX centerY
  constructor
  · apply Plane.Point.ext
    · simp only [Affine.midpoint, ExplicitField.div_eq_mul_inv]
      calc
        ((first.x + second.x) * (2 : K)⁻¹ +
              (third.x + fourth.x) * (2 : K)⁻¹) * (2 : K)⁻¹ =
            ((first.x + third.x) * (2 : K)⁻¹ +
              (second.x + fourth.x) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                ring1
        _ = ((first.x + third.x) * (2 : K)⁻¹ +
              (first.x + third.x) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                rw [← centerX]
        _ = (first.x + third.x) * (2 : K)⁻¹ := by
          calc
            ((first.x + third.x) * (2 : K)⁻¹ +
                  (first.x + third.x) * (2 : K)⁻¹) * (2 : K)⁻¹ =
                (first.x + third.x) * (2 : K)⁻¹ *
                  (2 * (2 : K)⁻¹) := by
                    ring1
            _ = (first.x + third.x) * (2 : K)⁻¹ := by
              rw [twoInverse]
              ring1
    · simp only [Affine.midpoint, ExplicitField.div_eq_mul_inv]
      calc
        ((first.y + second.y) * (2 : K)⁻¹ +
              (third.y + fourth.y) * (2 : K)⁻¹) * (2 : K)⁻¹ =
            ((first.y + third.y) * (2 : K)⁻¹ +
              (second.y + fourth.y) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                ring1
        _ = ((first.y + third.y) * (2 : K)⁻¹ +
              (first.y + third.y) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                rw [← centerY]
        _ = (first.y + third.y) * (2 : K)⁻¹ := by
          calc
            ((first.y + third.y) * (2 : K)⁻¹ +
                  (first.y + third.y) * (2 : K)⁻¹) * (2 : K)⁻¹ =
                (first.y + third.y) * (2 : K)⁻¹ *
                  (2 * (2 : K)⁻¹) := by
                    ring1
            _ = (first.y + third.y) * (2 : K)⁻¹ := by
              rw [twoInverse]
              ring1
  · apply Plane.Point.ext
    · simp only [Affine.midpoint, ExplicitField.div_eq_mul_inv]
      calc
        ((second.x + third.x) * (2 : K)⁻¹ +
              (first.x + fourth.x) * (2 : K)⁻¹) * (2 : K)⁻¹ =
            ((first.x + third.x) * (2 : K)⁻¹ +
              (second.x + fourth.x) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                ring1
        _ = ((first.x + third.x) * (2 : K)⁻¹ +
              (first.x + third.x) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                rw [← centerX]
        _ = (first.x + third.x) * (2 : K)⁻¹ := by
          calc
            ((first.x + third.x) * (2 : K)⁻¹ +
                  (first.x + third.x) * (2 : K)⁻¹) * (2 : K)⁻¹ =
                (first.x + third.x) * (2 : K)⁻¹ *
                  (2 * (2 : K)⁻¹) := by
                    ring1
            _ = (first.x + third.x) * (2 : K)⁻¹ := by
              rw [twoInverse]
              ring1
    · simp only [Affine.midpoint, ExplicitField.div_eq_mul_inv]
      calc
        ((second.y + third.y) * (2 : K)⁻¹ +
              (first.y + fourth.y) * (2 : K)⁻¹) * (2 : K)⁻¹ =
            ((first.y + third.y) * (2 : K)⁻¹ +
              (second.y + fourth.y) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                ring1
        _ = ((first.y + third.y) * (2 : K)⁻¹ +
              (first.y + third.y) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                rw [← centerY]
        _ = (first.y + third.y) * (2 : K)⁻¹ := by
          calc
            ((first.y + third.y) * (2 : K)⁻¹ +
                  (first.y + third.y) * (2 : K)⁻¹) * (2 : K)⁻¹ =
                (first.y + third.y) * (2 : K)⁻¹ *
                  (2 * (2 : K)⁻¹) := by
                    ring1
            _ = (first.y + third.y) * (2 : K)⁻¹ := by
              rw [twoInverse]
              ring1

/-- A nondegenerate parallelogram has a nondegenerate side-midpoint parallelogram. The new first-three-point determinant
is one half of the original determinant; the proof retains that relation in multiplied form. -/
theorem midpoint_quadrilateral_determinant_ne_zero
  [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : Incidence.pointDeterminant first second third ≠ 0)
    (parallelSides : Parallelogram.Basic.ParallelogramSideConditions first second third fourth) :
    Incidence.pointDeterminant
      (Affine.midpoint first second) (Affine.midpoint second third)
      (Affine.midpoint third fourth) ≠ 0 := by
  have originalCenter := Parallelogram.Basic.parallelogram_center first second third fourth
    twoNonzero determinantNonzero parallelSides
  have centerX := congrArg Plane.Point.x originalCenter
  have centerY := congrArg Plane.Point.y originalCenter
  change (first.x + third.x) / 2 = (second.x + fourth.x) / 2 at centerX
  change (first.y + third.y) / 2 = (second.y + fourth.y) / 2 at centerY
  have xSums : first.x + third.x = second.x + fourth.x := by
    calc
      first.x + third.x = ((first.x + third.x) / 2) * 2 := by
        rw [ExplicitField.div_mul_cancel _ twoNonzero]
      _ = ((second.x + fourth.x) / 2) * 2 := by rw [centerX]
      _ = second.x + fourth.x :=
        ExplicitField.div_mul_cancel _ twoNonzero
  have ySums : first.y + third.y = second.y + fourth.y := by
    calc
      first.y + third.y = ((first.y + third.y) / 2) * 2 := by
        rw [ExplicitField.div_mul_cancel _ twoNonzero]
      _ = ((second.y + fourth.y) / 2) * 2 := by rw [centerY]
      _ = second.y + fourth.y :=
        ExplicitField.div_mul_cancel _ twoNonzero
  have fourthX : fourth.x = first.x - second.x + third.x := by
    calc
      fourth.x = first.x + third.x - second.x := by
        rw [xSums]
        ring1
      _ = first.x - second.x + third.x := by ring1
  have fourthY : fourth.y = first.y - second.y + third.y := by
    calc
      fourth.y = first.y + third.y - second.y := by
        rw [ySums]
        ring1
      _ = first.y - second.y + third.y := by ring1
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  have determinantFormula :
      Incidence.pointDeterminant
          (Affine.midpoint first second) (Affine.midpoint second third)
          (Affine.midpoint third fourth) * 2 =
        Incidence.pointDeterminant first second third := by
    calc
      Incidence.pointDeterminant
            (Affine.midpoint first second) (Affine.midpoint second third)
            (Affine.midpoint third fourth) * 2 =
          Incidence.pointDeterminant first second third *
            ((2 * (2 : K)⁻¹) * (2 * (2 : K)⁻¹)) := by
              unfold Incidence.pointDeterminant Affine.midpoint
              simp only [ExplicitField.div_eq_mul_inv]
              rw [fourthX, fourthY]
              ring1
      _ = Incidence.pointDeterminant first second third := by
        rw [twoInverse]
        ring1
  intro midpointDeterminantZero
  apply determinantNonzero
  calc
    Incidence.pointDeterminant first second third =
        Incidence.pointDeterminant
          (Affine.midpoint first second) (Affine.midpoint second third)
          (Affine.midpoint third fourth) * 2 := determinantFormula.symm
    _ = 0 := by rw [midpointDeterminantZero]; ring1

/-- Exercise 3.17: the four side midpoints of a nondegenerate parallelogram again satisfy the finite parallelogram
certificate, and both of its diagonal midpoints are the original parallelogram center. -/
theorem exercise_3_17 [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : Incidence.pointDeterminant first second third ≠ 0)
    (parallelSides : Parallelogram.Basic.ParallelogramSideConditions first second third fourth) :
    Incidence.pointDeterminant
        (Affine.midpoint first second) (Affine.midpoint second third)
        (Affine.midpoint third fourth) ≠ 0 ∧
      Parallelogram.Basic.ParallelogramSideConditions
        (Affine.midpoint first second) (Affine.midpoint second third)
        (Affine.midpoint third fourth) (Affine.midpoint first fourth) ∧
      Affine.midpoint (Affine.midpoint first second) (Affine.midpoint third fourth) =
          Affine.midpoint first third ∧
        Affine.midpoint (Affine.midpoint second third) (Affine.midpoint first fourth) =
          Affine.midpoint first third := by
  have originalCenter := Parallelogram.Basic.parallelogram_center first second third fourth
    twoNonzero determinantNonzero parallelSides
  exact ⟨
    midpoint_quadrilateral_determinant_ne_zero first second third fourth
      twoNonzero determinantNonzero parallelSides,
    midpoint_quadrilateral_side_conditions first second third fourth,
    midpoint_quadrilateral_same_center first second third fourth
      twoNonzero originalCenter⟩

end Purelib.Geometry.Quadrilaterals.Parallelogram.Midpoint

end
