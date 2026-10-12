module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Isometry.Reflection
public import Purelib.Geometry.Plane.Isometry.Rotation
import Purelib.Geometry.Plane.Point.Basic
import Purelib.LinearAlgebra.Coordinates2.Orthogonal
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Isometry

open Purelib.LinearAlgebra

/-!
# Divine Proportions, §13.1: translations, rotations, and reflections

This file gives executable isometries for the coordinate transformations in
Examples 13.1–13.3 and proves the composition calculations requested in
Exercises 13.2, 13.4, and 13.5.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Isometry.Composition

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 13.4: outside characteristic two, a unit central rotation cannot also have the coordinate form of a central
reflection. -/
theorem centralRotationPoint_ne_centralReflectionPoint
    [Nontrivial K] (q r t u : K) (unit : q ^ 2 + r ^ 2 = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ ∀ point : Plane.Point K,
      Rotation.centralRotationPoint q r point = Reflection.centralReflectionPoint t u point := by
  intro sameMap
  have firstAxis := sameMap (⟨1, 0⟩ : Plane.Point K)
  have secondAxis := sameMap (⟨0, 1⟩ : Plane.Point K)
  have qEqT : q = t := by
    have projected := congrArg Plane.Point.x firstAxis
    change q * 1 - r * 0 = t * 1 + u * 0 at projected
    calc
      q = q * 1 - r * 0 := by ring1
      _ = t * 1 + u * 0 := projected
      _ = t := by ring1
  have rEqU : r = u := by
    have projected := congrArg Plane.Point.y firstAxis
    change r * 1 + q * 0 = u * 1 - t * 0 at projected
    calc
      r = r * 1 + q * 0 := by ring1
      _ = u * 1 - t * 0 := projected
      _ = u := by ring1
  have negREqU : -r = u := by
    have projected := congrArg Plane.Point.x secondAxis
    change q * 0 - r * 1 = t * 0 + u * 1 at projected
    calc
      -r = q * 0 - r * 1 := by ring1
      _ = t * 0 + u * 1 := projected
      _ = u := by ring1
  have qEqNegT : q = -t := by
    have projected := congrArg Plane.Point.y secondAxis
    change r * 0 + q * 1 = u * 0 - t * 1 at projected
    calc
      q = r * 0 + q * 1 := by ring1
      _ = u * 0 - t * 1 := projected
      _ = -t := by ring1
  have twoQZero : (2 : K) * q = 0 := by
    calc
      (2 : K) * q = q + t := by rw [← qEqT]; ring1
      _ = 0 := by rw [qEqNegT]; ring1
  have twoRZero : (2 : K) * r = 0 := by
    calc
      (2 : K) * r = r + u := by rw [← rEqU]; ring1
      _ = 0 := by rw [← negREqU]; ring1
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  have qZero : q = 0 := by
    calc
      q = 1 * q := by ring1
      _ = (2 * (2 : K)⁻¹) * q := by rw [twoCancel]
      _ = (2 : K)⁻¹ * (2 * q) := by ring1
      _ = 0 := by rw [twoQZero]; ring1
  have rZero : r = 0 := by
    calc
      r = 1 * r := by ring1
      _ = (2 * (2 : K)⁻¹) * r := by rw [twoCancel]
      _ = (2 : K)⁻¹ * (2 * r) := by ring1
      _ = 0 := by rw [twoRZero]; ring1
  have zeroEqualsOne : (0 : K) = 1 := by
    calc
      0 = q ^ 2 + r ^ 2 := by rw [qZero, rZero]; ring1
      _ = 1 := unit
  exact zero_ne_one zeroEqualsOne

/-- Exercise 13.5, reflection-reflection calculation: `σ_{t,u} σ_{q,r} = ρ_{qt+ru,qu-rt}`. -/
theorem centralReflectionPoint_comp (q r t u : K) (point :
  Plane.Point K) :
    Reflection.centralReflectionPoint t u (Reflection.centralReflectionPoint q r point) =
      Rotation.centralRotationPoint (q * t + r * u) (q * u - r * t) point := by
  apply Plane.Point.ext <;>
    simp only [Reflection.centralReflectionPoint, Rotation.centralRotationPoint] <;>
    ring1

/-- Exercise 13.5, rotation-rotation calculation in both orders. -/
theorem centralRotationPoint_comp (q r t u : K) (point :
  Plane.Point K) :
    Rotation.centralRotationPoint q r (Rotation.centralRotationPoint t u point) =
        Rotation.centralRotationPoint (q * t - r * u) (q * u + r * t) point ∧
      Rotation.centralRotationPoint t u (Rotation.centralRotationPoint q r point) =
        Rotation.centralRotationPoint (q * t - r * u) (q * u + r * t) point := by
  constructor <;>
    apply Plane.Point.ext <;>
    simp only [Rotation.centralRotationPoint] <;>
    ring1

/-- Exercise 13.5, collecting the two composition laws together with the unit-pair calculations that make every
displayed map an isometry. -/
theorem exercise_13_5 (q r t u : K)
    (firstUnit : q ^ 2 + r ^ 2 = 1)
    (secondUnit : t ^ 2 + u ^ 2 = 1) (point : Plane.Point K) :
    ((q * t + r * u) ^ 2 + (q * u - r * t) ^ 2 = 1) ∧
      Reflection.centralReflectionPoint t u (Reflection.centralReflectionPoint q r point) =
        Rotation.centralRotationPoint (q * t + r * u) (q * u - r * t) point ∧
      ((q * t - r * u) ^ 2 + (q * u + r * t) ^ 2 = 1) ∧
      Rotation.centralRotationPoint q r (Rotation.centralRotationPoint t u point) =
        Rotation.centralRotationPoint (q * t - r * u) (q * u + r * t) point ∧
      Rotation.centralRotationPoint t u (Rotation.centralRotationPoint q r point) =
        Rotation.centralRotationPoint (q * t - r * u) (q * u + r * t) point := by
  exact ⟨Coordinates2.Orthogonal.centralReflectionComposition_unit q r t u firstUnit secondUnit,
    centralReflectionPoint_comp q r t u point,
    Coordinates2.Orthogonal.centralRotationComposition_unit q r t u firstUnit secondUnit,
    (centralRotationPoint_comp q r t u point).1,
    (centralRotationPoint_comp q r t u point).2⟩

end Purelib.Geometry.Plane.Isometry.Composition

end
