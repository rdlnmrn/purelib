module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Space.Metric
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Space.Metric.DirectionSpread.Residual
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

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Space

open Purelib.Geometry.Space.Metric

open Purelib.LinearAlgebra

section
public section

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

namespace Purelib.Geometry.Space.Polyhedron.Regular.Icosahedron.Witnessed

section

variable {K : Type*} [ExplicitField K]

/-! ## Exercise 26.4: an explicit finite icosahedron -/

/-- A uniformly scaled standard icosahedron neighborhood. Scaling by four removes every `/2` from the usual golden-ratio
coordinates. -/
@[expose] def icosahedronV (root : K) :
  Metric.Point3 K := ⟨0, 4, 2 * (1 + root)⟩
/-- The displayed scaled icosahedron vertex `(4, 2*(1+root), 0)`. -/
@[expose] def icosahedronA (root : K) :
  Metric.Point3 K := ⟨4, 2 * (1 + root), 0⟩
/-- The displayed scaled icosahedron vertex `(0, -4, 2*(1+root))`. -/
@[expose] def icosahedronD (root : K) :
  Metric.Point3 K := ⟨0, -4, 2 * (1 + root)⟩
/-- The displayed scaled icosahedron vertex `(2*(1+root), 0, 4)`. -/
@[expose] def icosahedronE (root : K) :
  Metric.Point3 K := ⟨2 * (1 + root), 0, 4⟩
/-- The displayed scaled icosahedron vertex `(-4, -2*(1+root), 0)`. -/
@[expose] def icosahedronG (root : K) :
  Metric.Point3 K := ⟨-4, -2 * (1 + root), 0⟩

/-- The midpoint of `VE`, written directly in the scaled coordinates. -/
@[expose] def icosahedronM (root : K) :
  Metric.Point3 K := ⟨1 + root, 2, 3 + root⟩

/-- The displayed point `M` really is the midpoint of `VE`, in cleared coordinate form. -/
theorem icosahedronM_midpoint_cleared (root : K)
  :
    Coordinates3.Vector.add (icosahedronV root)
      (icosahedronE root) =
      Coordinates3.Vector.scale 2 (icosahedronM root) := by
  unfold icosahedronV icosahedronE
    icosahedronM Coordinates3.Vector.add Coordinates3.Vector.scale
  congr 1 <;> ring1

/-- All metric and dot-product calculations needed for Exercise 26.4. -/
theorem exercise_26_4_metric_certificates
    (root : K) (rootSquare : root ^ 2 = 5) :
    Coordinates3.Vector.quadrance (Coordinates3.Vector.sub
      (icosahedronD root)
      (icosahedronM root)) = 48 ∧
      Coordinates3.Vector.quadrance (Coordinates3.Vector.sub
        (icosahedronA root)
        (icosahedronM root)) = 48 ∧
      Coordinates3.Vector.quadrance (Coordinates3.Vector.sub
        (icosahedronG root)
        (icosahedronM root)) =
        80 + 32 * root ∧
      Coordinates3.Vector.dot (Coordinates3.Vector.sub
        (icosahedronD root)
        (icosahedronM root))
          (Coordinates3.Vector.sub (icosahedronG root)
            (icosahedronM root)) =
        32 + 16 * root ∧
      Coordinates3.Vector.dot (Coordinates3.Vector.sub
        (icosahedronA root)
        (icosahedronM root))
          (Coordinates3.Vector.sub (icosahedronG root)
            (icosahedronM root)) = -16 ∧
      Coordinates3.Vector.quadrance (Coordinates3.Vector.sub
        (icosahedronA root)
        (icosahedronG root)) =
        32 * (5 + root) := by
  dsimp [icosahedronA,
    icosahedronD,
    icosahedronG,
    icosahedronM,
    Coordinates3.Vector.quadrance, Coordinates3.Vector.dot, Coordinates3.Vector.sub]
  constructor
  · apply Group.eq_of_sub_eq_zero
    calc
      _ = 2 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1
  constructor
  · apply Group.eq_of_sub_eq_zero
    calc
      _ = 6 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1
  constructor
  · apply Group.eq_of_sub_eq_zero
    calc
      _ = 6 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1
  constructor
  · ring1
  constructor
  · apply Group.eq_of_sub_eq_zero
    calc
      _ = -2 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1
  · apply Group.eq_of_sub_eq_zero
    calc
      _ = 16 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1

/-- Exercise 26.4's two exact spreads and final long quadrance. Nonzero hypotheses name precisely the denominators used
in the printed fractions. -/
theorem exercise_26_4
    (root : K) (rootSquare : root ^ 2 = 5)
    (fortyEightNonzero : (48 : K) ≠ 0)
    (longMetricNonzero : (80 : K) + 32 * root ≠ 0)
    (fifteenNonzero : (15 : K) ≠ 0) :
    Coordinates3.Vector.spread
        (Coordinates3.Vector.sub (icosahedronD root)
          (icosahedronM root))
        (Coordinates3.Vector.sub (icosahedronG root)
          (icosahedronM root))
        (by
          rw [(exercise_26_4_metric_certificates root
            rootSquare).1]
          exact fortyEightNonzero)
        (by
          rw [(exercise_26_4_metric_certificates root
            rootSquare).2.2.1]
          exact longMetricNonzero) =
      (10 - 2 * root) / 15 ∧
    Coordinates3.Vector.spread
        (Coordinates3.Vector.sub (icosahedronA root)
          (icosahedronM root))
        (Coordinates3.Vector.sub (icosahedronG root)
          (icosahedronM root))
        (by
          rw [(exercise_26_4_metric_certificates root
            rootSquare).2.1]
          exact fortyEightNonzero)
        (by
          rw [(exercise_26_4_metric_certificates root
            rootSquare).2.2.1]
          exact longMetricNonzero) =
      (10 + 2 * root) / 15 ∧
    Coordinates3.Vector.quadrance (Coordinates3.Vector.sub
      (icosahedronA root)
      (icosahedronG root)) =
      32 * (5 + root) := by
  let metrics := exercise_26_4_metric_certificates root
    rootSquare
  have denominatorNonzero :
      (48 : K) * (80 + 32 * root) ≠ 0 :=
    ExplicitField.mul_ne_zero fortyEightNonzero longMetricNonzero
  constructor
  · rw [DirectionSpread.Residual.directionSpread_residual_formula]
    rw [metrics.1, metrics.2.2.1, metrics.2.2.2.1]
    apply ExplicitField.eq_of_mul_eq_mul_right
      (ExplicitField.mul_ne_zero denominatorNonzero fifteenNonzero)
    have leftCancel := ExplicitField.div_mul_cancel
      (48 * (80 + 32 * root) - (32 + 16 * root) ^ 2)
      denominatorNonzero
    have rightCancel := ExplicitField.div_mul_cancel
      (10 - 2 * root) fifteenNonzero
    calc
      ((48 * (80 + 32 * root) - (32 + 16 * root) ^ 2) /
          (48 * (80 + 32 * root))) *
          ((48 * (80 + 32 * root)) * 15) =
        (48 * (80 + 32 * root) - (32 + 16 * root) ^ 2) * 15 := by
          rw [← mul_assoc, leftCancel]
      _ = (10 - 2 * root) * (48 * (80 + 32 * root)) := by
        apply Group.eq_of_sub_eq_zero
        calc
          (48 * (80 + 32 * root) - (32 + 16 * root) ^ 2) * 15 -
              (10 - 2 * root) * (48 * (80 + 32 * root)) =
            -768 * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [rootSquare]; ring1
      _ = ((10 - 2 * root) / 15) *
          ((48 * (80 + 32 * root)) * 15) := by
        calc
          (10 - 2 * root) * (48 * (80 + 32 * root)) =
              (((10 - 2 * root) / 15) * 15) *
                (48 * (80 + 32 * root)) := by rw [rightCancel]
          _ = ((10 - 2 * root) / 15) *
              ((48 * (80 + 32 * root)) * 15) := by ring1
  constructor
  · rw [DirectionSpread.Residual.directionSpread_residual_formula]
    rw [metrics.2.1, metrics.2.2.1, metrics.2.2.2.2.1]
    apply ExplicitField.eq_of_mul_eq_mul_right
      (ExplicitField.mul_ne_zero denominatorNonzero fifteenNonzero)
    have leftCancel := ExplicitField.div_mul_cancel
      (48 * (80 + 32 * root) - (-16) ^ 2) denominatorNonzero
    have rightCancel := ExplicitField.div_mul_cancel
      (10 + 2 * root) fifteenNonzero
    calc
      ((48 * (80 + 32 * root) - (-16) ^ 2) /
          (48 * (80 + 32 * root))) *
          ((48 * (80 + 32 * root)) * 15) =
        (48 * (80 + 32 * root) - (-16) ^ 2) * 15 := by
          rw [← mul_assoc, leftCancel]
      _ = (10 + 2 * root) * (48 * (80 + 32 * root)) := by
        apply Group.eq_of_sub_eq_zero
        calc
          (48 * (80 + 32 * root) - (-16) ^ 2) * 15 -
              (10 + 2 * root) * (48 * (80 + 32 * root)) =
            -3072 * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [rootSquare]; ring1
      _ = ((10 + 2 * root) / 15) *
          ((48 * (80 + 32 * root)) * 15) := by
        calc
          (10 + 2 * root) * (48 * (80 + 32 * root)) =
              (((10 + 2 * root) / 15) * 15) *
                (48 * (80 + 32 * root)) := by rw [rightCancel]
          _ = ((10 + 2 * root) / 15) *
              ((48 * (80 + 32 * root)) * 15) := by ring1
  · exact metrics.2.2.2.2.2
end
end Purelib.Geometry.Space.Polyhedron.Regular.Icosahedron.Witnessed

end

end
