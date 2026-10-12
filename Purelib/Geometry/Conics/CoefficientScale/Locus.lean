module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 15 worked examples

This module records the book's concrete finite-field conics separately from
the generic constructive proofs.  In particular, Example 15.6 is checked in
the executable eleven-element field without enumerating that field globally.
-/

namespace Purelib.Geometry.Conics.CoefficientScale.Locus

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Two conic representatives whose six coefficients differ by one nonzero scale have exactly the same locus. This is
the quotient-free finite meaning of equality of the book's conic proportions. -/
public theorem conic_contains_iff_of_coefficient_scale
    (source target : Conic K) (scale : K) (scaleNonzero : scale ≠ 0)
    (dScale : source.d = scale * target.d)
    (eScale : source.e = scale * target.e)
    (fScale : source.f = scale * target.f)
    (aScale : source.a = scale * target.a)
    (bScale : source.b = scale * target.b)
    (cScale : source.c = scale * target.c)
    (point : Plane.Point K) :
    source.Contains point ↔ target.Contains point := by
  have evaluationScale :
      source.evaluate point = scale * target.evaluate point := by
    unfold Conic.evaluate
    rw [dScale, eScale, fScale, aScale, bScale, cScale]
    ring1
  have scaleCancel : scale⁻¹ * scale = (1 : K) := by
    calc
      scale⁻¹ * scale = scale * scale⁻¹ := by ring1
      _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel scale scaleNonzero
  constructor
  · intro sourceContains
    unfold Conic.Contains at sourceContains ⊢
    have productZero : scale * target.evaluate point = 0 := by
      rw [← evaluationScale]
      exact sourceContains
    calc
      target.evaluate point = 1 * target.evaluate point := by ring1
      _ = (scale⁻¹ * scale) * target.evaluate point := by rw [scaleCancel]
      _ = scale⁻¹ * (scale * target.evaluate point) := by ring1
      _ = 0 := by rw [productZero]; ring1
  · intro targetContains
    unfold Conic.Contains at targetContains ⊢
    rw [evaluationScale, targetContains]
    ring1

end

end Purelib.Geometry.Conics.CoefficientScale.Locus

end
