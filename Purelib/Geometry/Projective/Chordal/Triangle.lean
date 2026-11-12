module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Hermitian

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Hermitian

section
@[expose] public section

/-!
# Choice-free projective quadrance over constructive Gaussian fractions

This is the finite projective geometry used by the constructive CCL layer.  It
is deliberately separate from `Purelib.CCL.Geometry.Chordal`, whose coordinates are Mathlib's
`Rat`.  Every coordinate here is an explicit quotient of an integer numerator
and a positive integer denominator.
-/

namespace Purelib.Geometry.Projective.Chordal.Triangle

/-- Square-root-free triangle estimate for squared chordal quadrance. The factor two keeps the statement entirely inside
constructive fractions. -/
theorem chordalSq_triangle_two {x y z :
  Line.GaussianLine}
    (hx : (Proj.HasNonzeroCoordinate x)) (hy : (Proj.HasNonzeroCoordinate y))
    (hz : (Proj.HasNonzeroCoordinate z)) :
    Basic.chordalSq x z ≤ 2 * (Basic.chordalSq x y + Basic.chordalSq y z) := by
  have hxWeight : 0 < (Proj.weight x) := Proj.weight_pos hx
  have hyWeight : 0 < (Proj.weight y) := Proj.weight_pos hy
  have hzWeight : 0 < (Proj.weight z) := Proj.weight_pos hz
  have expansion := congrArg Basic.normSq (Proj.cross_mul_weight x y z)
  have sumBound := Bounds.normSq_add_le_two
    ((Proj.cross x) y * (Proj.hermitian y) z) ((Proj.cross y) z * (Proj.hermitian y) x)
  have crossBound :
      Basic.normSq ((Proj.cross x) z) * (Proj.weight y) ^ 2 ≤
        2 * (Basic.normSq ((Proj.cross x) y) * ((Proj.weight y) * (Proj.weight z)) +
          Basic.normSq ((Proj.cross y) z) * ((Proj.weight x) * (Proj.weight y))) := by
    calc
      Basic.normSq ((Proj.cross x) z) * (Proj.weight y) ^ 2 =
          Basic.normSq ((Proj.cross x) z * ⟨(Proj.weight y), 0⟩) := by
            simp only [Basic.normSq, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im]
            ring1
      _ = Basic.normSq
          ((Proj.cross x) y * (Proj.hermitian y) z + (Proj.cross y) z * (Proj.hermitian y) x) := expansion
      _ ≤ 2 *
          (Basic.normSq ((Proj.cross x) y * (Proj.hermitian y) z) +
            Basic.normSq ((Proj.cross y) z * (Proj.hermitian y) x)) := sumBound
      _ = 2 *
          (Basic.normSq ((Proj.cross x) y) * Basic.normSq
            ((Proj.hermitian y) z) +
            Basic.normSq ((Proj.cross y) z) * Basic.normSq
              ((Proj.hermitian y) x)) := by
              rw [Basic.normSq_mul, Basic.normSq_mul]
      _ ≤ 2 * (Basic.normSq ((Proj.cross x) y) * ((Proj.weight y) * (Proj.weight z)) +
          Basic.normSq ((Proj.cross y) z) * ((Proj.weight x) * (Proj.weight y))) := by
            apply Arithmetic.mul_le_mul_of_nonneg_left_direct
              (c := 2) _ (by decide)
            apply add_le_add
            · exact Arithmetic.mul_le_mul_of_nonneg_left_direct
                (Proj.normSq_hermitian_le_weight_mul y z)
                (Basic.normSq_nonneg ((Proj.cross x) y))
            · have bound := Proj.normSq_hermitian_le_weight_mul y x
              rw [Fraction.Field.mul_comm (Proj.weight y) (Proj.weight x)] at bound
              exact Arithmetic.mul_le_mul_of_nonneg_left_direct
                bound (Basic.normSq_nonneg ((Proj.cross y) z))
  have cancelled :
      Basic.normSq ((Proj.cross x) z) * (Proj.weight y) ≤
        2 * (Basic.normSq ((Proj.cross x) y) * (Proj.weight z) +
          Basic.normSq ((Proj.cross y) z) * (Proj.weight x)) := by
    apply Arithmetic.le_of_mul_le_mul_right_direct
      (c := (Proj.weight y)) _ hyWeight
    calc
      (Basic.normSq ((Proj.cross x) z) * (Proj.weight y)) * (Proj.weight y) =
          Basic.normSq ((Proj.cross x) z) * (Proj.weight y) ^ 2 := by ring1
      _ ≤ 2 * (Basic.normSq ((Proj.cross x) y) * ((Proj.weight y) * (Proj.weight z)) +
          Basic.normSq ((Proj.cross y) z) * ((Proj.weight x) * (Proj.weight y))) :=
            crossBound
      _ = (2 * (Basic.normSq ((Proj.cross x) y) * (Proj.weight z) +
          Basic.normSq ((Proj.cross y) z) * (Proj.weight x))) * (Proj.weight y) := by ring1
  rw [Basic.chordalSq_eq_cross, Basic.chordalSq_eq_cross, Basic.chordalSq_eq_cross]
  have xzPositive : 0 < (Proj.weight x) * (Proj.weight z) :=
    Arithmetic.mul_pos_direct hxWeight hzWeight
  apply (Field.div_le_iff_pos xzPositive).2
  apply Arithmetic.le_of_mul_le_mul_right_direct
    (c := (Proj.weight y)) _ hyWeight
  calc
    (Basic.normSq ((Proj.cross x) z) * (Proj.weight y)) =
        Basic.normSq ((Proj.cross x) z) * (Proj.weight y) := rfl
    _ ≤ 2 * (Basic.normSq ((Proj.cross x) y) * (Proj.weight z) +
        Basic.normSq ((Proj.cross y) z) * (Proj.weight x)) := cancelled
    _ = (2 *
        (Basic.normSq ((Proj.cross x) y) / ((Proj.weight x) * (Proj.weight y)) +
          Basic.normSq ((Proj.cross y) z) / ((Proj.weight y) * (Proj.weight z))) *
        ((Proj.weight x) * (Proj.weight z))) * (Proj.weight y) := by
      have xyNonzero : (Proj.weight x) * (Proj.weight y) ≠ 0 :=
        (Arithmetic.mul_pos_direct hxWeight hyWeight).ne'
      have yzNonzero : (Proj.weight y) * (Proj.weight z) ≠ 0 :=
        (Arithmetic.mul_pos_direct hyWeight hzWeight).ne'
      have leftCancel :
          (Basic.normSq ((Proj.cross x) y) / ((Proj.weight x) * (Proj.weight y)) *
              ((Proj.weight x) * (Proj.weight z))) * (Proj.weight y) =
            Basic.normSq ((Proj.cross x) y) * (Proj.weight z) := by
        calc
          (Basic.normSq ((Proj.cross x) y) / ((Proj.weight x) * (Proj.weight y)) *
              ((Proj.weight x) * (Proj.weight z))) * (Proj.weight y) =
              (Basic.normSq ((Proj.cross x) y) / ((Proj.weight x) * (Proj.weight y)) *
                ((Proj.weight x) * (Proj.weight y))) * (Proj.weight z) := by ring1
          _ = Basic.normSq ((Proj.cross x) y) * (Proj.weight z) :=
            congrArg (fun value => value * (Proj.weight z))
              (Fraction.Field.div_mul_cancel_of_ne _ _ xyNonzero)
      have rightCancel :
          (Basic.normSq ((Proj.cross y) z) / ((Proj.weight y) * (Proj.weight z)) *
              ((Proj.weight x) * (Proj.weight z))) * (Proj.weight y) =
            Basic.normSq ((Proj.cross y) z) * (Proj.weight x) := by
        calc
          (Basic.normSq ((Proj.cross y) z) / ((Proj.weight y) * (Proj.weight z)) *
              ((Proj.weight x) * (Proj.weight z))) * (Proj.weight y) =
              (Basic.normSq ((Proj.cross y) z) / ((Proj.weight y) * (Proj.weight z)) *
                ((Proj.weight y) * (Proj.weight z))) * (Proj.weight x) := by ring1
          _ = Basic.normSq ((Proj.cross y) z) * (Proj.weight x) :=
            congrArg (fun value => value * (Proj.weight x))
              (Fraction.Field.div_mul_cancel_of_ne _ _ yzNonzero)
      rw [← leftCancel, ← rightCancel]
      ring1

end Purelib.Geometry.Projective.Chordal.Triangle

end
