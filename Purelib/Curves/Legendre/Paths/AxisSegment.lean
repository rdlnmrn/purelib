module

public import Purelib.Curves.Legendre.Paths
public import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

/-!
# Original axis-segment coordinates and constant geometry

Both coordinates follow the original endpoint interpolation. Equal endpoint
indices therefore give the same point at every parameter, and intrinsic
regularity of that point computes the original segment safety certificate.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment

open Purelib.Data

/-- Transport the original axis segment along exact equalities of both endpoint parameters.

Equality elimination preserves the complete original geometry and its
horizontal or vertical direction. Only the two endpoint indices change.
-/
@[expose] def castParameters {source target start finish : Gaussian} (segment : AxisSegment source target)
    (first : source = start) (last : target = finish) : AxisSegment start finish := by
  subst start
  subst finish
  exact segment

/-- Exact endpoint transport preserves every actual original affine point reading of the same axis segment. -/
theorem castParameters_pointAt {source target start finish : Gaussian} (segment : AxisSegment source target)
    (first : source = start) (last : target = finish) (parameter : Coordinate) :
    (segment.castParameters first last).pointAt parameter = segment.pointAt parameter := by
  subst start
  subst finish
  rfl

/-- The original real coordinate interpolates the same retained axis endpoints. -/
theorem pointAt_re {start finish : Gaussian} (segment : AxisSegment start finish) (parameter : Coordinate) :
    (segment.pointAt parameter).re = start.re + (finish.re - start.re) * parameter := by
  cases segment with
  | horizontal first last height => rfl
  | vertical real first last =>
    change real = real + (real - real) * parameter
    ring1

/-- The original imaginary coordinate interpolates the same retained axis endpoints. -/
theorem pointAt_im {start finish : Gaussian} (segment : AxisSegment start finish) (parameter : Coordinate) :
    (segment.pointAt parameter).im = start.im + (finish.im - start.im) * parameter := by
  cases segment with
  | horizontal first last height =>
    change height = height + (height - height) * parameter
    ring1
  | vertical real first last => rfl

/-- Every original axis segment with equal endpoint indices evaluates to that same point at every parameter. -/
theorem pointAt_self {point : Gaussian} (segment : AxisSegment point point) (parameter : Coordinate) :
    segment.pointAt parameter = point := by
  apply Gaussian.Basic.ext
  · rewrite [segment.pointAt_re]
    ring1
  · rewrite [segment.pointAt_im]
    ring1

/-- Derive the original safety certificate of an equal-endpoint segment from intrinsic regularity of its point.

The same point is attained at every unit parameter. The original safety
checker consumes these two whole-interval avoidance proofs and computes
both positive singular-value clearances on the actual supplied geometry.
-/
@[expose] def Safe.ofEqualEndpoints {point : Gaussian} (segment : AxisSegment point point)
    (nonzero : point ≠ 0) (notOne : point ≠ 1) : Safe segment := by
  have avoidsZero : segment.Avoids 0 := by
    intro parameter _ _
    rewrite [segment.pointAt_self parameter]
    exact nonzero
  have avoidsOne : segment.Avoids 1 := by
    intro parameter _ _
    rewrite [segment.pointAt_self parameter]
    exact notOne
  exact Safe.ofAvoidance segment avoidsZero avoidsOne

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale normSq_scale)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order.Arithmetic

variable {start finish : Canonical} (segment : AxisSegment start finish)

/-- The actual endpoint and oriented displacement give a common quadrance ceiling for every unit-axis point. -/
@[expose] def quadranceCeiling : Rational :=
  let first := segment.pointAt 0
  let last := segment.pointAt 1
  2 * (Norm.Basic.normSq first + Norm.Basic.normSq (last - first))

/-- The endpoint-derived ceiling reads the same original source and target coordinates. -/
theorem quadranceCeiling_eq : segment.quadranceCeiling =
    2 * (Norm.Basic.normSq start + Norm.Basic.normSq (finish - start)) := by
  unfold quadranceCeiling
  rewrite [segment.pointAt_zero, segment.pointAt_one]
  rfl

/-- The computed whole-axis parameter ceiling is nonnegative, including a stationary axis. -/
theorem quadranceCeiling_nonnegative : 0 ≤ segment.quadranceCeiling := by
  rewrite [segment.quadranceCeiling_eq]
  exact mul_nonneg_direct (by decide +kernel)
    ((show (0 : Rational) = 0 + 0 by ring1).trans_le
      (add_le_add_direct (Norm.Basic.normSq_nonneg start) (Norm.Basic.normSq_nonneg (finish - start))))

/-- Both original coordinate laws retain the literal oriented affine interpolation. -/
theorem pointAt_eq_scale (fraction : Rational) :
    segment.pointAt fraction = start + scale fraction (finish - start) := by
  apply Basic.ext
  · rewrite [segment.pointAt_re, Basic.add_re, Scale.scale_re, Basic.sub_re]
    ring1
  · rewrite [segment.pointAt_im, Basic.add_im, Scale.scale_im, Basic.sub_im]
    ring1

/-- Every point of the full rational unit interval obeys the same endpoint-derived parameter ceiling. -/
theorem pointAt_normSq_le (fraction : Rational) (nonnegative : 0 ≤ fraction) (unit : fraction ≤ 1) :
    Norm.Basic.normSq (segment.pointAt fraction) ≤ segment.quadranceCeiling := by
  have square : fraction ^ 2 ≤ 1 :=
    (show fraction ^ 2 = fraction * fraction by ring1).trans_le
      ((mul_le_mul_direct unit unit nonnegative (by decide +kernel : (0 : Rational) ≤ 1)).trans_eq
        (by ring1))
  have scaled : Norm.Basic.normSq (scale fraction (finish - start)) ≤ Norm.Basic.normSq (finish - start) :=
    (normSq_scale fraction (finish - start)).trans_le
      ((mul_le_mul_of_nonneg_right_direct square (Norm.Basic.normSq_nonneg (finish - start))).trans_eq
        (Field.one_mul _))
  have estimate : Norm.Basic.normSq (segment.pointAt fraction) ≤
      2 * (Norm.Basic.normSq start + Norm.Basic.normSq (finish - start)) :=
    (congrArg Norm.Basic.normSq (segment.pointAt_eq_scale fraction)).trans_le
    ((Norm.Bounds.normSq_add_le_two start (scale fraction (finish - start))).trans
      (mul_le_mul_of_nonneg_left_direct
        (add_le_add_direct (Order.Basic.le_refl _) scaled) (by decide +kernel)))
  exact estimate.trans_eq segment.quadranceCeiling_eq.symm

end Purelib.Curves.Legendre.Paths.AxisSegment
