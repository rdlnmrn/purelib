module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
public import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

public section

/-! # Certified root chords inside the fixed padded reciprocal disk -/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data (Contains)
open Purelib.Riemann.RootContinuation.RootRadialGeometry (chord)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Scale (scale)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}

section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

/-- The original disk padding squared, divided by the collar radius squared, sets the root approximation tolerance. -/
@[expose] def squareTolerance
    (data : Data cap) : Coordinate := data.padding ^ 2 / ReciprocalExteriorCollar.radius curve ^ 2

/-- The retained padding and collar radius make the root approximation tolerance strictly positive. -/
theorem squareTolerance_positive
    (data : Data cap) : 0 < data.squareTolerance :=
  Field.div_pos_direct (Arithmetic.pow_pos_direct data.positive 2)
    (ReciprocalExteriorCollar.radius_square_positive curve)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry.Data

/-- Bound a weighted squared norm of a sum by the two original squared norms and the exact weight factors. -/
private theorem weighted_sum (weight : Coordinate) (first last : Gaussian) :
    weight * normSq (first + last) ≤ (weight + weight ^ 2) * normSq first + (1 + weight) * normSq last := by
  apply Arithmetic.le_of_sub_nonneg_direct
  exact (normSq_nonneg (scale weight first - last)).trans_eq (by
    simp only [normSq, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Scale.scale_re, Scale.scale_im]
    ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

/-- The square tolerance is chosen before the source stage; the resulting root coordinate and its whole chord may then
use uniform cap bounds. -/
theorem contains_square
    (data : Data cap) {point root : Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point)
    (square : normSq (root * root - point) ≤ data.squareTolerance) : data.Contains (root * root) := by
  have insideBound := inside
  simp only [Reciprocal.Bounds.InDisk, Norm.Basic.normSq_eq_canonical] at insideBound
  change ReciprocalExteriorCollar.radius curve ^ 2 * Norm.Basic.normSq (root * root) ≤ (1 +
    data.padding) ^ 2
  rw [Norm.Basic.normSq_eq_canonical]
  have error : ReciprocalExteriorCollar.radius curve ^ 2 * normSq (root * root - point) ≤ data.padding ^ 2 := by
    have estimate := Arithmetic.mul_le_mul_of_nonneg_left_direct square
      (ReciprocalExteriorCollar.radius_square_positive curve).le
    exact estimate.trans_eq ((Fraction.Field.mul_comm _ _).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (ReciprocalExteriorCollar.radius_square_positive curve).ne'))
  have estimate := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (ReciprocalPaddedRootGeometry.Data.weighted_sum data.padding point (root *
      root - point)) (ReciprocalExteriorCollar.radius_square_positive curve).le
  rw [show point + (root * root - point) = root * root by ring1] at estimate
  have normalized : ReciprocalExteriorCollar.radius curve ^ 2 *
      ((data.padding + data.padding ^ 2) * normSq point + (1 + data.padding) * normSq (root * root - point)) =
      (data.padding + data.padding ^ 2) * (ReciprocalExteriorCollar.radius curve ^ 2 * normSq point) +
        (1 + data.padding) * (ReciprocalExteriorCollar.radius curve ^ 2 * normSq (root * root - point)) := by ring1
  have bound := add_le_add
    (Arithmetic.mul_le_mul_of_nonneg_left_direct insideBound
      (add_nonneg data.positive.le (Arithmetic.sq_nonneg_direct data.padding)))
    (Arithmetic.mul_le_mul_of_nonneg_left_direct error (add_nonneg (by
        decide : (0 : Coordinate) ≤ 1) data.positive.le))
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := data.padding) _ data.positive
  exact (show ReciprocalExteriorCollar.radius curve ^ 2 * normSq (root * root) * data.padding =
    ReciprocalExteriorCollar.radius curve ^ 2 * (data.padding * normSq (root * root)) by ring1).trans_le
      (estimate.trans (normalized.trans_le (bound.trans_eq (by ring1))))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry.Data

/-- A chord point at a unit-interval parameter has squared norm at most the larger endpoint squared norm.

The unit-interval weights are nonnegative, and the squared difference of the original endpoints pays the convex chord
estimate. -/
private theorem chord_norm_le (first last : Gaussian) {parameter :
  Coordinate}
    (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (chord first last parameter) ≤ max (normSq first) (normSq last) := by
  have complement := Arithmetic.sub_nonneg_direct unit.2
  have firstBound := Arithmetic.sub_nonneg_direct (Basic.le_max_left (normSq first)
    (normSq last))
  have lastBound := Arithmetic.sub_nonneg_direct (Basic.le_max_right (normSq first)
    (normSq last))
  apply Arithmetic.le_of_sub_nonneg_direct
  have nonnegative := add_nonneg (add_nonneg
    (Arithmetic.mul_nonneg_direct complement firstBound)
    (Arithmetic.mul_nonneg_direct unit.1 lastBound))
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct unit.1 complement)
      (normSq_nonneg (last - first)))
  exact nonnegative.trans_eq (by
    simp only [chord, normSq, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Scale.scale_re,
      Scale.scale_im]
    ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

/-- Every point on a chord whose squared endpoints lie in the original padded disk also has its square in that disk.

Both original endpoint squares lie in the same retained padded disk, whose squared-norm bound also controls the whole
unit-interval chord. -/
theorem chord_square
    (data : Data cap) {first last : Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last))
    {parameter : Coordinate} (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
    data.Contains (chord first last parameter * chord first last parameter) := by
  change ReciprocalExteriorCollar.radius curve ^ 2 * Norm.Basic.normSq
    (chord first last parameter * chord first last parameter) ≤ (1 + data.padding)
      ^ 2
  rw [Norm.Basic.normSq_eq_canonical]
  have square := Arithmetic.pow_le_pow_direct (normSq_nonneg _)
    (ReciprocalPaddedRootGeometry.Data.chord_norm_le first last unit) 2
  have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct square
    (ReciprocalExteriorCollar.radius_square_positive curve).le
  have maxBound : ReciprocalExteriorCollar.radius curve ^ 2 * max (normSq first) (normSq last) ^ 2 ≤ (1 + data.padding)
    ^ 2 := by
    rcases Basic.le_total (normSq first) (normSq last) with order | order
    · rw [Basic.max_eq_right order]
      have endpointBound := lastInside
      change ReciprocalExteriorCollar.radius curve ^ 2 *
        Norm.Basic.normSq (last * last) ≤ (1 + data.padding) ^ 2 at endpointBound
      rw [Norm.Basic.normSq_eq_canonical,
        normSq_mul] at endpointBound
      have square : normSq last ^ 2 = normSq last * normSq last := by ring1
      rw [square]
      exact endpointBound
    · rw [Basic.max_eq_left order]
      have endpointBound := firstInside
      change ReciprocalExteriorCollar.radius curve ^ 2 *
        Norm.Basic.normSq (first * first) ≤ (1 + data.padding) ^ 2 at endpointBound
      rw [Norm.Basic.normSq_eq_canonical,
        normSq_mul] at endpointBound
      have square : normSq first ^ 2 = normSq first * normSq first := by ring1
      rw [square]
      exact endpointBound
  exact (show ReciprocalExteriorCollar.radius curve ^ 2 * normSq
    (chord first last parameter * chord first last parameter) =
      ReciprocalExteriorCollar.radius curve ^ 2 * normSq (chord first last parameter) ^ 2 by
        rw [normSq_mul]; ring1).trans_le (bound.trans maxBound)

/-- A root whose square lies in the original padded disk has squared norm at most two. -/
theorem root_norm_le
    (data : Data cap) {root : Gaussian} (inside : data.Contains (root *
      root)) : normSq root ≤ 2 := by
  have bound := data.norm_le inside
  simp only [Norm.Basic.normSq_eq_canonical] at bound
  rw [normSq_mul] at bound
  exact Arithmetic.le_of_sq_le_sq_direct (by decide : (0 : Coordinate) ≤ 2)
    ((show normSq root ^ 2 = normSq root * normSq root by ring1).trans_le (bound.trans_eq (by
        decide : (4 : Coordinate) = 2 ^ 2)))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

end
end
