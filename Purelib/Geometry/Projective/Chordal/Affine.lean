module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line

section
@[expose] public section

/-!
# Choice-free projective quadrance over constructive Gaussian fractions

This is the finite projective geometry used by the constructive CCL layer.  It
is deliberately separate from `Purelib.CCL.Geometry.Chordal`, whose coordinates are Mathlib's
`Rat`.  Every coordinate here is an explicit quotient of an integer numerator
and a positive integer denominator.
-/

namespace Purelib.Geometry.Projective.Chordal.Affine

/-- Affine specialization of squared chordal quadrance. -/
theorem chordalSq_affine (z w : Data.Gaussian.Basic.Canonical) :
    Chordal.Basic.chordalSq (Proj.affine z) (Proj.affine w) =
      Data.Gaussian.Norm.Basic.normSq (z - w) / ((1 + Data.Gaussian.Norm.Basic.normSq z) * (1 +
        Data.Gaussian.Norm.Basic.normSq w)) := by
  have numerator : z * 1 - w * 1 = z - w := by
    rw [Data.Gaussian.Basic.mul_one,
      Data.Gaussian.Basic.mul_one]
  simp only [Chordal.Basic.chordalSq, Proj.affine, numerator, Data.Gaussian.Norm.Basic.normSq_one]
  congr 1
  all_goals ring1

/-- Affine squared-chordal quadrance is bounded by the ordinary displayed Gaussian squared distance. -/
theorem chordalSq_affine_le_normSq (z w :
  Data.Gaussian.Basic.Canonical) :
    Chordal.Basic.chordalSq (Proj.affine z) (Proj.affine w) ≤ Data.Gaussian.Norm.Basic.normSq (z - w) := by
  have leftOne : (1 : Fraction.Rational) ≤ 1 + Data.Gaussian.Norm.Basic.normSq z :=
    le_add_of_nonneg_right (Data.Gaussian.Norm.Basic.normSq_nonneg z)
  have rightOne : (1 : Fraction.Rational) ≤ 1 + Data.Gaussian.Norm.Basic.normSq w :=
    le_add_of_nonneg_right (Data.Gaussian.Norm.Basic.normSq_nonneg w)
  have denominatorOne : (1 : Fraction.Rational) ≤
      (1 + Data.Gaussian.Norm.Basic.normSq z) * (1 + Data.Gaussian.Norm.Basic.normSq w) := by
    calc
      1 = 1 * 1 := by ring1
      _ ≤ (1 + Data.Gaussian.Norm.Basic.normSq z) * (1 + Data.Gaussian.Norm.Basic.normSq w) :=
        Fraction.Order.Arithmetic.mul_le_mul_direct leftOne rightOne
          (by decide)
          (add_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg z))
  rw [chordalSq_affine]
  have quotientBound :=
    Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      (Data.Gaussian.Norm.Basic.normSq_nonneg (z - w)) (show (0 : Fraction.Rational) < 1 by decide)
      denominatorOne
  have divideOne : Data.Gaussian.Norm.Basic.normSq (z - w) / 1 = Data.Gaussian.Norm.Basic.normSq (z -
    w) := by
    calc
      Data.Gaussian.Norm.Basic.normSq (z - w) / 1 =
          (Data.Gaussian.Norm.Basic.normSq (z - w) / 1) * 1 :=
        (Fraction.Field.mul_one_direct _).symm
      _ = Data.Gaussian.Norm.Basic.normSq (z - w) :=
        Fraction.Field.div_mul_cancel_of_ne
          (Data.Gaussian.Norm.Basic.normSq (z - w)) 1 (show (1 : Fraction.Rational) ≠ 0 by decide)
  exact quotientBound.trans_eq divideOne

/-- Squared chordal quadrance from an affine point to `ω`. -/
theorem chordalSq_omega (z : Data.Gaussian.Basic.Canonical) :
    Chordal.Basic.chordalSq (Proj.affine z) Proj.omega =
      1 / (1 + Data.Gaussian.Norm.Basic.normSq z) := by
  simp only [Chordal.Basic.chordalSq, Proj.affine, Proj.omega, Data.Gaussian.Basic.mul_zero,
    Data.Gaussian.Basic.mul_one, Data.Gaussian.Basic.zero_sub, Data.Gaussian.Norm.Basic.normSq_neg,
      Data.Gaussian.Norm.Basic.normSq_one, Data.Gaussian.Norm.Basic.normSq_zero]
  congr 1
  all_goals ring1
end Purelib.Geometry.Projective.Chordal.Affine

end

section
@[expose] public section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

namespace Purelib.Geometry.Projective.Chordal.Affine

/-! ## Completed-block chordal bounds give affine boxes -/

/-- On a fixed bounded affine chart, a chordal bound converts to an ordinary squared-distance bound with the explicit
factor `(1 + K)^2`. -/
theorem normSq_sub_le_of_chordalSq_le
    {left right : Data.Gaussian.Basic.Canonical} {K Q : Fraction.Rational}
    (KNonnegative : 0 ≤ K) (QNonnegative : 0 ≤ Q)
    (leftNorm : Data.Gaussian.Norm.Basic.normSq left ≤ K) (rightNorm : Data.Gaussian.Norm.Basic.normSq
      right ≤ K)
    (chordalBound : Chordal.Basic.chordalSq (Proj.affine left)
      (Proj.affine right) ≤ Q) :
    Data.Gaussian.Norm.Basic.normSq (left - right) ≤ (1 + K) ^ 2 * Q := by
  let denominator := (1 + Data.Gaussian.Norm.Basic.normSq left) * (1 + Data.Gaussian.Norm.Basic.normSq
    right)
  have leftWeightPositive : (0 : Fraction.Rational) < 1 + Data.Gaussian.Norm.Basic.normSq left :=
    add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg left)
  have rightWeightPositive : (0 : Fraction.Rational) < 1 + Data.Gaussian.Norm.Basic.normSq right :=
    add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg right)
  have denominatorPositive : 0 < denominator :=
    Fraction.Order.Arithmetic.mul_pos_direct leftWeightPositive
      rightWeightPositive
  have exactDistance : Data.Gaussian.Norm.Basic.normSq (left - right) =
      Chordal.Basic.chordalSq (Proj.affine left) (Proj.affine right) * denominator := by
    rw [chordalSq_affine]
    exact (Fraction.Field.div_mul_cancel_of_ne
      (Data.Gaussian.Norm.Basic.normSq (left - right)) denominator denominatorPositive.ne').symm
  have denominatorBound : denominator ≤ (1 + K) * (1 + K) := by
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (add_le_add_right leftNorm 1) (add_le_add_right rightNorm 1)
      (add_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg right))
      (add_nonneg (by decide) KNonnegative)
  calc
    Data.Gaussian.Norm.Basic.normSq (left - right) =
        Chordal.Basic.chordalSq (Proj.affine left)
          (Proj.affine right) * denominator := exactDistance
    _ ≤ Q * denominator :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        chordalBound denominatorPositive.le
    _ ≤ Q * ((1 + K) * (1 + K)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        denominatorBound QNonnegative
    _ = (1 + K) ^ 2 * Q := by ring1
end Purelib.Geometry.Projective.Chordal.Affine

end

section
@[expose] public section

/-!
# Affine chordal quadrance over constructive Gaussian fractions

The first paper only needs the affine chart of projective chordal distance.
Keeping that formula here avoids importing the continued-logarithm project's
homogeneous-coordinate and matrix layers into RFAP.
-/

namespace Purelib.Geometry.Projective.Chordal.Affine

/-- Exact squared chordal quadrance between two displayed affine Gaussian rationals. The squared form needs no square
root or completed real number. -/
def affineChordalSq (z w : Data.Gaussian.Basic.Canonical) :
  Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (z - w) / ((1 + Data.Gaussian.Norm.Basic.normSq z) * (1 +
    Data.Gaussian.Norm.Basic.normSq w))

/-- The affine squared chordal expression is nonnegative. -/
theorem affineChordalSq_nonneg (z w : Data.Gaussian.Basic.Canonical) :
    0 <= affineChordalSq z w := by
  exact Fraction.Order.Field.div_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (add_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg z))
      (add_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg w)))

/-- Affine squared chordal quadrance is at most ordinary displayed Gaussian squared distance. -/
theorem affineChordalSq_le_normSq (z w :
  Data.Gaussian.Basic.Canonical) :
    affineChordalSq z w <= Data.Gaussian.Norm.Basic.normSq (z - w) := by
  have leftOne : (1 : Fraction.Rational) <= 1 + Data.Gaussian.Norm.Basic.normSq z :=
    le_add_of_nonneg_right (Data.Gaussian.Norm.Basic.normSq_nonneg z)
  have rightOne : (1 : Fraction.Rational) <= 1 + Data.Gaussian.Norm.Basic.normSq w :=
    le_add_of_nonneg_right (Data.Gaussian.Norm.Basic.normSq_nonneg w)
  have denominatorOne : (1 : Fraction.Rational) <=
      (1 + Data.Gaussian.Norm.Basic.normSq z) * (1 + Data.Gaussian.Norm.Basic.normSq w) := by
    calc
      1 = 1 * 1 := by ring1
      _ <= (1 + Data.Gaussian.Norm.Basic.normSq z) * (1 + Data.Gaussian.Norm.Basic.normSq w) :=
        Fraction.Order.Arithmetic.mul_le_mul_direct leftOne rightOne
          (by decide) (add_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg z))
  have quotientBound :=
    Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      (Data.Gaussian.Norm.Basic.normSq_nonneg (z - w)) (show (0 : Fraction.Rational) < 1 by decide)
      denominatorOne
  have divideOne : Data.Gaussian.Norm.Basic.normSq (z - w) / 1 = Data.Gaussian.Norm.Basic.normSq (z -
    w) := by
    calc
      Data.Gaussian.Norm.Basic.normSq (z - w) / 1 = (Data.Gaussian.Norm.Basic.normSq (z - w) / 1) * 1
        :=
        (Fraction.Field.mul_one_direct _).symm
      _ = Data.Gaussian.Norm.Basic.normSq (z - w) :=
        Fraction.Field.div_mul_cancel_of_ne
          (Data.Gaussian.Norm.Basic.normSq (z - w)) 1 (show (1 : Fraction.Rational) ≠ 0 by decide)
  exact quotientBound.trans_eq divideOne
end Purelib.Geometry.Projective.Chordal.Affine

end

end
