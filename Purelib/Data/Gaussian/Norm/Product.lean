module

public import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Quantified movement of two original Gaussian products

The two original products retain their ordered factors. Their difference
splits into factor movement times an original magnitude; the finite
quadrance estimate gives separately paid contributions without identifying
any inputs or replacing a reading by a common witness.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Product

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The difference of two original products has its two-factor quadrance bound. -/
theorem difference_normSq_le (firstLeft lastLeft firstRight lastRight : Canonical) :
    Norm.Basic.normSq (firstLeft * firstRight - lastLeft * lastRight) ≤
      2 * (Norm.Basic.normSq (firstLeft - lastLeft) * Norm.Basic.normSq firstRight +
        Norm.Basic.normSq lastLeft * Norm.Basic.normSq (firstRight - lastRight)) := by
  have identity : firstLeft * firstRight - lastLeft * lastRight =
      (firstLeft - lastLeft) * firstRight + lastLeft * (firstRight - lastRight) := by ring1
  rewrite [identity]
  have bound := Norm.Bounds.normSq_add_le_two
    ((firstLeft - lastLeft) * firstRight) (lastLeft * (firstRight - lastRight))
  rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul] at bound
  exact bound

/-- Separate original factor movements and magnitudes give a computed two-product difference budget. -/
theorem difference_le {firstLeft lastLeft firstRight lastRight : Canonical}
    {leftMovement rightMagnitude leftMagnitude rightMovement : Fraction.Rational}
    (leftClose : Norm.Basic.normSq (firstLeft - lastLeft) ≤ leftMovement)
    (rightBound : Norm.Basic.normSq firstRight ≤ rightMagnitude)
    (leftBound : Norm.Basic.normSq lastLeft ≤ leftMagnitude)
    (rightClose : Norm.Basic.normSq (firstRight - lastRight) ≤ rightMovement) :
    Norm.Basic.normSq (firstLeft * firstRight - lastLeft * lastRight) ≤
      2 * (leftMovement * rightMagnitude + leftMagnitude * rightMovement) := by
  have firstTerm := Arithmetic.mul_le_mul_direct leftClose rightBound
    (Norm.Basic.normSq_nonneg firstRight) ((Norm.Basic.normSq_nonneg (firstLeft - lastLeft)).trans leftClose)
  have lastTerm := Arithmetic.mul_le_mul_direct leftBound rightClose
    (Norm.Basic.normSq_nonneg (firstRight - lastRight)) ((Norm.Basic.normSq_nonneg lastLeft).trans leftBound)
  exact (difference_normSq_le firstLeft lastLeft firstRight lastRight).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct firstTerm lastTerm)
      (by decide +kernel))

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

/-- Two product residuals with the same quarter-radius stage retain that decay after three fixed factors.

The two residual terms retain their original Gaussian values. The fixed
factor quadrances and their displayed ceilings give the same common-stage
scale; all nonnegative multipliers needed by the proof follow from the
supplied squared-norm bounds.
-/
theorem scaled_difference_quarter_le (h w p u d n r : Canonical)
    (W P U D N R : Fraction.Rational) (index : Nat)
    (wBound : Norm.Basic.normSq w ≤ W) (pBound : Norm.Basic.normSq p ≤ P)
    (uBound : Norm.Basic.normSq u ≤ U) (dBound : Norm.Basic.normSq d ≤ quarterRadius D index)
    (nBound : Norm.Basic.normSq n ≤ N) (rBound : Norm.Basic.normSq r ≤ quarterRadius R index) :
    Norm.Basic.normSq (h * w * p * (u * d - n * r)) ≤
      quarterRadius (2 * Norm.Basic.normSq h * W * P * (U * D + N * R)) index := by
  have wNonnegative := (Norm.Basic.normSq_nonneg w).trans wBound
  have pNonnegative := (Norm.Basic.normSq_nonneg p).trans pBound
  have uNonnegative := (Norm.Basic.normSq_nonneg u).trans uBound
  have nNonnegative := (Norm.Basic.normSq_nonneg n).trans nBound
  have firstTerm : Norm.Basic.normSq (u * d) ≤ U * quarterRadius D index :=
    (Norm.Basic.normSq_mul u d).trans_le
      (Arithmetic.mul_le_mul_direct uBound dBound (Norm.Basic.normSq_nonneg d) uNonnegative)
  have lastTerm : Norm.Basic.normSq (n * r) ≤ N * quarterRadius R index :=
    (Norm.Basic.normSq_mul n r).trans_le
      (Arithmetic.mul_le_mul_direct nBound rBound (Norm.Basic.normSq_nonneg r) nNonnegative)
  have difference : Norm.Basic.normSq (u * d - n * r) ≤
      2 * (U * quarterRadius D index + N * quarterRadius R index) :=
    (Norm.Bounds.normSq_sub_le_two (u * d) (n * r)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct firstTerm lastTerm) (by decide +kernel))
  have shrinking : Norm.Basic.normSq (u * d - n * r) ≤ quarterRadius (2 * (U * D + N * R)) index :=
    difference.trans_eq (by
      rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
      ring1)
  have outerBound : Norm.Basic.normSq (h * w * p) ≤ Norm.Basic.normSq h * W * P := by
    rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct wBound (Norm.Basic.normSq_nonneg h)) pBound
      (Norm.Basic.normSq_nonneg p)
      (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg h) wNonnegative)
  have outerNonnegative : 0 ≤ Norm.Basic.normSq h * W * P :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg h) wNonnegative) pNonnegative
  have scaled := Arithmetic.mul_le_mul_direct outerBound shrinking
    (Norm.Basic.normSq_nonneg (u * d - n * r)) outerNonnegative
  exact ((Norm.Basic.normSq_mul (h * w * p) (u * d - n * r)).trans_le scaled).trans_eq (by
    rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
    ring1)

end Purelib.Data.Gaussian.Norm.Product
