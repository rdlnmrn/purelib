module

public import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Squared-distance contraction under a common affine blend

The exact finite variance identity bounds the distance between two blended
pairs by the same nonnegative blend of their original endpoint distances.
All points and the original rational blend remain the scalar inputs.
-/

public section

namespace Purelib.Geometry.Rational.Affine.Segment

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- A common unit-interval affine blend contracts squared distance to its weighted endpoint distances. -/
theorem normSq_line_difference_le (first target other last : Canonical)
    {blend : Fraction.Rational} (inside : 0 ≤ blend ∧ blend ≤ 1) :
    Norm.Basic.normSq (Affine.line first (target - first) blend -
      Affine.line other (last - other) blend) ≤
        (1 - blend) * Norm.Basic.normSq (first - other) + blend * Norm.Basic.normSq (target - last) := by
  have variance :
      ((1 - blend) * Norm.Basic.normSq (first - other) + blend * Norm.Basic.normSq (target - last)) -
        Norm.Basic.normSq (Affine.line first (target - first) blend -
          Affine.line other (last - other) blend) =
      (blend * (1 - blend)) * Norm.Basic.normSq ((first - other) - (target - last)) := by
    simp only [Norm.Basic.normSq, Affine.line, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im,
      Basic.mul_re, Basic.mul_im, Cast.ofCoordinate_re, Cast.ofCoordinate_im]
    ring1
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  rewrite [variance]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct inside.1
      (Fraction.Order.Arithmetic.sub_nonneg_direct inside.2)) (Norm.Basic.normSq_nonneg _)

end Purelib.Geometry.Rational.Affine.Segment
