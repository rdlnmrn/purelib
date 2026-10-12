module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Bounds on Gaussian sums and their movement

Two retained quadrance bounds control the sum of the original Gaussian
values. Bounds on their separate displacements control the sum displacement.
-/

namespace Purelib.Data.Gaussian.Norm.Addition.Bounds

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Two pointwise displacement bounds give twice their sum as a bound on movement of the Gaussian sum. -/
public theorem sum_movement_le (laterLeft
  earlierLeft laterRight earlierRight :
    Basic.Canonical) (leftRadius rightRadius : Fraction.Rational)
    (leftClose : Basic.normSq (laterLeft - earlierLeft) ≤ leftRadius)
    (rightClose : Basic.normSq (laterRight - earlierRight) ≤ rightRadius) :
    Basic.normSq ((laterLeft + laterRight) - (earlierLeft + earlierRight)) ≤
      2 * (leftRadius + rightRadius) := by
  have identity :
      (laterLeft + laterRight) - (earlierLeft + earlierRight) =
        (laterLeft - earlierLeft) + (laterRight - earlierRight) := by
    apply Basic.ext <;>
      simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im] <;> ring1
  rw [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add leftClose rightClose) (by decide))

/-- Two Gaussian norm bounds give twice their sum as a bound on the norm of their sum. -/
public theorem sum_bounded (left right :
  Basic.Canonical)
    (leftBound rightBound : Fraction.Rational)
    (leftSmall : Basic.normSq left ≤ leftBound)
    (rightSmall : Basic.normSq right ≤ rightBound) :
    Basic.normSq (left + right) ≤ 2 * (leftBound + rightBound) :=
  (Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add leftSmall rightSmall) (by decide))

end Purelib.Data.Gaussian.Norm.Addition.Bounds

end
