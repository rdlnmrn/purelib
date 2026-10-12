module
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Ball

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite squared-error enclosures for constructive CCL arithmetic

The standalone CCL word remains a list of bits.  Arithmetic uses a proof
sidecar: a rational centre and a rational squared Euclidean error.  The
operations below transport these finite certificates directly.  They do not
name completed limits or collections of compatible points.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball
section Ball

/-- Division enclosure. The denominator apartness certificate is explicit; without it division is intentionally not a
total arithmetic operation. -/
def div (numerator denominator : Ball) (apart
  : Ball.Apart denominator) : Ball :=
  let denominatorCenterNorm := Data.Gaussian.Norm.Basic.normSq denominator.center
  { center := numerator.center / denominator.center
    radiusSq :=
      (2 * (numerator.radiusSq * denominatorCenterNorm +
        Data.Gaussian.Norm.Basic.normSq numerator.center * denominator.radiusSq)) /
      (apart.lowerSq * denominatorCenterNorm)
    radiusSq_nonneg :=
      Fraction.Order.Field.div_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              numerator.radiusSq_nonneg (Data.Gaussian.Norm.Basic.normSq_nonneg denominator.center))
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              (Data.Gaussian.Norm.Basic.normSq_nonneg numerator.center)
              denominator.radiusSq_nonneg)))
        (Fraction.Order.Arithmetic.mul_nonneg_direct apart.positive.le
          (Data.Gaussian.Norm.Basic.normSq_nonneg denominator.center)) }

/-- The division ball admits quotients of readings from its original numerator and denominator balls.

The retained denominator apartness certificate supplies the positive lower quadrance needed by the quotient error bound.
-/
theorem contains_div {numerator denominator :
  Ball}
    (apart : Ball.Apart denominator) {x y : Data.Gaussian.Basic.Canonical}
    (xInside : numerator.Contains x) (yInside : denominator.Contains y) :
    (numerator.div denominator apart).Contains (x / y) := by
  have yNormPositive := apart.positive.trans_le (apart.lower yInside)
  have yNonzero : y ≠ 0 := fun zero => by
    rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at yNormPositive
    exact (lt_irrefl _ yNormPositive).elim
  have centerNonzero := (Apart.center_nonzero apart)
  let denominatorCenterNorm := Data.Gaussian.Norm.Basic.normSq denominator.center
  let numeratorBound :=
    2 * (numerator.radiusSq * denominatorCenterNorm +
      Data.Gaussian.Norm.Basic.normSq numerator.center * denominator.radiusSq)
  let denominatorBound := apart.lowerSq * denominatorCenterNorm
  have denominatorCenterPositive : 0 < denominatorCenterNorm :=
    Data.Gaussian.Norm.Basic.normSq_pos centerNonzero
  have denominatorBoundPositive : 0 < denominatorBound :=
    Fraction.Order.Arithmetic.mul_pos_direct apart.positive
      denominatorCenterPositive
  have numeratorDifference :
      x * denominator.center - numerator.center * y =
        (x - numerator.center) * denominator.center -
          numerator.center * (y - denominator.center) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im] <;> ring1
  have numeratorEstimate :
      Data.Gaussian.Norm.Basic.normSq (x * denominator.center - numerator.center * y) ≤
        numeratorBound := by
    rw [numeratorDifference]
    calc
      Data.Gaussian.Norm.Basic.normSq ((x - numerator.center) * denominator.center -
          numerator.center * (y - denominator.center)) ≤
          2 *
            (Data.Gaussian.Norm.Basic.normSq ((x - numerator.center) * denominator.center) +
              Data.Gaussian.Norm.Basic.normSq (numerator.center *
                (y - denominator.center))) := Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ = 2 *
          (Data.Gaussian.Norm.Basic.normSq (x - numerator.center) * denominatorCenterNorm +
            Data.Gaussian.Norm.Basic.normSq numerator.center *
              Data.Gaussian.Norm.Basic.normSq (y - denominator.center)) := by
        rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
      _ ≤ numeratorBound := by
        dsimp only [numeratorBound]
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        · exact add_le_add
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              xInside (Data.Gaussian.Norm.Basic.normSq_nonneg denominator.center))
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              yInside (Data.Gaussian.Norm.Basic.normSq_nonneg numerator.center))
        · decide
  have denominatorEstimate : denominatorBound ≤
      Data.Gaussian.Norm.Basic.normSq y * denominatorCenterNorm :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (apart.lower yInside) (Data.Gaussian.Norm.Basic.normSq_nonneg denominator.center)
  have quotientIdentity :
      x / y - numerator.center / denominator.center =
        (x * denominator.center - numerator.center * y) /
          (y * denominator.center) := by
    exact Purelib.Data.Gaussian.Field.div_sub_div x numerator.center y denominator.center
      yNonzero centerNonzero
  unfold Ball.Contains Ball.div
  dsimp only
  rw [quotientIdentity, Data.Gaussian.Field.normSq_div _ _
    (Data.Gaussian.Field.mul_ne_zero_direct yNonzero centerNonzero), Data.Gaussian.Norm.Basic.normSq_mul]
  have exactDenominatorPositive :
      0 < Data.Gaussian.Norm.Basic.normSq y * denominatorCenterNorm :=
    Fraction.Order.Arithmetic.mul_pos_direct (Data.Gaussian.Norm.Basic.normSq_pos yNonzero)
      denominatorCenterPositive
  calc
    Data.Gaussian.Norm.Basic.normSq (x * denominator.center - numerator.center * y) *
          (Data.Gaussian.Norm.Basic.normSq y * denominatorCenterNorm)⁻¹ =
        Data.Gaussian.Norm.Basic.normSq (x * denominator.center - numerator.center * y) /
          (Data.Gaussian.Norm.Basic.normSq y * denominatorCenterNorm) := by
      rfl
    _ ≤ numeratorBound / (Data.Gaussian.Norm.Basic.normSq y * denominatorCenterNorm) := by
      apply (Fraction.Order.Field.div_le_iff_pos
        exactDenominatorPositive).2
      calc
        Data.Gaussian.Norm.Basic.normSq (x * denominator.center - numerator.center * y) ≤
            numeratorBound := numeratorEstimate
        _ = (numeratorBound / (Data.Gaussian.Norm.Basic.normSq y * denominatorCenterNorm)) *
            (Data.Gaussian.Norm.Basic.normSq y * denominatorCenterNorm) :=
          (Fraction.Field.div_mul_cancel_of_ne numeratorBound
            (Data.Gaussian.Norm.Basic.normSq y * denominatorCenterNorm)
            exactDenominatorPositive.ne').symm
    _ ≤ numeratorBound / denominatorBound :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (by
          exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg
              (Fraction.Order.Arithmetic.mul_nonneg_direct
                numerator.radiusSq_nonneg
                (Data.Gaussian.Norm.Basic.normSq_nonneg denominator.center))
              (Fraction.Order.Arithmetic.mul_nonneg_direct
                (Data.Gaussian.Norm.Basic.normSq_nonneg numerator.center)
                denominator.radiusSq_nonneg)))
        denominatorBoundPositive denominatorEstimate

end Ball

end Purelib.Approximation.Gaussian.Enclosure.Ball

end
