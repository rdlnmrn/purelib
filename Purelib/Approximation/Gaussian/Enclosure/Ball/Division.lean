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

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

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
  : Apart denominator) : Ball :=
  let denominatorCenterNorm := Basic.normSq denominator.center
  { center := numerator.center / denominator.center
    radiusSq :=
      (2 * (numerator.radiusSq * denominatorCenterNorm +
        Basic.normSq numerator.center * denominator.radiusSq)) /
      (apart.lowerSq * denominatorCenterNorm)
    radiusSq_nonneg :=
      Field.div_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (Arithmetic.mul_nonneg_direct
              numerator.radiusSq_nonneg (Basic.normSq_nonneg denominator.center))
            (Arithmetic.mul_nonneg_direct
              (Basic.normSq_nonneg numerator.center)
              denominator.radiusSq_nonneg)))
        (Arithmetic.mul_nonneg_direct apart.positive.le
          (Basic.normSq_nonneg denominator.center)) }

/-- The division ball admits quotients of readings from its original numerator and denominator balls.

The retained denominator apartness certificate supplies the positive lower quadrance needed by the quotient error bound.
-/
theorem contains_div {numerator denominator :
  Ball}
    (apart : Apart denominator) {x y : Data.Gaussian.Basic.Canonical}
    (xInside : numerator.Contains x) (yInside : denominator.Contains y) :
    (numerator.div denominator apart).Contains (x / y) := by
  have yNormPositive := apart.positive.trans_le (apart.lower yInside)
  have yNonzero : y ≠ 0 := fun zero => by
    rw [zero, Basic.normSq_zero] at yNormPositive
    exact (lt_irrefl _ yNormPositive).elim
  have centerNonzero := (Apart.center_nonzero apart)
  let denominatorCenterNorm := Basic.normSq denominator.center
  let numeratorBound :=
    2 * (numerator.radiusSq * denominatorCenterNorm +
      Basic.normSq numerator.center * denominator.radiusSq)
  let denominatorBound := apart.lowerSq * denominatorCenterNorm
  have denominatorCenterPositive : 0 < denominatorCenterNorm :=
    Basic.normSq_pos centerNonzero
  have denominatorBoundPositive : 0 < denominatorBound :=
    Arithmetic.mul_pos_direct apart.positive
      denominatorCenterPositive
  have numeratorDifference :
      x * denominator.center - numerator.center * y =
        (x - numerator.center) * denominator.center -
          numerator.center * (y - denominator.center) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im] <;> ring1
  have numeratorEstimate :
      Basic.normSq (x * denominator.center - numerator.center * y) ≤
        numeratorBound := by
    rw [numeratorDifference]
    calc
      Basic.normSq ((x - numerator.center) * denominator.center -
          numerator.center * (y - denominator.center)) ≤
          2 *
            (Basic.normSq ((x - numerator.center) * denominator.center) +
              Basic.normSq (numerator.center *
                (y - denominator.center))) := Bounds.normSq_sub_le_two _ _
      _ = 2 *
          (Basic.normSq (x - numerator.center) * denominatorCenterNorm +
            Basic.normSq numerator.center *
              Basic.normSq (y - denominator.center)) := by
        rw [Basic.normSq_mul, Basic.normSq_mul]
      _ ≤ numeratorBound := by
        dsimp only [numeratorBound]
        apply Arithmetic.mul_le_mul_of_nonneg_left_direct
        · exact add_le_add
            (Arithmetic.mul_le_mul_of_nonneg_right_direct
              xInside (Basic.normSq_nonneg denominator.center))
            (Arithmetic.mul_le_mul_of_nonneg_left_direct
              yInside (Basic.normSq_nonneg numerator.center))
        · decide
  have denominatorEstimate : denominatorBound ≤
      Basic.normSq y * denominatorCenterNorm :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      (apart.lower yInside) (Basic.normSq_nonneg denominator.center)
  have quotientIdentity :
      x / y - numerator.center / denominator.center =
        (x * denominator.center - numerator.center * y) /
          (y * denominator.center) := by
    exact Data.Gaussian.Field.div_sub_div x numerator.center y denominator.center
      yNonzero centerNonzero
  unfold Contains div
  dsimp only
  rw [quotientIdentity, Data.Gaussian.Field.normSq_div _ _
    (Data.Gaussian.Field.mul_ne_zero_direct yNonzero centerNonzero), Basic.normSq_mul]
  have exactDenominatorPositive :
      0 < Basic.normSq y * denominatorCenterNorm :=
    Arithmetic.mul_pos_direct (Basic.normSq_pos yNonzero)
      denominatorCenterPositive
  calc
    Basic.normSq (x * denominator.center - numerator.center * y) *
          (Basic.normSq y * denominatorCenterNorm)⁻¹ =
        Basic.normSq (x * denominator.center - numerator.center * y) /
          (Basic.normSq y * denominatorCenterNorm) := by
      rfl
    _ ≤ numeratorBound / (Basic.normSq y * denominatorCenterNorm) := by
      apply (Field.div_le_iff_pos
        exactDenominatorPositive).2
      calc
        Basic.normSq (x * denominator.center - numerator.center * y) ≤
            numeratorBound := numeratorEstimate
        _ = (numeratorBound / (Basic.normSq y * denominatorCenterNorm)) *
            (Basic.normSq y * denominatorCenterNorm) :=
          (Fraction.Field.div_mul_cancel_of_ne numeratorBound
            (Basic.normSq y * denominatorCenterNorm)
            exactDenominatorPositive.ne').symm
    _ ≤ numeratorBound / denominatorBound :=
      Field.div_le_div_of_nonneg_left_direct
        (by
          exact Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg
              (Arithmetic.mul_nonneg_direct
                numerator.radiusSq_nonneg
                (Basic.normSq_nonneg denominator.center))
              (Arithmetic.mul_nonneg_direct
                (Basic.normSq_nonneg numerator.center)
                denominator.radiusSq_nonneg)))
        denominatorBoundPositive denominatorEstimate

/-- Transport a denominator's complete apartness through its original ball equality without changing division. -/
theorem div_cast (numerator : Ball) {original retained : Ball} (same : original = retained)
    (apart : Ball.Apart original) :
    numerator.div retained (Eq.ndrec (motive := fun ball => Ball.Apart ball) apart same) =
      numerator.div original apart := by
  cases same
  rfl

end Ball

end Purelib.Approximation.Gaussian.Enclosure.Ball

end

namespace Purelib.Approximation.Gaussian.Enclosure.Ball

/-- A zero-centred numerator gives the exact quotient radius without evaluating the denominator centre.

The original denominator ball and apartness certificate are retained.
Its strictly positive centre quadrance cancels from the original
radius expression; the numerator radius is not replaced by zero.
-/
public theorem div_radiusSq_of_center_zero (numerator denominator : Ball)
    (apart : Apart denominator) (zero : numerator.center = 0) :
    (numerator.div denominator apart).radiusSq = 2 * numerator.radiusSq / apart.lowerSq := by
  change (2 * (numerator.radiusSq * Basic.normSq denominator.center +
    Basic.normSq numerator.center * denominator.radiusSq)) /
      (apart.lowerSq * Basic.normSq denominator.center) = _
  rewrite [zero, Basic.normSq_zero, Fraction.Field.zero_mul_direct, _root_.add_zero]
  apply Fraction.Field.div_eq_div_of_cross_mul
    (Fraction.Field.mul_ne_zero_direct apart.positive.ne'
      (Basic.normSq_pos (Apart.center_nonzero apart)).ne') apart.positive.ne'
  ring1

end Purelib.Approximation.Gaussian.Enclosure.Ball
