module

public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Quadrance and finite sensitivity of Gaussian powers

Finite powers preserve Gaussian quadrance exactly. A recursive sensitivity
factor bounds power differences from a common squared-magnitude bound on
the two original inputs. It uses their actual difference, without identifying
the inputs or selecting a common owner.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Power

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Gaussian quadrance preserves the finite scalar power of the original input. -/
theorem normSq_pow (value : Canonical) : (exponent : Nat) →
    Norm.Basic.normSq (value ^ exponent) = Norm.Basic.normSq value ^ exponent
  | 0 => by rewrite [pow_zero, Norm.Basic.normSq_one, pow_zero]; rfl
  | exponent + 1 => by
      rewrite [pow_succ, Norm.Basic.normSq_mul, normSq_pow value exponent, pow_succ]
      rfl

/-- The finite product sensitivity computed from a common squared-magnitude bound. -/
@[expose] def differenceFactor (bound : Fraction.Rational) : Nat → Fraction.Rational
  | 0 => 0
  | exponent + 1 => 2 * (differenceFactor bound exponent * bound + bound ^ exponent)

/-- The next finite sensitivity uses the original previous factor and scalar power bound. -/
theorem differenceFactor_succ (bound : Fraction.Rational) (exponent : Nat) :
    differenceFactor bound (exponent + 1) = 2 * (differenceFactor bound exponent * bound + bound ^ exponent) := rfl

/-- Every computed finite sensitivity is nonnegative at a nonnegative magnitude bound. -/
theorem differenceFactor_nonnegative {bound : Fraction.Rational} (nonnegative : 0 ≤ bound) :
    (exponent : Nat) → 0 ≤ differenceFactor bound exponent
  | 0 => Fraction.Order.Basic.le_refl _
  | exponent + 1 => Arithmetic.mul_nonneg_direct (by decide +kernel) (by
      calc
        0 = 0 + 0 := by decide +kernel
        _ ≤ differenceFactor bound exponent * bound + bound ^ exponent :=
          Arithmetic.add_le_add_direct
            (Arithmetic.mul_nonneg_direct
              (differenceFactor_nonnegative nonnegative exponent) nonnegative)
            (Arithmetic.pow_nonneg_direct nonnegative exponent))

/-- The two original finite powers differ by at most their computed sensitivity times the input displacement.

Both inputs retain their displayed common squared-magnitude bound. The
recursive product estimate keeps their exact difference and accounts for
the previous power difference and the additional original factor.
-/
theorem difference_normSq_le {first last : Canonical} {bound : Fraction.Rational}
    (firstBound : Norm.Basic.normSq first ≤ bound) (lastBound : Norm.Basic.normSq last ≤ bound) :
    (exponent : Nat) → Norm.Basic.normSq (first ^ exponent - last ^ exponent) ≤
      differenceFactor bound exponent * Norm.Basic.normSq (first - last)
  | 0 => by
      rewrite [pow_zero, pow_zero, Gaussian.Basic.sub_self, Norm.Basic.normSq_zero]
      change (0 : Fraction.Rational) ≤ 0 * Norm.Basic.normSq (first - last)
      rewrite [Fraction.Field.zero_mul_direct]
      exact Fraction.Order.Basic.le_refl _
  | exponent + 1 => by
      have nonnegative : 0 ≤ bound := (Norm.Basic.normSq_nonneg first).trans firstBound
      have previous := difference_normSq_le firstBound lastBound exponent
      have powerBound : Norm.Basic.normSq (first ^ exponent) ≤ bound ^ exponent := by
        rewrite [normSq_pow]
        exact Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) firstBound exponent
      have firstTerm : Norm.Basic.normSq ((first ^ exponent - last ^ exponent) * last) ≤
          (differenceFactor bound exponent * Norm.Basic.normSq (first - last)) * bound := by
        rewrite [Norm.Basic.normSq_mul]
        exact Arithmetic.mul_le_mul_direct previous lastBound (Norm.Basic.normSq_nonneg _)
          (Arithmetic.mul_nonneg_direct (differenceFactor_nonnegative nonnegative exponent)
            (Norm.Basic.normSq_nonneg _))
      have secondTerm : Norm.Basic.normSq (first ^ exponent * (first - last)) ≤
          bound ^ exponent * Norm.Basic.normSq (first - last) := by
        rewrite [Norm.Basic.normSq_mul]
        exact Arithmetic.mul_le_mul_of_nonneg_right_direct powerBound (Norm.Basic.normSq_nonneg _)
      have identity : first ^ (exponent + 1) - last ^ (exponent + 1) =
          (first ^ exponent - last ^ exponent) * last + first ^ exponent * (first - last) := by
        rewrite [pow_succ, pow_succ]
        ring1
      rewrite [identity]
      calc
        _ ≤ 2 * (Norm.Basic.normSq ((first ^ exponent - last ^ exponent) * last) +
            Norm.Basic.normSq (first ^ exponent * (first - last))) := Norm.Bounds.normSq_add_le_two _ _
        _ ≤ 2 * ((differenceFactor bound exponent * Norm.Basic.normSq (first - last)) * bound +
            bound ^ exponent * Norm.Basic.normSq (first - last)) :=
          Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct firstTerm secondTerm) (by decide +kernel)
        _ = differenceFactor bound (exponent + 1) * Norm.Basic.normSq (first - last) := by
          rewrite [differenceFactor_succ]
          ring1

end Purelib.Data.Gaussian.Norm.Power
