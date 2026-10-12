module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Polynomial.Ascending.Rational.Nonnegative.Evaluation

/-- A nonnegative coefficient table has nonnegative value at a nonnegative rational argument. -/
theorem scalarEvalCoefficients_nonnegative {radius :
  Fraction.Rational}
    (radiusNonnegative : 0 ≤ radius) : ∀ coefficients,
    (∀ degree, 0 ≤ Ascending.Rational.Basic.coefficientCoefficients coefficients degree) →
      0 ≤ Ascending.Rational.Evaluation.scalarEvalCoefficients radius coefficients
  | [], _ => le_rfl
  | _ :: remaining, coefficientsNonnegative =>
      add_nonneg (coefficientsNonnegative 0)
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct radiusNonnegative
          (scalarEvalCoefficients_nonnegative
            radiusNonnegative remaining
            (fun degree => coefficientsNonnegative (degree + 1))))

/-- The shifted high-tail value is at most the full value for nonnegative coefficients and argument.

Dropping `count` entries gives a tail multiplied by the argument to that count; all omitted low-degree contributions are
nonnegative. -/
theorem scalarEvalCoefficients_drop_scaled_le
  {radius : Fraction.Rational}
    (radiusNonnegative : 0 ≤ radius) : ∀ coefficients count,
    (∀ degree, 0 ≤ Ascending.Rational.Basic.coefficientCoefficients coefficients degree) →
      radius ^ count *
          Ascending.Rational.Evaluation.scalarEvalCoefficients radius (coefficients.drop count) ≤
        Ascending.Rational.Evaluation.scalarEvalCoefficients radius coefficients
  | coefficients, 0, coefficientsNonnegative => by
      rw [List.drop_zero, pow_zero,
        Fraction.Field.one_mul]
  | [], count + 1, coefficientsNonnegative => by
      change radius ^ (count + 1) * 0 ≤ 0
      rw [Fraction.Field.mul_zero_direct]
  | coefficient :: remaining, count + 1, coefficientsNonnegative => by
      rw [List.drop_succ_cons, pow_succ, Ascending.Rational.Evaluation.scalarEvalCoefficients]
      have tailBound :=
        scalarEvalCoefficients_drop_scaled_le
        radiusNonnegative remaining count
        (fun degree => coefficientsNonnegative (degree + 1))
      calc
        radius ^ count * radius *
            Ascending.Rational.Evaluation.scalarEvalCoefficients radius (remaining.drop count) =
          radius *
            (radius ^ count *
              Ascending.Rational.Evaluation.scalarEvalCoefficients radius (remaining.drop count)) := by
            ring1
        _ ≤ radius * Ascending.Rational.Evaluation.scalarEvalCoefficients radius remaining :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            tailBound radiusNonnegative
        _ ≤ coefficient + radius * Ascending.Rational.Evaluation.scalarEvalCoefficients radius remaining :=
          le_add_of_nonneg_left (coefficientsNonnegative 0)
end Purelib.Polynomial.Ascending.Rational.Nonnegative.Evaluation

end
