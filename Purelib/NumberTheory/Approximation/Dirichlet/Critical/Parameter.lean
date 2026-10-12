module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic
public import Purelib.NumberTheory.Pell.FiniteBranch
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

open Purelib.NumberTheory

/-!
# Finite sharpness witnesses for the Dirichlet window

This module constructs a wholly rational family of index-one windows.  The
parameters satisfy the Pell identity

`m ^ 2 - 4 * m * n + n ^ 2 = 1`,

so their normalized coordinates approach the quadratic boundary without
introducing its omitted irrational zero.  Every member is finite data and
will carry its own minimal-cylinder certificate.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter

/-- The rational critical parameter `m/n` at a supplied finite stage.

The original natural numerator and denominator are converted through their
canonical denominator-one integer records before division. The same ratio
is retained without a unary natural-cast scan over either Pell coefficient.
-/
@[expose] def pellParameter (stage : Nat) :
  Fraction.Rational :=
  Fraction.Cast.fromInt (Pell.FiniteBranch.pellNumerator stage : Int) /
    Fraction.Cast.fromInt (Pell.FiniteBranch.pellDenominator stage : Int)

/-- The directly computed parameter is exactly the original ratio of the two finite natural Pell coefficients. -/
theorem pellParameter_eq_castRatio (stage : Nat) : pellParameter stage =
    (Pell.FiniteBranch.pellNumerator stage : Fraction.Rational) /
      (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) := by
  rewrite [Fraction.Cast.natCast_eq_fromInt, Fraction.Cast.natCast_eq_fromInt]
  rfl

/-- The finite Pell denominator has positive rational cast. -/
theorem pellDenominator_cast_pos (stage : Nat) :
    (0 : Fraction.Rational) < (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) :=
  Fraction.Cast.Order.natCast_pos_direct (Pell.FiniteBranch.pellDenominator_pos stage)

/-- Clearing the explicitly positive Pell denominator recovers its numerator. -/
theorem pellParameter_mul_denominator (stage :
  Nat) :
    pellParameter stage * (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) =
      (Pell.FiniteBranch.pellNumerator stage : Fraction.Rational) := by
  rewrite [pellParameter_eq_castRatio]
  exact Fraction.Field.div_mul_cancel_of_ne _ _
    (pellDenominator_cast_pos stage).ne'

/-- The parameter polynomial is strictly positive at every finite Pell
stage; after clearing the displayed denominator its value is exactly one. -/
theorem parameterPolynomial_pellParameter_scaled
  (stage : Nat) :
    Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (pellParameter stage) *
        (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 = 1 := by
  have castEquation := congrArg (fun value : Nat => (value : Fraction.Rational))
    (Pell.FiniteBranch.pellEquation stage)
  simp only [Algebra.NatCast.add, Algebra.NatCast.mul, Algebra.NatCast.pow, Nat.cast_ofNat, -eq_self, -iff_self]
    at castEquation
  calc
    Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (pellParameter stage) *
          (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 =
        (pellParameter stage * (Pell.FiniteBranch.pellDenominator stage :
          Fraction.Rational)) ^ 2 -
          4 * (pellParameter stage *
            (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational)) *
              (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) +
          (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 := by
      unfold Dirichlet.Critical.Cylinder.Basic.parameterPolynomial
      ring1
    _ =
        (Pell.FiniteBranch.pellNumerator stage : Fraction.Rational) ^ 2 -
          4 * (Pell.FiniteBranch.pellNumerator stage : Fraction.Rational) *
            (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) +
          (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 := by
      rw [pellParameter_mul_denominator]
    _ = 1 := by
      calc
        (Pell.FiniteBranch.pellNumerator stage : Fraction.Rational) ^ 2 -
              4 * (Pell.FiniteBranch.pellNumerator stage : Fraction.Rational) *
                (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) +
              (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 =
            ((Pell.FiniteBranch.pellNumerator stage : Fraction.Rational) ^ 2 +
                (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2) -
              4 * (Pell.FiniteBranch.pellNumerator stage : Fraction.Rational) *
                (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) := by ring1
        _ = 1 := by rw [castEquation]; ring1

/-- The critical boundary polynomial is positive at every finite Pell parameter.

Its product with the positive squared denominator is exactly one, so no limiting argument is needed. -/
theorem parameterPolynomial_pellParameter_pos
  (stage : Nat) :
    0 < Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (pellParameter stage) := by
  have denominatorSquareNonnegative :
      (0 : Fraction.Rational) ≤ (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have productPositive :
      0 < (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 *
        Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (pellParameter stage) := by
    calc
      (0 : Fraction.Rational) < 1 := by decide
      _ = (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 *
          Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (pellParameter stage) := by
        rw [Fraction.Field.mul_comm,
          parameterPolynomial_pellParameter_scaled]
  exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
    productPositive denominatorSquareNonnegative

/-- The Pell denominator is at most four times its numerator. -/
theorem pellDenominator_le_four_mul_numerator
  (stage : Nat) :
    Pell.FiniteBranch.pellDenominator stage ≤ 4 * Pell.FiniteBranch.pellNumerator stage := by
  unfold Pell.FiniteBranch.pellDenominator
  calc
    Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage ≤
        Pell.FiniteBranch.pellNumerator stage + 3 * Pell.FiniteBranch.pellNumerator stage :=
      Nat.add_le_add_left (Pell.FiniteBranch.pellDifference_bounds stage).2 _
    _ = 4 * Pell.FiniteBranch.pellNumerator stage := by ring1

/-- Three times the Pell numerator is strictly below its denominator. -/
theorem three_mul_numerator_lt_pellDenominator
  (stage : Nat) :
    3 * Pell.FiniteBranch.pellNumerator stage < Pell.FiniteBranch.pellDenominator stage := by
  unfold Pell.FiniteBranch.pellDenominator
  calc
    3 * Pell.FiniteBranch.pellNumerator stage =
        Pell.FiniteBranch.pellNumerator stage + 2 * Pell.FiniteBranch.pellNumerator stage := by ring1
    _ < Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage :=
      Nat.add_lt_add_left (Pell.FiniteBranch.pellDifference_bounds stage).1 _

/-- The displayed Pell parameter is at least one quarter. -/
theorem oneFourth_le_pellParameter (stage : Nat)
  :
    (1 / 4 : Fraction.Rational) ≤ pellParameter stage := by
  rewrite [pellParameter_eq_castRatio]
  have denominatorPositive := pellDenominator_cast_pos stage
  have castDenominatorUpper :
      (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ≤
        (4 * Pell.FiniteBranch.pellNumerator stage : Nat) :=
    Fraction.Cast.Order.natCast_le_direct
      (pellDenominator_le_four_mul_numerator stage)
  apply (Fraction.Order.Field.le_div_iff_pos denominatorPositive).2
  rw [show (1 / 4 : Fraction.Rational) *
      (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) =
        (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) / 4 by
    rw [Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.one_mul]
    exact Fraction.Field.mul_comm _ _]
  apply (Fraction.Order.Field.div_le_iff_pos (by decide)).2
  simpa only [Algebra.NatCast.mul, Nat.cast_ofNat,
    Fraction.Field.mul_comm, -eq_self, -iff_self] using castDenominatorUpper

/-- The displayed Pell parameter is strictly below one third. -/
theorem pellParameter_lt_oneThird (stage : Nat) :
    pellParameter stage < (1 / 3 : Fraction.Rational) := by
  rewrite [pellParameter_eq_castRatio]
  have denominatorPositive := pellDenominator_cast_pos stage
  have castTripleLower :
      (3 * Pell.FiniteBranch.pellNumerator stage : Nat) <
        (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct
      (three_mul_numerator_lt_pellDenominator stage)
  apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
  rw [show (1 / 3 : Fraction.Rational) *
      (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) =
        (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) / 3 by
    rw [Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.one_mul]
    exact Fraction.Field.mul_comm _ _]
  apply (Fraction.Order.Field.lt_div_iff_pos (by decide)).2
  simpa only [Algebra.NatCast.mul, Nat.cast_ofNat,
    Fraction.Field.mul_comm, -eq_self, -iff_self] using castTripleLower

/-- Every finite Pell ratio lies in the exact chamber required by the
minimal-cylinder calculation. -/
theorem pellParameter_isCritical (stage : Nat) :
    Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter (pellParameter stage) :=
  ⟨oneFourth_le_pellParameter stage, pellParameter_lt_oneThird
    stage,
    parameterPolynomial_pellParameter_pos stage⟩
end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter

end
