module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Group.Negation
public import Purelib.Approximation.Rational.Budget.Product
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Data.Rat

-- Preserve the original subtraction parent with its direct negation-zero law.
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Data.Rat.Fraction.Order

/-!
# Rational semantic quotient allowances

The original magnitude bounds and state allowances determine the division
marginal. Its comparisons with the product allowance, squared lower-quadrance
scaling and requested-target scaling retain the same rational polynomials.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent

/-- A separable state-local numerator allowance for comparing two quotients. It
includes enough squares to absorb the cross-state products without ever
selecting a completed value.

The original rational polynomial retains two square terms and two magnitude-
error terms. Their fixed coefficients absorb the signed cross-state products
while preserving each operand factor. -/
@[expose] public def divisionMarginal (leftBound rightBound leftAllowance rightAllowance :
    Fraction.Rational) : Fraction.Rational :=
  8 * leftAllowance * leftAllowance +
    4 * rightBound * leftAllowance +
    8 * rightAllowance * rightAllowance +
    4 * leftBound * rightAllowance

/-- Nonnegative bounds and allowances give a nonnegative division marginal.

Both magnitude bounds and both error allowances are nonnegative. Each retained
product term is nonnegative, and their sum gives the stated bound. -/
public theorem divisionMarginal_nonneg
    {leftBound rightBound leftAllowance rightAllowance : Fraction.Rational}
    (leftBoundNonnegative : 0 ≤ leftBound)
    (rightBoundNonnegative : 0 ≤ rightBound)
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    0 ≤ divisionMarginal leftBound rightBound
      leftAllowance rightAllowance := by
  unfold divisionMarginal
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct (by decide)
            leftNonnegative) leftNonnegative)
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct (by decide)
            rightBoundNonnegative) leftNonnegative))
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide)
          rightNonnegative) rightNonnegative))
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide)
        leftBoundNonnegative) rightNonnegative)

/-- For nonnegative allowances, the product allowance is at most the division
marginal.

Both original error allowances are nonnegative. The difference of the two
polynomials is four times their squared difference plus their product, so it
is nonnegative. -/
public theorem productAllowance_le_divisionMarginal
    {leftBound rightBound leftAllowance rightAllowance : Fraction.Rational}
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    productAllowance leftBound rightBound leftAllowance rightAllowance ≤
      divisionMarginal leftBound rightBound leftAllowance rightAllowance := by
  have squarePlusProduct :
      0 ≤ (leftAllowance - rightAllowance) *
          (leftAllowance - rightAllowance) +
        leftAllowance * rightAllowance :=
    add_nonneg (by
      simpa only [pow_two] using
        Arithmetic.sq_nonneg_direct
          (leftAllowance - rightAllowance))
      (Arithmetic.mul_nonneg_direct
        leftNonnegative rightNonnegative)
  apply Arithmetic.le_of_sub_nonneg_direct
  have scaled := Arithmetic.mul_nonneg_direct
    (by decide : (0 : Fraction.Rational) ≤ 4) squarePlusProduct
  have identity :
      divisionMarginal leftBound rightBound leftAllowance rightAllowance -
          productAllowance leftBound rightBound leftAllowance rightAllowance =
        4 * ((leftAllowance - rightAllowance) *
          (leftAllowance - rightAllowance) +
            leftAllowance * rightAllowance) := by
    unfold divisionMarginal productAllowance productBase
    ring1
  rw [identity]
  exact scaled

/-- For nonnegative bounds and allowances, the division marginal is at most twice
the product allowance.

All four original bounds and allowances are nonnegative. Subtracting the
marginal from twice the product allowance leaves three nonnegative terms with
the retained original factors. -/
public theorem divisionMarginal_le_two_productAllowance
    {leftBound rightBound leftAllowance rightAllowance : Fraction.Rational}
    (leftBoundNonnegative : 0 ≤ leftBound)
    (rightBoundNonnegative : 0 ≤ rightBound)
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    divisionMarginal leftBound rightBound leftAllowance rightAllowance ≤
      2 * productAllowance leftBound rightBound
        leftAllowance rightAllowance := by
  apply Arithmetic.le_of_sub_nonneg_direct
  have crossNonnegative : 0 ≤ 8 * leftAllowance * rightAllowance :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide)
        leftNonnegative) rightNonnegative
  have leftLinearNonnegative :
      0 ≤ 4 * rightBound * leftAllowance :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide)
        rightBoundNonnegative) leftNonnegative
  have rightLinearNonnegative :
      0 ≤ 4 * leftBound * rightAllowance :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide)
        leftBoundNonnegative) rightNonnegative
  have total := add_nonneg
    (add_nonneg crossNonnegative leftLinearNonnegative)
    rightLinearNonnegative
  have identity :
      2 * productAllowance leftBound rightBound
            leftAllowance rightAllowance -
          divisionMarginal leftBound rightBound
            leftAllowance rightAllowance =
        8 * leftAllowance * rightAllowance +
          4 * rightBound * leftAllowance +
          4 * leftBound * rightAllowance := by
    unfold divisionMarginal productAllowance productBase
    ring1
  rw [identity]
  exact total

/-- Scale the division marginal by four and divide by the square of the retained
lower quadrance.

Both input magnitude bounds and error allowances remain explicit in this
rational quotient-comparison budget. -/
@[expose] public def divisionSemanticAllowance (leftBound rightBound lowerSq leftAllowance
    rightAllowance : Fraction.Rational) : Fraction.Rational :=
  (4 * divisionMarginal leftBound rightBound
      leftAllowance rightAllowance) / (lowerSq * lowerSq)

/-- The semantic division allowance is nonnegative when all retained inputs are
nonnegative.

The retained magnitude bounds, lower quadrance and both allowances are
nonnegative. The marginal numerator is nonnegative and division by the same
nonnegative square preserves the weak sign. -/
public theorem divisionSemanticAllowance_nonneg
    {leftBound rightBound lowerSq leftAllowance rightAllowance : Fraction.Rational}
    (leftBoundNonnegative : 0 ≤ leftBound)
    (rightBoundNonnegative : 0 ≤ rightBound)
    (lowerNonnegative : 0 ≤ lowerSq)
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    0 ≤ divisionSemanticAllowance leftBound rightBound lowerSq
      leftAllowance rightAllowance := by
  apply Fraction.Order.Field.div_nonneg_direct
  · exact Arithmetic.mul_nonneg_direct (by decide)
      (divisionMarginal_nonneg leftBoundNonnegative rightBoundNonnegative
        leftNonnegative rightNonnegative)
  · exact Arithmetic.mul_nonneg_direct
      lowerNonnegative lowerNonnegative

/-- Compute the local division request as one thirty-second of the target times
the lower quadrance squared.

This finite rational request compensates for the displayed denominator floor. -/
@[expose] public def divisionSemanticTarget (lowerSq target : Fraction.Rational) : Fraction.Rational :=
  (target / 32) * (lowerSq * lowerSq)

/-- Positive lower quadrance and requested target give a positive semantic
division request.

The output target and retained lower quadrance are strictly positive. Dividing
the target by the fixed positive constant and multiplying by the original
quadrance square preserves positivity. -/
public theorem divisionSemanticTarget_pos {lowerSq target : Fraction.Rational}
    (lowerPositive : 0 < lowerSq) (targetPositive : 0 < target) :
    0 < divisionSemanticTarget lowerSq target :=
  Arithmetic.mul_pos_direct
    (Fraction.Order.Field.div_pos_direct targetPositive
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 32) (by decide)))
    (Arithmetic.mul_pos_direct lowerPositive lowerPositive)

end Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent
