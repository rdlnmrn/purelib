module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Squares
public import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction.Order

/-!
# Rational product allowances

The two original magnitude bounds and two state allowances determine the
product polynomial. Its direct certificates retain all five terms and the
fourfold scaling used by coherent Gaussian multiplication.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent

/-- The state-local polynomial used as a conservative product allowance.

Both magnitude bounds and both squared-error allowances occur explicitly.
Their cross product, two squares and two magnitude-error terms determine the
original rational polynomial. -/
@[expose] public def productBase (leftBound rightBound leftAllowance rightAllowance :
    Fraction.Rational) : Fraction.Rational :=
  leftAllowance * rightAllowance +
    leftAllowance * leftAllowance +
    rightAllowance * rightAllowance +
    leftAllowance * rightBound +
    leftBound * rightAllowance

/-- Four times the conservative polynomial product allowance.

The expression retains both magnitude bounds and both local error allowances
without selecting any limiting value. -/
@[expose] public def productAllowance (leftBound rightBound leftAllowance rightAllowance :
    Fraction.Rational) : Fraction.Rational :=
  4 * productBase leftBound rightBound leftAllowance rightAllowance

/-- The polynomial product allowance is nonnegative for nonnegative bounds and
allowances.

Each retained product is nonnegative under the four displayed weak bounds.
Adding the five terms preserves that sign without changing their factors. -/
public theorem productBase_nonneg {leftBound rightBound leftAllowance
    rightAllowance : Fraction.Rational}
    (leftBoundNonnegative : 0 ≤ leftBound)
    (rightBoundNonnegative : 0 ≤ rightBound)
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    0 ≤ productBase leftBound rightBound leftAllowance rightAllowance := by
  unfold productBase
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg
          (Arithmetic.mul_nonneg_direct
            leftNonnegative rightNonnegative)
          (Arithmetic.mul_nonneg_direct
            leftNonnegative leftNonnegative))
        (Arithmetic.mul_nonneg_direct
          rightNonnegative rightNonnegative))
      (Arithmetic.mul_nonneg_direct
        leftNonnegative rightBoundNonnegative))
    (Arithmetic.mul_nonneg_direct
      leftBoundNonnegative rightNonnegative)

/-- Bound the two product cross terms by the sum of the displayed polynomial
allowances.

The first left allowance and second right allowance must be nonnegative; the
other cross product is controlled by their squares. -/
public theorem product_cross_bound
    (leftBound rightBound leftOne leftTwo rightOne rightTwo : Fraction.Rational)
    (leftOneNonnegative : 0 ≤ leftOne)
    (rightTwoNonnegative : 0 ≤ rightTwo) :
    (leftOne + leftTwo) * (rightOne + rightBound) +
        (leftTwo + leftBound) * (rightOne + rightTwo) ≤
      productBase leftBound rightBound leftOne rightOne +
        productBase leftBound rightBound leftTwo rightTwo := by
  let common :=
    leftOne * rightOne + leftTwo * rightTwo +
      rightBound * (leftOne + leftTwo) +
      leftBound * (rightOne + rightTwo)
  have cross := Squares.twice_mul_le_sq_add_sq leftTwo rightOne
  have extraNonnegative :
      0 ≤ leftOne * leftOne + rightTwo * rightTwo :=
    add_nonneg
      (Arithmetic.mul_nonneg_direct
        leftOneNonnegative leftOneNonnegative)
      (Arithmetic.mul_nonneg_direct
        rightTwoNonnegative rightTwoNonnegative)
  calc
    (leftOne + leftTwo) * (rightOne + rightBound) +
        (leftTwo + leftBound) * (rightOne + rightTwo) =
      common + 2 * leftTwo * rightOne := by
        dsimp only [common]
        ring1
    _ ≤ common + (leftTwo * leftTwo + rightOne * rightOne) :=
      add_le_add_right cross common
    _ ≤ common + (leftTwo * leftTwo + rightOne * rightOne) +
        (leftOne * leftOne + rightTwo * rightTwo) :=
      le_add_of_nonneg_right extraNonnegative
    _ = productBase leftBound rightBound leftOne rightOne +
        productBase leftBound rightBound leftTwo rightTwo := by
      dsimp only [common]
      unfold productBase
      ring1

end Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent
