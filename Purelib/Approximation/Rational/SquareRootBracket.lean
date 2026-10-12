module
public import Purelib.Algebra.NatCast

import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Nat.SquareRoot
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.NumberTheory.SquareClass.Rational.Basic
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
public import Mathlib.Order.Basic
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.Field.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Nat

open Purelib.Data.Rat

open Purelib.NumberTheory.SquareClass.Rational.Basic

public section

/-!
# Rational square-root brackets

A retained positive numerator and denominator determine a finite integer
radicand at each requested scale. The cached integer square-root floor gives
rational endpoints, certified square bounds and an exact reciprocal width.
-/

namespace Purelib.Approximation.Rational.SquareRootBracket.KernelApproximation

/-! ## Finite square-root brackets -/

set_option genInjectivity false in
/-- Cached finite bracket around the square root of a positive rational target.

The parameter `scale` requests denominator refinement by `scale + 1`. The
record retains the radicand, floor numerator, common denominator, rational
endpoints and their square, sign and exact-width certificates. -/
structure SqrtBracket
    (target : TheoremSixtyTwo.PositiveSquareClassRepresentative)
    (scale : Nat) where
  /-- The cached natural radicand for the requested denominator refinement. -/ radicand : Nat
  /-- The radicand is the target numerator times its denominator times the squared refinement factor. -/ radicand_eq :
    radicand = target.numerator * target.denominator *
    (scale + 1) ^ 2
  /-- The cached integer square-root floor used for the lower endpoint. -/ lowerNumerator : Nat
  /-- The cached lower numerator equals the executable square-root floor of the retained radicand. -/ lowerNumerator_eq
    : lowerNumerator =
    SquareRoot.floor radicand
  /-- The common natural denominator of both rational endpoints. -/ denominator : Nat
  /-- The denominator is the target denominator times the positive refinement factor. -/ denominator_eq : denominator =
    target.denominator * (scale + 1)
  /-- The retained denominator is strictly positive. -/ denominator_positive : 0 < denominator
  /-- The cached lower rational endpoint. -/ lower : Fraction.Rational
  /-- The lower endpoint uses the retained floor numerator and common denominator. -/ lower_eq : lower = (lowerNumerator
    : Fraction.Rational) / (denominator : Fraction.Rational)
  /-- The cached upper rational endpoint. -/ upper : Fraction.Rational
  /-- The upper endpoint uses the successor floor numerator and common denominator. -/ upper_eq : upper =
    (lowerNumerator + 1 : Nat) / (denominator : Fraction.Rational)
  /-- The lower endpoint is nonnegative. -/ lower_nonnegative : 0 ≤ lower
  /-- The upper endpoint is strictly positive. -/ upper_positive : 0 < upper
  /-- The lower endpoint squared is at most the target value. -/ lower_square_le : lower ^ 2 ≤
    target.representative.value
  /-- The target value is strictly below the upper endpoint squared. -/ value_lt_upper_square :
    target.representative.value < upper ^ 2
  /-- The exact endpoint width is the reciprocal of the retained denominator. -/ width_eq : upper - lower = 1 /
    (denominator : Fraction.Rational)

constructive_injectivity SqrtBracket

/-- Compute a finite square-root bracket at the requested denominator scale.

The retained radicand is evaluated once by the owned integer square-root floor.
Its two integer bounds certify the cached rational endpoints and their width. -/
@[expose] def sqrtBracket
    (target : TheoremSixtyTwo.PositiveSquareClassRepresentative)
    (scale : Nat) : SqrtBracket target scale := by
  let refinement := scale + 1
  let radicand := target.numerator * target.denominator * refinement ^ 2
  let lowerNumerator := SquareRoot.floor radicand
  let denominator := target.denominator * refinement
  have refinementPositive : 0 < refinement := by
    unfold refinement
    omega0
  have denominatorPositive : 0 < denominator := by
    unfold denominator
    exact Nat.mul_pos target.denominator_positive refinementPositive
  have lowerNatural : lowerNumerator ^ 2 ≤ radicand := by
    unfold lowerNumerator
    exact SquareRoot.floor_square_le radicand
  have upperNatural : radicand < (lowerNumerator + 1) ^ 2 := by
    unfold lowerNumerator
    exact SquareRoot.lt_floor_succ_square radicand
  have lowerCleared : lowerNumerator ^ 2 * target.denominator ≤
      target.numerator * denominator ^ 2 := by
    calc
      lowerNumerator ^ 2 * target.denominator ≤
          radicand * target.denominator :=
        Nat.mul_le_mul_right target.denominator lowerNatural
      _ = target.numerator * denominator ^ 2 := by
        unfold radicand denominator
        ring1
  have upperCleared : target.numerator * denominator ^ 2 <
      (lowerNumerator + 1) ^ 2 * target.denominator := by
    calc
      target.numerator * denominator ^ 2 =
          radicand * target.denominator := by
        unfold radicand denominator
        ring1
      _ < (lowerNumerator + 1) ^ 2 * target.denominator :=
        Nat.mul_lt_mul_of_pos_right upperNatural target.denominator_positive
  let lower : Fraction.Rational := (lowerNumerator : Fraction.Rational) / (denominator : Fraction.Rational)
  let upper : Fraction.Rational :=
    (lowerNumerator + 1 : Nat) / (denominator : Fraction.Rational)
  refine
    { radicand := radicand
      radicand_eq := rfl
      lowerNumerator := lowerNumerator
      lowerNumerator_eq := rfl
      denominator := denominator
      denominator_eq := rfl
      denominator_positive := denominatorPositive
      lower := lower
      lower_eq := rfl
      upper := upper
      upper_eq := rfl
      lower_nonnegative := ?_
      upper_positive := ?_
      lower_square_le := ?_
      value_lt_upper_square := ?_
      width_eq := ?_ }
  · unfold lower
    exact Fraction.Order.Field.div_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
      (Fraction.Cast.Order.natCast_le_direct
        denominatorPositive.le)
  · unfold upper
    exact Fraction.Order.Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (by omega0))
      (Fraction.Cast.Order.natCast_pos_direct denominatorPositive)
  · unfold lower
    rw [target.value_eq_div]
    exact Fraction.Order.Field.nat_square_div_le_div denominatorPositive
      target.denominator_positive lowerCleared
  · unfold upper
    rw [target.value_eq_div]
    exact Fraction.Order.Field.nat_div_lt_square_div denominatorPositive
      target.denominator_positive upperCleared
  · unfold lower upper
    simp only [Algebra.NatCast.add, Nat.cast_one,
      Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1

/-- The upper-square error is bounded by a reciprocal refinement.

For the retained positive target, the upper endpoint squared exceeds its value
by at most `(2 * target + 3) / (scale + 1)`. The proof uses the cached endpoint
width and square bounds. -/
theorem sqrtBracket_square_error_le
    (target : TheoremSixtyTwo.PositiveSquareClassRepresentative)
    (scale : Nat) (bracket : SqrtBracket target scale) :
    bracket.upper ^ 2 - target.representative.value ≤
      (2 * target.representative.value + 3) /
        (scale + 1 : Nat) := by
  let refinement : Nat := scale + 1
  have refinementPositiveNatural : 0 < refinement := by
    unfold refinement
    omega0
  have refinementPositive : (0 : Fraction.Rational) < (refinement : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      refinementPositiveNatural
  have refinementAtLeastOneNatural : 1 ≤ refinement := by
    unfold refinement
    omega0
  have refinementAtLeastOne : (1 : Fraction.Rational) ≤ (refinement : Fraction.Rational) := by
    simpa only [Nat.cast_one] using
      Fraction.Cast.Order.natCast_le_direct
        refinementAtLeastOneNatural
  have denominatorAtLeastRefinementNatural :
      refinement ≤ bracket.denominator := by
    rw [bracket.denominator_eq]
    have denominatorAtLeastOne : 1 ≤ target.denominator :=
      target.denominator_positive
    calc
      refinement = 1 * refinement := by omega0
      _ ≤ target.denominator * refinement :=
        Nat.mul_le_mul_right refinement denominatorAtLeastOne
  have denominatorAtLeastRefinement :
      (refinement : Fraction.Rational) ≤ (bracket.denominator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct
      denominatorAtLeastRefinementNatural
  have denominatorPositive :
      (0 : Fraction.Rational) < (bracket.denominator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      bracket.denominator_positive
  have widthPositive : 0 < bracket.upper - bracket.lower := by
    rw [bracket.width_eq]
    exact Fraction.Order.Field.div_pos_direct (by decide)
      denominatorPositive
  have widthLeRefinement :
      bracket.upper - bracket.lower ≤ 1 / (refinement : Fraction.Rational) := by
    rw [bracket.width_eq]
    exact Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      (by decide) refinementPositive denominatorAtLeastRefinement
  have widthLeOne : bracket.upper - bracket.lower ≤ 1 := by
    calc
      bracket.upper - bracket.lower ≤ 1 / (refinement : Fraction.Rational) :=
        widthLeRefinement
      _ ≤ 1 / (1 : Fraction.Rational) :=
        Fraction.Order.Field.div_le_div_of_nonneg_left_direct
          (by decide) (by decide) refinementAtLeastOne
      _ = 1 := by decide
  have valueLeSquareSuccessor : target.representative.value ≤
      (target.representative.value + 1) ^ 2 := by
    have extraNonnegative : 0 ≤
        target.representative.value ^ 2 +
          target.representative.value + 1 :=
      add_nonneg
        (add_nonneg
          (Fraction.Order.Arithmetic.sq_nonneg_direct
            target.representative.value)
          target.positive.le)
        (by decide)
    calc
      target.representative.value =
          target.representative.value + 0 := by ring1
      _ ≤ target.representative.value +
          (target.representative.value ^ 2 +
            target.representative.value + 1) :=
        (by
          simpa only [zero_add, add_comm] using
            Fraction.Order.Arithmetic.add_le_add_right_direct
              extraNonnegative target.representative.value)
      _ = (target.representative.value + 1) ^ 2 := by ring1
  have lowerLeSuccessor : bracket.lower ≤
      target.representative.value + 1 := by
    apply Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
      (add_nonneg target.positive.le (by decide))
    exact bracket.lower_square_le.trans valueLeSquareSuccessor
  have twiceLowerLe : 2 * bracket.lower ≤
      2 * (target.representative.value + 1) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      lowerLeSuccessor (by decide)
  have sumLe : bracket.upper + bracket.lower ≤
      2 * target.representative.value + 3 := by
    calc
      bracket.upper + bracket.lower =
          2 * bracket.lower + (bracket.upper - bracket.lower) := by ring1
      _ ≤ 2 * (target.representative.value + 1) + 1 :=
        Fraction.Order.Arithmetic.add_le_add_direct twiceLowerLe widthLeOne
      _ = 2 * target.representative.value + 3 := by ring1
  have sumNonnegative : 0 ≤ bracket.upper + bracket.lower :=
    add_nonneg bracket.upper_positive.le bracket.lower_nonnegative
  have reciprocalNonnegative :
      0 ≤ 1 / (refinement : Fraction.Rational) :=
    (Fraction.Order.Field.div_pos_direct (by decide)
      refinementPositive).le
  calc
    bracket.upper ^ 2 - target.representative.value ≤
        bracket.upper ^ 2 - bracket.lower ^ 2 :=
      Fraction.Order.Arithmetic.sub_le_sub_left_direct
        bracket.lower_square_le (bracket.upper ^ 2)
    _ = (bracket.upper - bracket.lower) *
        (bracket.upper + bracket.lower) := by ring1
    _ ≤ (1 / (refinement : Fraction.Rational)) *
        (2 * target.representative.value + 3) :=
      Fraction.Order.Arithmetic.mul_le_mul_direct widthLeRefinement sumLe
        sumNonnegative reciprocalNonnegative
    _ = (2 * target.representative.value + 3) /
        (scale + 1 : Nat) := by
      unfold refinement
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      ring1
end Purelib.Approximation.Rational.SquareRootBracket.KernelApproximation

end
