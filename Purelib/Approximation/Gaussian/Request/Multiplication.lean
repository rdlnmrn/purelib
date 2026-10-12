module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Mul
public import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Request.Basic (Name)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Request.Basic

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction.Order

/-!
# Multiplication of Gaussian enclosure requests

Both retained centre bounds determine one common operand request. The exact
product ball, its radius bound and its admitted readings use those same
original operand requests.
-/

namespace Purelib.Approximation.Gaussian.Request.Basic.Name

/-- A strictly positive coefficient bounding the multiplication error after both
operand radii have been replaced by a common number below one.

The coefficient is four times the sum of the two retained centre bounds, plus
two. Those bounds and the fixed positive margin determine the original error
coefficient. -/
@[expose] public def multiplicativeCoefficient (left right : Name) : Fraction.Rational :=
  4 * (left.centerBound + right.centerBound) + 2

/-- The multiplication error coefficient is strictly positive for the original two
request oracles.

Each retained centre bound is nonnegative. Four times their sum is therefore
nonnegative, and the fixed positive summand gives the strict bound. -/
public theorem multiplicativeCoefficient_pos (left right : Name) :
    0 < multiplicativeCoefficient left right := by
  unfold multiplicativeCoefficient
  have nonnegative : 0 ≤ 4 * (left.centerBound + right.centerBound) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  exact lt_of_lt_of_le (by decide : (0 : Fraction.Rational) < 2)
    (le_add_of_nonneg_left nonnegative)

/-- Operand squared-error request used for multiplication. The extra `target` in
the denominator makes this number strictly below one without a minimum
operation.

Dividing the target by its sum with the positive multiplication coefficient
yields the original operand request. The positive coefficient makes that
request strictly below one for a positive target. -/
@[expose] public def multiplicativeInputTarget (left right : Name)
    (target : Fraction.Rational) : Fraction.Rational :=
  target / (target + multiplicativeCoefficient left right)

/-- A positive output target gives a strictly positive common multiplication input
request.

The requested output bound is positive and the coefficient retains a strictly
positive margin. Their sum is a positive denominator for the same computed
input request. -/
public theorem multiplicativeInputTarget_pos (left right : Name)
    {target : Fraction.Rational} (positive : 0 < target) :
    0 < multiplicativeInputTarget left right target := by
  apply Fraction.Order.Field.div_pos_direct positive
  exact Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (Arithmetic.le_of_lt_direct
        (multiplicativeCoefficient_pos left right))

/-- The common multiplication input request is strictly below one for a positive
output target.

The denominator is the positive target plus a strictly positive coefficient.
Comparing the numerator with that same denominator establishes the strict
bound by one. -/
public theorem multiplicativeInputTarget_lt_one (left right : Name)
    {target : Fraction.Rational} (positive : 0 < target) :
    multiplicativeInputTarget left right target < 1 := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (Arithmetic.le_of_lt_direct
        (multiplicativeCoefficient_pos left right)))).2
  calc
    target < target + multiplicativeCoefficient left right :=
      by
        have shifted := Arithmetic.add_lt_add_left_direct
          (multiplicativeCoefficient_pos left right) target
        rewrite [_root_.add_zero] at shifted
        exact shifted
    _ = 1 * (target + multiplicativeCoefficient left right) := by ring1

/-- The common multiplication request times its error coefficient is strictly
below the positive output target.

The denominator contains the positive target in addition to the original
coefficient. Scaling the request by that coefficient therefore leaves a strict
margin below the same output target. -/
public theorem multiplicative_budget_lt (left right : Name)
    {target : Fraction.Rational} (positive : 0 < target) :
    multiplicativeInputTarget left right target *
        multiplicativeCoefficient left right < target := by
  let coefficient := multiplicativeCoefficient left right
  have coefficientPositive : 0 < coefficient :=
    multiplicativeCoefficient_pos left right
  have denominatorPositive : 0 < target + coefficient :=
    Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (Arithmetic.le_of_lt_direct coefficientPositive)
  change target / (target + coefficient) * coefficient < target
  calc
    target / (target + coefficient) * coefficient =
        (target * coefficient) / (target + coefficient) := by
      exact Fraction.Field.quotient_mul_reorder _ _ _
    _ < target := by
      apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
      have coefficientLt : coefficient < target + coefficient := by
        calc
          coefficient = 0 + coefficient := (_root_.zero_add coefficient).symm
          _ < target + coefficient :=
            Arithmetic.add_lt_add_right_direct positive
              coefficient
      have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct
        positive coefficientLt
      exact scaled

/-- Bound the product-radius polynomial using a common input radius below one.

Both radius allowances are nonnegative and strictly below the same positive
input bound. The two centre quadrances are bounded by their nonnegative
magnitude bounds, so the original linear and product terms fit the displayed
multiplication coefficient. -/
private theorem mul_radius_bound
    {leftRadius rightRadius leftNorm rightNorm leftBound rightBound epsilon : Fraction.Rational}
    (leftRadiusNonnegative : 0 ≤ leftRadius)
    (rightRadiusNonnegative : 0 ≤ rightRadius)
    (leftBoundNonnegative : 0 ≤ leftBound)
    (rightBoundNonnegative : 0 ≤ rightBound)
    (leftSmall : leftRadius < epsilon)
    (rightSmall : rightRadius < epsilon)
    (leftCenter : leftNorm ≤ leftBound)
    (rightCenter : rightNorm ≤ rightBound)
    (epsilonPositive : 0 < epsilon)
    (epsilonLtOne : epsilon < 1) :
    4 * (leftRadius * rightNorm + leftNorm * rightRadius) +
        2 * (leftRadius * rightRadius) <
      epsilon * (4 * (leftBound + rightBound) + 2) := by
  have firstLeft : leftRadius * rightNorm ≤ epsilon * rightBound := by
    calc
      leftRadius * rightNorm ≤ leftRadius * rightBound :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct rightCenter leftRadiusNonnegative
      _ ≤ epsilon * rightBound :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Arithmetic.le_of_lt_direct leftSmall) rightBoundNonnegative
  have firstRight : leftNorm * rightRadius ≤ leftBound * epsilon := by
    calc
      leftNorm * rightRadius ≤ leftBound * rightRadius :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct leftCenter rightRadiusNonnegative
      _ ≤ leftBound * epsilon :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.le_of_lt_direct rightSmall) leftBoundNonnegative
  have firstOrder : leftRadius * rightNorm + leftNorm * rightRadius ≤
      epsilon * (rightBound + leftBound) := by
    calc
      leftRadius * rightNorm + leftNorm * rightRadius ≤
          epsilon * rightBound + leftBound * epsilon :=
        Arithmetic.add_le_add_direct firstLeft firstRight
      _ = epsilon * (rightBound + leftBound) := by ring1
  have productError : leftRadius * rightRadius < epsilon * epsilon := by
    calc
      leftRadius * rightRadius ≤ leftRadius * epsilon :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.le_of_lt_direct rightSmall) leftRadiusNonnegative
      _ < epsilon * epsilon :=
        Arithmetic.mul_lt_mul_of_pos_right_direct leftSmall epsilonPositive
  have linearScaled :
      4 * (leftRadius * rightNorm + leftNorm * rightRadius) ≤
        4 * (epsilon * (rightBound + leftBound)) :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct firstOrder
      (by decide : (0 : Fraction.Rational) ≤ 4)
  have productScaled : 2 * (leftRadius * rightRadius) < 2 * (epsilon * epsilon) :=
    Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide : (0 : Fraction.Rational) < 2) productError
  have epsilonSquare : epsilon * epsilon < epsilon * 1 :=
    Arithmetic.mul_lt_mul_of_pos_left_direct epsilonPositive epsilonLtOne
  have twiceEpsilonSquare : 2 * (epsilon * epsilon) < 2 * (epsilon * 1) :=
    Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide : (0 : Fraction.Rational) < 2) epsilonSquare
  calc
    4 * (leftRadius * rightNorm + leftNorm * rightRadius) +
        2 * (leftRadius * rightRadius) ≤
      4 * (epsilon * (rightBound + leftBound)) + 2 * (leftRadius * rightRadius) :=
        Arithmetic.add_le_add_right_direct linearScaled _
    _ < 4 * (epsilon * (rightBound + leftBound)) + 2 * (epsilon * epsilon) :=
      Arithmetic.add_lt_add_left_direct productScaled _
    _ < 4 * (epsilon * (rightBound + leftBound)) + 2 * (epsilon * 1) :=
      Arithmetic.add_lt_add_left_direct twiceEpsilonSquare _
    _ = epsilon * (4 * (leftBound + rightBound) + 2) := by ring1

/-- The product ball meets the output target when both operand radii meet their
common request and both centres meet their original bounds.

The two original ball radii satisfy the same common request, and their centres
satisfy the retained magnitude bounds. Direct scalar multiplication and
addition bound the original product-radius formula below the positive output
target. -/
public theorem mul_radius_lt (leftName rightName : Name) (left right : Enclosure.Ball)
    {target : Fraction.Rational} (positive : 0 < target)
    (leftSmall :
      left.radiusSq < multiplicativeInputTarget leftName rightName target)
    (rightSmall :
      right.radiusSq < multiplicativeInputTarget leftName rightName target)
    (leftCenter : Data.Gaussian.Norm.Basic.normSq left.center ≤ leftName.centerBound)
    (rightCenter : Data.Gaussian.Norm.Basic.normSq right.center ≤ rightName.centerBound) :
    (left.mul right).radiusSq < target := by
  let epsilon : Fraction.Rational := multiplicativeInputTarget leftName rightName target
  let leftRadius : Fraction.Rational := left.radiusSq
  let rightRadius : Fraction.Rational := right.radiusSq
  let leftNorm : Fraction.Rational := Data.Gaussian.Norm.Basic.normSq left.center
  let rightNorm : Fraction.Rational := Data.Gaussian.Norm.Basic.normSq right.center
  let leftBound : Fraction.Rational := leftName.centerBound
  let rightBound : Fraction.Rational := rightName.centerBound
  have bound :
      4 * (leftRadius * rightNorm + leftNorm * rightRadius) +
          2 * (leftRadius * rightRadius) <
        epsilon * (4 * (leftBound + rightBound) + 2) :=
    mul_radius_bound left.radiusSq_nonneg right.radiusSq_nonneg
      leftName.centerBound_nonneg rightName.centerBound_nonneg
      leftSmall rightSmall leftCenter rightCenter
      (multiplicativeInputTarget_pos leftName rightName positive)
      (multiplicativeInputTarget_lt_one leftName rightName positive)
  change 4 * (leftRadius * rightNorm + leftNorm * rightRadius) +
    2 * (leftRadius * rightRadius) < target
  exact bound.trans (multiplicative_budget_lt leftName rightName positive)

/-- Multiply two rational enclosure request oracles.

Each operand receives the common target computed from both retained centre
bounds; the output centre bound is their product. -/
@[expose] public def mul (left right : Name) : Name where
  request target positive :=
    let inputPositive := multiplicativeInputTarget_pos left right positive
    (left.request (multiplicativeInputTarget left right target) inputPositive).mul
      (right.request (multiplicativeInputTarget left right target) inputPositive)
  accurate target positive := by
    apply mul_radius_lt left right
    · exact positive
    · exact left.accurate _ _
    · exact right.accurate _ _
    · exact left.center_bounded _ _
    · exact right.center_bounded _ _
  centerBound := left.centerBound * right.centerBound
  centerBound_nonneg :=
    Arithmetic.mul_nonneg_direct left.centerBound_nonneg
      right.centerBound_nonneg
  center_bounded target positive := by
    change Data.Gaussian.Norm.Basic.normSq
      ((left.request (multiplicativeInputTarget left right target) _).center *
        (right.request (multiplicativeInputTarget left right target) _).center) ≤
      left.centerBound * right.centerBound
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      (left.center_bounded _ _) (right.center_bounded _ _)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) left.centerBound_nonneg

/-- The product request admits products of readings admitted by the two original
common-target operand requests.

Both readings belong to the original operand balls requested at the same
retained input target. Their product belongs to the original product ball,
without altering either request or reading. -/
public theorem request_contains_mul (left right : Name) {target : Fraction.Rational}
    (positive : 0 < target) {x y : Data.Gaussian.Basic.Canonical}
    (xInside : (left.request (multiplicativeInputTarget left right target)
      (multiplicativeInputTarget_pos left right positive)).Contains x)
    (yInside : (right.request (multiplicativeInputTarget left right target)
      (multiplicativeInputTarget_pos left right positive)).Contains y) :
    (left.mul right).request target positive |>.Contains (x * y) :=
  Enclosure.Ball.contains_mul xInside yInside

end Purelib.Approximation.Gaussian.Request.Basic.Name

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent

/-- The process multiplication request is strictly smaller than its positive outer
request.

The same retained coefficient is at least one, so multiplying the positive
input request by it bounds the request itself. Its strict product-budget bound
gives the original outer target comparison. -/
public theorem processMultiplicativeInputTarget_lt_target
    (leftName rightName : Name)
    {target : Fraction.Rational} (positive : 0 < target) :
    Name.multiplicativeInputTarget
        leftName rightName target < target := by
  let epsilon :=
    Name.multiplicativeInputTarget
      leftName rightName target
  have epsilonPositive : 0 < epsilon :=
    Name.multiplicativeInputTarget_pos
      leftName rightName positive
  have boundPartNonnegative :
      0 ≤ 4 * (leftName.centerBound + rightName.centerBound) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg leftName.centerBound_nonneg rightName.centerBound_nonneg)
  have coefficientOne :
      1 ≤ Name.multiplicativeCoefficient
        leftName rightName := by
    unfold Name.multiplicativeCoefficient
    exact (show (1 : Fraction.Rational) ≤ 2 by decide).trans
      (le_add_of_nonneg_left boundPartNonnegative)
  calc
    epsilon = epsilon * 1 :=
      (Fraction.Field.mul_one_direct _).symm
    _ ≤ epsilon *
        Name.multiplicativeCoefficient
          leftName rightName :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        coefficientOne epsilonPositive.le
    _ < target :=
      Name.multiplicative_budget_lt
        leftName rightName positive

end Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent
