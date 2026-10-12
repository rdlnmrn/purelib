module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Division
public import Purelib.Approximation.Gaussian.Request.Apart
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Request

open Purelib.Approximation.Gaussian.Request.Basic

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction.Order

/-!
# Apartness-certified Gaussian enclosure requests

The original denominator request retains a positive lower quadrance. The
quotient construction uses both centre bounds, that lower quadrance and the
same operand requests to certify its exact output ball.
-/

namespace Purelib.Approximation.Gaussian.Request.Basic.Name

/-- Common operand request used by division. Its denominator deliberately contains
twice the coefficient actually needed, leaving a strict rational margin in the
final estimate.

The numerator retains the output target times the lower quadrance squared.
Four times the sum of the two original centre bounds plus one is the same
strictly positive budget denominator. -/
@[expose] public def divisionInputTarget (left right : Gaussian.Request.Basic.Name) (lowerSq : Fraction.Rational)
    (target : Fraction.Rational) : Fraction.Rational :=
  (target * (lowerSq * lowerSq)) /
    (4 * (left.centerBound + right.centerBound + 1))

/-- The division budget denominator computed from the two retained centre bounds
is strictly positive.

The two original centre bounds are nonnegative. Adding the fixed unit gives a
strictly positive sum, and multiplication by four preserves that sign. -/
public theorem divisionDenominator_pos (left right : Gaussian.Request.Basic.Name) :
    0 < 4 * (left.centerBound + right.centerBound + 1) := by
  apply Arithmetic.mul_pos_direct (by decide)
  exact Arithmetic.add_pos_of_nonneg_of_pos_direct
    (add_nonneg left.centerBound_nonneg right.centerBound_nonneg) (by decide)

/-- A positive output target and positive denominator lower quadrance give a
positive common division input request.

The output target and denominator lower quadrance are both strictly positive.
Their original product is positive and the retained centre-bound denominator
is positive. -/
public theorem divisionInputTarget_pos (left right : Gaussian.Request.Basic.Name) (lowerSq : Fraction.Rational)
    (lowerPositive : 0 < lowerSq) {target : Fraction.Rational}
    (positive : 0 < target) :
    0 < divisionInputTarget left right lowerSq target := by
  apply Fraction.Order.Field.div_pos_direct
  · exact Arithmetic.mul_pos_direct positive
      (Arithmetic.mul_pos_direct lowerPositive lowerPositive)
  · exact divisionDenominator_pos left right

/-- The common division request leaves a strict margin below the target times the
squared lower quadrance.

Twice the sum of the original centre bounds is strictly below the retained
budget denominator. Multiplication by the same positive operand request gives
the stated margin. -/
public theorem division_budget_lt (left right : Gaussian.Request.Basic.Name) (lowerSq : Fraction.Rational)
    (lowerPositive : 0 < lowerSq) {target : Fraction.Rational}
    (positive : 0 < target) :
    2 * divisionInputTarget left right lowerSq target *
        (left.centerBound + right.centerBound) <
      target * (lowerSq * lowerSq) := by
  let epsilon := divisionInputTarget left right lowerSq target
  let sumBound := left.centerBound + right.centerBound
  let denominator : Fraction.Rational := 4 * (sumBound + 1)
  have epsilonPositive : 0 < epsilon :=
    divisionInputTarget_pos left right lowerSq lowerPositive positive
  have denominatorPositive : 0 < denominator := by
    exact divisionDenominator_pos left right
  have coefficientLt : 2 * sumBound < denominator := by
    dsimp only [denominator, sumBound]
    have sumNonnegative :
        0 ≤ left.centerBound + right.centerBound :=
      add_nonneg left.centerBound_nonneg right.centerBound_nonneg
    apply Arithmetic.lt_of_add_lt_add_right_direct
      (c := -(2 * (left.centerBound + right.centerBound)))
    calc
      2 * (left.centerBound + right.centerBound) +
          -(2 * (left.centerBound + right.centerBound)) = 0 := by ring1
      _ < 2 * (left.centerBound + right.centerBound) + 4 :=
        Arithmetic.add_pos_of_nonneg_of_pos_direct
          (Arithmetic.mul_nonneg_direct (by decide)
            sumNonnegative)
          (by decide)
      _ = 4 * (left.centerBound + right.centerBound + 1) +
          -(2 * (left.centerBound + right.centerBound)) := by ring1
  have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct
    epsilonPositive coefficientLt
  calc
    2 * epsilon * sumBound = epsilon * (2 * sumBound) := by ring1
    _ < epsilon * denominator := scaled
    _ = target * (lowerSq * lowerSq) := by
      dsimp only [epsilon, denominator, sumBound, divisionInputTarget]
      exact Fraction.Field.div_mul_cancel_of_ne _ _
        (divisionDenominator_pos left right).ne'

/-- The certified quotient ball meets the requested squared-error target under the
original operand bounds and matching denominator lower quadrance.

Both operand radii meet the original common request and both centres satisfy
their retained bounds. The positive lower quadrance and its exact ball
certificate bound the original quotient radius. -/
public theorem div_radius_lt (leftName rightName : Gaussian.Request.Basic.Name) (lowerSq : Fraction.Rational)
    (lowerPositive : 0 < lowerSq) (left right : Enclosure.Ball)
    {target : Fraction.Rational} (positive : 0 < target)
    (leftSmall :
      left.radiusSq <
        divisionInputTarget leftName rightName lowerSq target)
    (rightSmall :
      right.radiusSq <
        divisionInputTarget leftName rightName lowerSq target)
    (leftCenter : Data.Gaussian.Norm.Basic.normSq left.center ≤ leftName.centerBound)
    (rightCenter : Data.Gaussian.Norm.Basic.normSq right.center ≤ rightName.centerBound)
    (rightApart :
      Ball.Apart right)
    (sameLower : rightApart.lowerSq = lowerSq) :
    (left.div right rightApart).radiusSq < target := by
  let epsilon :=
    divisionInputTarget leftName rightName lowerSq target
  let centerNorm := Data.Gaussian.Norm.Basic.normSq right.center
  let numerator :=
    2 * (left.radiusSq * centerNorm +
      Data.Gaussian.Norm.Basic.normSq left.center * right.radiusSq)
  let lowerProduct := lowerSq * lowerSq
  have epsilonPositive : 0 < epsilon :=
    divisionInputTarget_pos leftName rightName lowerSq lowerPositive positive
  have rightCenterLower : lowerSq ≤ centerNorm := by
    rw [← sameLower]
    exact rightApart.lower right.contains_center
  have centerPositive : 0 < centerNorm :=
    lowerPositive.trans_le rightCenterLower
  have lowerProductPositive : 0 < lowerProduct :=
    Arithmetic.mul_pos_direct lowerPositive lowerPositive
  have numeratorNonnegative : 0 ≤ numerator := by
    exact Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Arithmetic.mul_nonneg_direct left.radiusSq_nonneg
          (Data.Gaussian.Norm.Basic.normSq_nonneg right.center))
        (Arithmetic.mul_nonneg_direct
          (Data.Gaussian.Norm.Basic.normSq_nonneg left.center) right.radiusSq_nonneg))
  have numeratorUpper : numerator ≤
      2 * epsilon * (leftName.centerBound + rightName.centerBound) := by
    dsimp only [numerator, centerNorm]
    have leftTerm : left.radiusSq * Data.Gaussian.Norm.Basic.normSq right.center ≤
        epsilon * rightName.centerBound :=
      Arithmetic.mul_le_mul_direct leftSmall.le rightCenter
        (Data.Gaussian.Norm.Basic.normSq_nonneg right.center) epsilonPositive.le
    have rightTerm : Data.Gaussian.Norm.Basic.normSq left.center * right.radiusSq ≤
        leftName.centerBound * epsilon :=
      Arithmetic.mul_le_mul_direct leftCenter rightSmall.le
        right.radiusSq_nonneg leftName.centerBound_nonneg
    calc
      2 * (left.radiusSq * Data.Gaussian.Norm.Basic.normSq right.center +
          Data.Gaussian.Norm.Basic.normSq left.center * right.radiusSq) ≤
          2 * (epsilon * rightName.centerBound +
            leftName.centerBound * epsilon) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftTerm rightTerm) (by decide)
      _ = 2 * epsilon *
          (leftName.centerBound + rightName.centerBound) := by ring1
  have numeratorStrict : numerator < target * lowerProduct :=
    numeratorUpper.trans_lt
      (division_budget_lt leftName rightName lowerSq lowerPositive positive)
  have denominatorLower : lowerProduct ≤
      lowerSq * centerNorm :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      rightCenterLower lowerPositive.le
  have denominatorPositive : 0 < lowerSq * centerNorm :=
    Arithmetic.mul_pos_direct lowerPositive centerPositive
  change
    (2 * (left.radiusSq * Data.Gaussian.Norm.Basic.normSq right.center +
      Data.Gaussian.Norm.Basic.normSq left.center * right.radiusSq)) /
      (rightApart.lowerSq * Data.Gaussian.Norm.Basic.normSq right.center) < target
  rw [sameLower]
  calc
    numerator / (lowerSq * centerNorm) ≤
        numerator / lowerProduct :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        numeratorNonnegative lowerProductPositive denominatorLower
    _ < target :=
      (Fraction.Order.Field.div_lt_iff_pos lowerProductPositive).2
        numeratorStrict

/-- Divide two enclosure request oracles using the original denominator apartness
certificate.

Both operands receive a common request computed from their retained centre
bounds, output target and denominator lower quadrance. -/
@[expose] public def div (left right : Gaussian.Request.Basic.Name) (apart : Name.Apart right) :
  Gaussian.Request.Basic.Name where
  request target positive :=
    let inputPositive := divisionInputTarget_pos left right apart.lowerSq
      apart.positive positive
    let leftBall :=
      left.request (divisionInputTarget left right apart.lowerSq target)
        inputPositive
    let rightBall :=
      right.request (divisionInputTarget left right apart.lowerSq target)
        inputPositive
    leftBall.div rightBall
      ((Apart.atRequest apart) (divisionInputTarget left right apart.lowerSq target)
        inputPositive)
  accurate target positive := by
    apply div_radius_lt left right apart.lowerSq apart.positive
    · exact positive
    · exact left.accurate _ _
    · exact right.accurate _ _
    · exact left.center_bounded _ _
    · exact right.center_bounded _ _
    · rfl
  centerBound := left.centerBound / apart.lowerSq
  centerBound_nonneg :=
    Fraction.Order.Field.div_nonneg_direct left.centerBound_nonneg
      apart.positive.le
  center_bounded target positive := by
    let inputPositive := divisionInputTarget_pos left right apart.lowerSq
      apart.positive positive
    let leftBall :=
      left.request (divisionInputTarget left right apart.lowerSq target)
        inputPositive
    let rightBall :=
      right.request (divisionInputTarget left right apart.lowerSq target)
        inputPositive
    let rightApart := (Apart.atRequest apart)
      (divisionInputTarget left right apart.lowerSq target) inputPositive
    have rightCenterLower : apart.lowerSq ≤ Data.Gaussian.Norm.Basic.normSq rightBall.center :=
      (Apart.center_lower apart) _ _
    have rightCenterPositive : 0 < Data.Gaussian.Norm.Basic.normSq rightBall.center :=
      apart.positive.trans_le rightCenterLower
    have rightCenterNonzero : rightBall.center ≠ 0 := by
      intro centerZero
      rw [centerZero, Data.Gaussian.Norm.Basic.normSq_zero] at rightCenterPositive
      exact (lt_irrefl _ rightCenterPositive).elim
    change Data.Gaussian.Norm.Basic.normSq (leftBall.center / rightBall.center) ≤
      left.centerBound / apart.lowerSq
    rw [Data.Gaussian.Field.normSq_div _ _ rightCenterNonzero]
    calc
      Data.Gaussian.Norm.Basic.normSq leftBall.center * (Data.Gaussian.Norm.Basic.normSq
        rightBall.center)⁻¹ =
          Data.Gaussian.Norm.Basic.normSq leftBall.center / Data.Gaussian.Norm.Basic.normSq
            rightBall.center := rfl
      _ ≤ left.centerBound / Data.Gaussian.Norm.Basic.normSq rightBall.center := by
        apply (Fraction.Order.Field.div_le_iff_pos
          rightCenterPositive).2
        calc
          Data.Gaussian.Norm.Basic.normSq leftBall.center ≤ left.centerBound :=
            left.center_bounded _ _
          _ = (left.centerBound / Data.Gaussian.Norm.Basic.normSq rightBall.center) *
              Data.Gaussian.Norm.Basic.normSq rightBall.center :=
            (Fraction.Field.div_mul_cancel_of_ne
              left.centerBound _ rightCenterPositive.ne').symm
      _ ≤ left.centerBound / apart.lowerSq :=
        Fraction.Order.Field.div_le_div_of_nonneg_left_direct
          left.centerBound_nonneg apart.positive rightCenterLower

/-- The division request admits quotients of readings admitted by its original two
operand requests and retained denominator apartness certificate.

The two readings remain in the original common-target operand balls. The
retained uniform denominator apartness certifies their quotient in the same
requested quotient ball. -/
public theorem request_contains_div (left right : Gaussian.Request.Basic.Name) (apart : Name.Apart right)
    {target : Fraction.Rational} (positive : 0 < target) {x y : Data.Gaussian.Basic.Canonical}
    (xInside : (left.request
      (divisionInputTarget left right apart.lowerSq target)
      (divisionInputTarget_pos left right apart.lowerSq apart.positive
        positive)).Contains x)
    (yInside : (right.request
      (divisionInputTarget left right apart.lowerSq target)
      (divisionInputTarget_pos left right apart.lowerSq apart.positive
        positive)).Contains y) :
    (left.div right apart).request target positive |>.Contains (x / y) :=
  Enclosure.Ball.contains_div
    ((Apart.atRequest apart) _ _) xInside yInside

end Purelib.Approximation.Gaussian.Request.Basic.Name
