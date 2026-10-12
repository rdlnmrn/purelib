module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Process.Division
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Division
import Purelib.Approximation.Rational.Budget.Product
public import Purelib.Approximation.Rational.Budget.Quotient.Semantic
import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Coherence of apartness-certified Gaussian process division

The original paired states, denominator apartness and semantic budgets retain
both operand coherence witnesses. Their exact ball radii and allowances give
the same quantitative refinement request for the quotient process.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Approximation.Rational.Request
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The quotient coherence allowance combines its displayed ball radius with the
semantic allowance for the two retained operand states.

The exact quotient ball radius is added to the semantic budget from both
original state allowances. The original paired state and apartness certificate
supply those same retained observations. -/
@[expose] public def divisionAllowance {left right : Process}
    (leftCoherent : Coherent left) (rightCoherent : Coherent right)
    (apart : Process.Apart right)
    (state : (left.div right apart).State) : Fraction.Rational :=
  ((left.div right apart).ball state).radiusSq +
    divisionSemanticAllowance left.centerBound right.centerBound apart.lowerSq
      (leftCoherent.allowance state.1) (rightCoherent.allowance state.2)

/-- Quotients of possible operand readings at two states differ in squared norm by
at most four times the sum of their quotient allowances.

Both operands retain coherence certificates, and the denominator retains a
uniform strictly positive lower squared norm. -/
public theorem division_possible_close
    {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right)
    (apart : Process.Apart right)
    {leftState rightState : (left.div right apart).State}
    {leftX leftY rightX rightY : Data.Gaussian.Basic.Canonical}
    (leftXPossible : left.Possible leftState.1 leftX)
    (leftYPossible : right.Possible leftState.2 leftY)
    (rightXPossible : left.Possible rightState.1 rightX)
    (rightYPossible : right.Possible rightState.2 rightY) :
    Data.Gaussian.Norm.Basic.normSq (leftX / leftY - rightX / rightY) ≤
      4 *
        (divisionAllowance leftCoherent rightCoherent apart leftState +
          divisionAllowance leftCoherent rightCoherent apart rightState) := by
  let leftOne := leftCoherent.allowance leftState.1
  let leftTwo := leftCoherent.allowance rightState.1
  let rightOne := rightCoherent.allowance leftState.2
  let rightTwo := rightCoherent.allowance rightState.2
  let marginalOne := divisionMarginal left.centerBound right.centerBound
    leftOne rightOne
  let marginalTwo := divisionMarginal left.centerBound right.centerBound
    leftTwo rightTwo
  have leftDenominatorLower : apart.lowerSq ≤ Data.Gaussian.Norm.Basic.normSq leftY :=
    apart.lower leftState.2 (right.possible_inside leftYPossible)
  have rightDenominatorLower : apart.lowerSq ≤ Data.Gaussian.Norm.Basic.normSq rightY :=
    apart.lower rightState.2 (right.possible_inside rightYPossible)
  have leftDenominatorPositive : 0 < Data.Gaussian.Norm.Basic.normSq leftY :=
    apart.positive.trans_le leftDenominatorLower
  have rightDenominatorPositive : 0 < Data.Gaussian.Norm.Basic.normSq rightY :=
    apart.positive.trans_le rightDenominatorLower
  have leftDenominatorNonzero : leftY ≠ 0 := by
    intro equal
    rw [equal, Data.Gaussian.Norm.Basic.normSq_zero] at leftDenominatorPositive
    exact (lt_irrefl _ leftDenominatorPositive).elim
  have rightDenominatorNonzero : rightY ≠ 0 := by
    intro equal
    rw [equal, Data.Gaussian.Norm.Basic.normSq_zero] at rightDenominatorPositive
    exact (lt_irrefl _ rightDenominatorPositive).elim
  have leftClose : Data.Gaussian.Norm.Basic.normSq (leftX - rightX) ≤
      4 * (leftOne + leftTwo) :=
    leftCoherent.possible_close leftXPossible rightXPossible
  have rightClose : Data.Gaussian.Norm.Basic.normSq (rightY - leftY) ≤
      4 * (rightTwo + rightOne) :=
    rightCoherent.possible_close rightYPossible leftYPossible
  have rightTwoNorm : Data.Gaussian.Norm.Basic.normSq rightY ≤
      2 * (rightTwo + right.centerBound) :=
    possible_normSq_le rightCoherent rightYPossible
  have leftTwoNorm : Data.Gaussian.Norm.Basic.normSq rightX ≤
      2 * (leftTwo + left.centerBound) :=
    possible_normSq_le leftCoherent rightXPossible
  have firstTerm :
      Data.Gaussian.Norm.Basic.normSq ((leftX - rightX) * rightY) ≤
        (4 * (leftOne + leftTwo)) *
          (2 * (rightTwo + right.centerBound)) := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      leftClose rightTwoNorm (Data.Gaussian.Norm.Basic.normSq_nonneg rightY)
      (Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (leftCoherent.allowance_nonneg leftState.1)
          (leftCoherent.allowance_nonneg rightState.1)))
  have secondTerm :
      Data.Gaussian.Norm.Basic.normSq (rightX * (rightY - leftY)) ≤
        (2 * (leftTwo + left.centerBound)) *
          (4 * (rightTwo + rightOne)) := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      leftTwoNorm rightClose (Data.Gaussian.Norm.Basic.normSq_nonneg (rightY - leftY))
      (Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (leftCoherent.allowance_nonneg rightState.1)
          left.centerBound_nonneg))
  have numeratorIdentity :
      leftX * rightY - rightX * leftY =
        (leftX - rightX) * rightY + rightX * (rightY - leftY) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1
  have crossBound := product_cross_bound
    left.centerBound right.centerBound leftOne leftTwo rightTwo rightOne
    (leftCoherent.allowance_nonneg leftState.1)
    (rightCoherent.allowance_nonneg leftState.2)
  have crossProductBound :
      Data.Gaussian.Norm.Basic.normSq (leftX * rightY - rightX * leftY) ≤
        4 *
          (productAllowance left.centerBound right.centerBound
              leftOne rightTwo +
            productAllowance left.centerBound right.centerBound
              leftTwo rightOne) := by
    rw [numeratorIdentity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((leftX - rightX) * rightY + rightX * (rightY - leftY)) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq ((leftX - rightX) * rightY) +
          Data.Gaussian.Norm.Basic.normSq (rightX * (rightY - leftY))) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          ((4 * (leftOne + leftTwo)) *
              (2 * (rightTwo + right.centerBound)) +
            (2 * (leftTwo + left.centerBound)) *
              (4 * (rightTwo + rightOne))) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = 16 *
          ((leftOne + leftTwo) * (rightTwo + right.centerBound) +
            (leftTwo + left.centerBound) * (rightTwo + rightOne)) := by
        ring1
      _ ≤ 16 *
          (productBase left.centerBound right.centerBound leftOne rightTwo +
            productBase left.centerBound right.centerBound leftTwo rightOne) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          crossBound (by decide)
      _ = 4 *
          (productAllowance left.centerBound right.centerBound leftOne rightTwo +
            productAllowance left.centerBound right.centerBound leftTwo rightOne) := by
        unfold productAllowance
        ring1
  have crossMarginalBound :
      productAllowance left.centerBound right.centerBound leftOne rightTwo +
          productAllowance left.centerBound right.centerBound leftTwo rightOne ≤
        marginalOne + marginalTwo := by
    calc
      productAllowance left.centerBound right.centerBound leftOne rightTwo +
          productAllowance left.centerBound right.centerBound leftTwo rightOne ≤
        divisionMarginal left.centerBound right.centerBound leftOne rightTwo +
          divisionMarginal left.centerBound right.centerBound leftTwo rightOne :=
        add_le_add
          (productAllowance_le_divisionMarginal
            (leftCoherent.allowance_nonneg leftState.1)
            (rightCoherent.allowance_nonneg rightState.2))
          (productAllowance_le_divisionMarginal
            (leftCoherent.allowance_nonneg rightState.1)
            (rightCoherent.allowance_nonneg leftState.2))
      _ = marginalOne + marginalTwo := by
        dsimp only [marginalOne, marginalTwo, leftOne, leftTwo,
          rightOne, rightTwo]
        unfold divisionMarginal
        ring1
  have numeratorBound :
      Data.Gaussian.Norm.Basic.normSq (leftX * rightY - rightX * leftY) ≤
        4 * (marginalOne + marginalTwo) :=
    crossProductBound.trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        crossMarginalBound (by decide))
  have denominatorLower : apart.lowerSq * apart.lowerSq ≤
      Data.Gaussian.Norm.Basic.normSq leftY * Data.Gaussian.Norm.Basic.normSq rightY :=
    Arithmetic.mul_le_mul_direct
      leftDenominatorLower rightDenominatorLower apart.positive.le
      (Data.Gaussian.Norm.Basic.normSq_nonneg leftY)
  have lowerProductPositive : 0 < apart.lowerSq * apart.lowerSq :=
    Arithmetic.mul_pos_direct apart.positive apart.positive
  have numeratorNonnegative :
      0 ≤ Data.Gaussian.Norm.Basic.normSq (leftX * rightY - rightX * leftY) :=
    Data.Gaussian.Norm.Basic.normSq_nonneg _
  have marginalOneNonnegative : 0 ≤ marginalOne :=
    divisionMarginal_nonneg left.centerBound_nonneg right.centerBound_nonneg
      (leftCoherent.allowance_nonneg leftState.1)
      (rightCoherent.allowance_nonneg leftState.2)
  have marginalTwoNonnegative : 0 ≤ marginalTwo :=
    divisionMarginal_nonneg left.centerBound_nonneg right.centerBound_nonneg
      (leftCoherent.allowance_nonneg rightState.1)
      (rightCoherent.allowance_nonneg rightState.2)
  rw [Purelib.Data.Gaussian.Field.div_sub_div _ _ _ _
      leftDenominatorNonzero rightDenominatorNonzero,
    Data.Gaussian.Field.normSq_div _ _
      (Data.Gaussian.Field.mul_ne_zero_direct
        leftDenominatorNonzero rightDenominatorNonzero), Data.Gaussian.Norm.Basic.normSq_mul]
  calc
    Data.Gaussian.Norm.Basic.normSq (leftX * rightY - rightX * leftY) /
          (Data.Gaussian.Norm.Basic.normSq leftY * Data.Gaussian.Norm.Basic.normSq rightY) ≤
        Data.Gaussian.Norm.Basic.normSq (leftX * rightY - rightX * leftY) /
          (apart.lowerSq * apart.lowerSq) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        numeratorNonnegative lowerProductPositive denominatorLower
    _ ≤ (4 * (marginalOne + marginalTwo)) /
          (apart.lowerSq * apart.lowerSq) := by
      change Data.Gaussian.Norm.Basic.normSq (leftX * rightY - rightX * leftY) *
          (apart.lowerSq * apart.lowerSq)⁻¹ ≤
        (4 * (marginalOne + marginalTwo)) *
          (apart.lowerSq * apart.lowerSq)⁻¹
      exact Arithmetic.mul_le_mul_of_nonneg_right_direct
        numeratorBound
        (Fraction.Order.Field.inv_pos_direct lowerProductPositive).le
    _ = divisionSemanticAllowance left.centerBound right.centerBound
          apart.lowerSq leftOne rightOne +
        divisionSemanticAllowance left.centerBound right.centerBound
          apart.lowerSq leftTwo rightTwo := by
      unfold divisionSemanticAllowance
      change (4 * (marginalOne + marginalTwo)) *
          (apart.lowerSq * apart.lowerSq)⁻¹ =
        (4 * marginalOne) * (apart.lowerSq * apart.lowerSq)⁻¹ +
          (4 * marginalTwo) * (apart.lowerSq * apart.lowerSq)⁻¹
      rw [mul_add, add_mul]
    _ ≤ divisionAllowance leftCoherent rightCoherent apart leftState +
          divisionAllowance leftCoherent rightCoherent apart rightState := by
      unfold divisionAllowance
      exact add_le_add
        (le_add_of_nonneg_left
          ((left.div right apart).ball leftState).radiusSq_nonneg)
        (le_add_of_nonneg_left
          ((left.div right apart).ball rightState).radiusSq_nonneg)
    _ ≤ 4 *
        (divisionAllowance leftCoherent rightCoherent apart leftState +
          divisionAllowance leftCoherent rightCoherent apart rightState) := by
      let total := divisionAllowance leftCoherent rightCoherent apart leftState +
        divisionAllowance leftCoherent rightCoherent apart rightState
      have totalNonnegative : 0 ≤ total := by
        unfold total divisionAllowance
        exact add_nonneg
          (add_nonneg
            ((left.div right apart).ball leftState).radiusSq_nonneg
            (divisionSemanticAllowance_nonneg left.centerBound_nonneg
              right.centerBound_nonneg apart.positive.le
              (leftCoherent.allowance_nonneg leftState.1)
              (rightCoherent.allowance_nonneg leftState.2)))
          (add_nonneg
            ((left.div right apart).ball rightState).radiusSq_nonneg
            (divisionSemanticAllowance_nonneg left.centerBound_nonneg
              right.centerBound_nonneg apart.positive.le
              (leftCoherent.allowance_nonneg rightState.1)
              (rightCoherent.allowance_nonneg rightState.2)))
      change total ≤ 4 * total
      calc
        total = 1 * total := (_root_.one_mul total).symm
        _ ≤ 4 * total :=
          Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide) totalNonnegative

/-- The semantic quotient allowance is below one quarter of the positive target
when both operand allowances satisfy the retained product request.

Both original allowances meet the retained semantic product request. The
product-to-marginal comparison and the same positive squared lower quadrance
give the strict quarter-target bound. -/
public theorem divisionSemanticAllowance_lt_quarter
    {left right : Process}
    (apart : Process.Apart right)
    {leftAllowance rightAllowance target : Fraction.Rational}
    (targetPositive : 0 < target)
    (leftSmall : leftAllowance <
      productInputTarget left right
        (divisionSemanticTarget apart.lowerSq target))
    (rightSmall : rightAllowance <
      productInputTarget left right
        (divisionSemanticTarget apart.lowerSq target))
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    divisionSemanticAllowance left.centerBound right.centerBound
        apart.lowerSq leftAllowance rightAllowance < target / 4 := by
  have semanticTargetPositive :
      0 < divisionSemanticTarget apart.lowerSq target :=
    divisionSemanticTarget_pos apart.positive targetPositive
  have productSmall := mul_allowances_lt_target
    leftNonnegative rightNonnegative semanticTargetPositive leftSmall rightSmall
  have marginalLe := divisionMarginal_le_two_productAllowance
    left.centerBound_nonneg right.centerBound_nonneg
    leftNonnegative rightNonnegative
  have fourMarginalLe :
      4 * divisionMarginal left.centerBound right.centerBound
          leftAllowance rightAllowance ≤
        8 * productAllowance left.centerBound right.centerBound
          leftAllowance rightAllowance := by
    calc
      4 * divisionMarginal left.centerBound right.centerBound
          leftAllowance rightAllowance ≤
        4 * (2 * productAllowance left.centerBound right.centerBound
          leftAllowance rightAllowance) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          marginalLe (by decide)
      _ = 8 * productAllowance left.centerBound right.centerBound
          leftAllowance rightAllowance := by ring1
  have numeratorSmall :
      4 * divisionMarginal left.centerBound right.centerBound
          leftAllowance rightAllowance <
        8 * divisionSemanticTarget apart.lowerSq target :=
    fourMarginalLe.trans_lt
      (Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide) productSmall)
  unfold divisionSemanticAllowance
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Arithmetic.mul_pos_direct
      apart.positive apart.positive)).2
  calc
    4 * divisionMarginal left.centerBound right.centerBound
        leftAllowance rightAllowance <
      8 * divisionSemanticTarget apart.lowerSq target := numeratorSmall
    _ = (target / 4) * (apart.lowerSq * apart.lowerSq) := by
      unfold divisionSemanticTarget
      rw [← Fraction.Field.mul_assoc,
        Purelib.Data.Rat.Bounds.Quarter.eight_div_thirtyTwo]

/-- The outer quotient request bound obtained by scaling an operand request by the
center-bound denominator and inverse squared apartness bound.

The operand request is scaled by the exact retained centre-bound denominator
and divided by the lower quadrance squared. This original rational expression
reverses the inner division request bound. -/
@[expose] public def divisionOuterTarget (left right : Process) (lowerSq operandRequest :
    Fraction.Rational) : Fraction.Rational :=
  (operandRequest *
      (4 * (left.centerBound + right.centerBound + 1))) /
    (lowerSq * lowerSq)

/-- The outer quotient request bound is positive when its operand request and
lower squared-norm bound are positive.

The operand request and lower quadrance are positive, and the original two
centre bounds are nonnegative. Both the retained scaled numerator and squared
denominator are positive. -/
public theorem divisionOuterTarget_pos (left right : Process)
    {lowerSq operandRequest : Fraction.Rational}
    (lowerPositive : 0 < lowerSq) (requestPositive : 0 < operandRequest) :
    0 < divisionOuterTarget left right lowerSq operandRequest := by
  apply Fraction.Order.Field.div_pos_direct
  · exact Arithmetic.mul_pos_direct requestPositive
      (Name.divisionDenominator_pos
        (Name.centerOnly 0
          left.centerBound left.centerBound_nonneg (by
            rw [Data.Gaussian.Norm.Basic.normSq_zero]
            exact left.centerBound_nonneg))
        (Name.centerOnly 0
          right.centerBound right.centerBound_nonneg (by
            rw [Data.Gaussian.Norm.Basic.normSq_zero]
            exact right.centerBound_nonneg)))
  · exact Arithmetic.mul_pos_direct
      lowerPositive lowerPositive

/-- A quotient request below the outer bound induces an operand request below the
displayed allowance request.

The two request names retain exactly the original operand center bounds. -/
public theorem processDivisionInputTarget_lt
    {left right : Process}
    (leftName rightName : Gaussian.Request.Basic.Name)
    (leftBound : leftName.centerBound = left.centerBound)
    (rightBound : rightName.centerBound = right.centerBound)
    {lowerSq operandRequest request : Fraction.Rational}
    (lowerPositive : 0 < lowerSq)
    (requestSmall :
      request < divisionOuterTarget left right lowerSq operandRequest) :
    Purelib.Approximation.Gaussian.Request.Basic.Name.divisionInputTarget
        leftName rightName lowerSq request < operandRequest := by
  let denominator := 4 * (left.centerBound + right.centerBound + 1)
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator]
    rw [← leftBound, ← rightBound]
    exact Name.divisionDenominator_pos
      leftName rightName
  have lowerProductPositive : 0 < lowerSq * lowerSq :=
    Arithmetic.mul_pos_direct lowerPositive lowerPositive
  unfold Name.divisionInputTarget
  rw [leftBound, rightBound]
  apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
  have scaled := Arithmetic.mul_lt_mul_of_pos_right_direct
    requestSmall lowerProductPositive
  unfold divisionOuterTarget at scaled
  have outerCancelled :
      (operandRequest * (4 * (left.centerBound + right.centerBound + 1)) /
          (lowerSq * lowerSq)) * (lowerSq * lowerSq) =
        operandRequest * (4 * (left.centerBound + right.centerBound + 1)) :=
    Fraction.Field.div_mul_cancel_of_ne _ _
      lowerProductPositive.ne'
  rw [outerCancelled] at scaled
  simpa only [denominator] using scaled

/-- Finite process coherence is preserved by division once the denominator process
carries a uniform finite apartness certificate. The request schedule first
makes both operand allowances small enough for the semantic quotient estimate,
then makes the ordinary enclosure radius small enough for the remaining half
of the requested budget.

Both original operand states and the denominator apartness certificate remain
in the quotient construction. The retained ball radius and semantic allowance
determine the same outer request and refinement certificates. -/
@[expose] public def div {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right)
    (apart : Process.Apart right) :
    Coherent (left.div right apart) where
  allowance := divisionAllowance leftCoherent rightCoherent apart
  allowance_nonneg state :=
    add_nonneg ((left.div right apart).ball state).radiusSq_nonneg
      (divisionSemanticAllowance_nonneg left.centerBound_nonneg
        right.centerBound_nonneg apart.positive.le
        (leftCoherent.allowance_nonneg state.1)
        (rightCoherent.allowance_nonneg state.2))
  ball_radius_le state :=
    le_add_of_nonneg_right
      (divisionSemanticAllowance_nonneg left.centerBound_nonneg
        right.centerBound_nonneg apart.positive.le
        (leftCoherent.allowance_nonneg state.1)
        (rightCoherent.allowance_nonneg state.2))
  possible_close := by
    rintro leftState rightState leftValue rightValue
      ⟨leftX, leftY, leftXPossible, leftYPossible, rfl⟩
      ⟨rightX, rightY, rightXPossible, rightYPossible, rfl⟩
    exact division_possible_close leftCoherent rightCoherent apart
      leftXPossible leftYPossible rightXPossible rightYPossible
  accuracyRequest target :=
    let semanticTarget := divisionSemanticTarget apart.lowerSq target
    let operandTarget := productInputTarget left right semanticTarget
    let leftRequest := leftCoherent.accuracyRequest operandTarget
    let rightRequest := rightCoherent.accuracyRequest operandTarget
    let sharedRequest := commonRequest leftRequest rightRequest
    Common.commonTarget (target / 2)
      (divisionOuterTarget left right apart.lowerSq sharedRequest)
  accuracyRequest_pos := by
    intro target positive
    let semanticTarget := divisionSemanticTarget apart.lowerSq target
    have semanticPositive : 0 < semanticTarget :=
      divisionSemanticTarget_pos apart.positive positive
    let operandTarget := productInputTarget left right semanticTarget
    have operandPositive : 0 < operandTarget :=
      productInputTarget_pos left right semanticPositive
    let leftRequest := leftCoherent.accuracyRequest operandTarget
    let rightRequest := rightCoherent.accuracyRequest operandTarget
    have leftRequestPositive : 0 < leftRequest :=
      leftCoherent.accuracyRequest_pos operandPositive
    have rightRequestPositive : 0 < rightRequest :=
      rightCoherent.accuracyRequest_pos operandPositive
    let sharedRequest := commonRequest leftRequest rightRequest
    have sharedPositive : 0 < sharedRequest :=
      commonRequest_pos leftRequestPositive rightRequestPositive
    exact Common.commonTarget_pos
      (Fraction.Order.Field.div_pos_direct positive (by decide))
      (divisionOuterTarget_pos left right apart.positive sharedPositive)
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    let semanticTarget := divisionSemanticTarget apart.lowerSq target
    have semanticPositive : 0 < semanticTarget :=
      divisionSemanticTarget_pos apart.positive positive
    let operandTarget := productInputTarget left right semanticTarget
    have operandPositive : 0 < operandTarget :=
      productInputTarget_pos left right semanticPositive
    let leftRequest := leftCoherent.accuracyRequest operandTarget
    let rightRequest := rightCoherent.accuracyRequest operandTarget
    have leftRequestPositive : 0 < leftRequest :=
      leftCoherent.accuracyRequest_pos operandPositive
    have rightRequestPositive : 0 < rightRequest :=
      rightCoherent.accuracyRequest_pos operandPositive
    let sharedRequest := commonRequest leftRequest rightRequest
    have sharedPositive : 0 < sharedRequest :=
      commonRequest_pos leftRequestPositive rightRequestPositive
    let outerTarget :=
      divisionOuterTarget left right apart.lowerSq sharedRequest
    have outerPositive : 0 < outerTarget :=
      divisionOuterTarget_pos left right apart.positive sharedPositive
    let radiusTarget := target / 2
    have radiusPositive : 0 < radiusTarget :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    change request <
      Common.commonTarget radiusTarget outerTarget
        at requestSmall
    have requestLtRadius : request < radiusTarget :=
      requestSmall.trans
        (Common.commonTarget_lt_left
          radiusPositive outerPositive)
    have requestLtOuter : request < outerTarget :=
      requestSmall.trans
        (Common.commonTarget_lt_right
          radiusPositive outerPositive)
    let leftName :=
      Name.centerOnly
        (left.ball state.1).center left.centerBound left.centerBound_nonneg
        (left.center_bounded state.1)
    let rightName :=
      Name.centerOnly
        (right.ball state.2).center right.centerBound right.centerBound_nonneg
        (right.center_bounded state.2)
    let processInputTarget :=
      Name.divisionInputTarget
        leftName rightName apart.lowerSq request
    have processInputPositive : 0 < processInputTarget :=
      Name.divisionInputTarget_pos
        leftName rightName apart.lowerSq apart.positive requestPositive
    have processInputLtShared : processInputTarget < sharedRequest :=
      processDivisionInputTarget_lt leftName rightName rfl rfl apart.positive
        requestLtOuter
    have processInputLtLeft : processInputTarget < leftRequest :=
      processInputLtShared.trans
        (commonRequest_lt_left leftRequestPositive rightRequestPositive)
    have processInputLtRight : processInputTarget < rightRequest :=
      processInputLtShared.trans
        (commonRequest_lt_right leftRequestPositive rightRequestPositive)
    have leftSmall :
        leftCoherent.allowance
            (left.refine state.1 processInputTarget processInputPositive) <
          operandTarget :=
      leftCoherent.refine_accurate state.1 operandTarget operandPositive
        processInputTarget processInputPositive processInputLtLeft
    have rightSmall :
        rightCoherent.allowance
            (right.refine state.2 processInputTarget processInputPositive) <
          operandTarget :=
      rightCoherent.refine_accurate state.2 operandTarget operandPositive
        processInputTarget processInputPositive processInputLtRight
    have semanticSmall :
        divisionSemanticAllowance left.centerBound right.centerBound
            apart.lowerSq
            (leftCoherent.allowance
              (left.refine state.1 processInputTarget processInputPositive))
            (rightCoherent.allowance
              (right.refine state.2 processInputTarget processInputPositive)) <
          target / 4 :=
      divisionSemanticAllowance_lt_quarter apart positive leftSmall rightSmall
        (leftCoherent.allowance_nonneg _)
        (rightCoherent.allowance_nonneg _)
    have radiusSmall :
        ((left.div right apart).ball
            ((left.div right apart).refine state request requestPositive)).radiusSq <
          target / 2 :=
      ((left.div right apart).accurate state request requestPositive).trans
        requestLtRadius
    change
      ((left.div right apart).ball
          ((left.div right apart).refine state request requestPositive)).radiusSq +
        divisionSemanticAllowance left.centerBound right.centerBound
          apart.lowerSq
          (leftCoherent.allowance
            (left.refine state.1 processInputTarget processInputPositive))
          (rightCoherent.allowance
            (right.refine state.2 processInputTarget processInputPositive)) <
        target
    exact (Arithmetic.add_lt_add_direct
      radiusSmall semanticSmall).trans (Purelib.Data.Rat.Bounds.Quarter.half_add_quarter_lt positive)

end Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent
