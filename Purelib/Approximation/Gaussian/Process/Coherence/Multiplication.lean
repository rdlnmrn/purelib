module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Multiplication
public import Purelib.Approximation.Rational.Budget.Product
public import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Approximation.Gaussian.Process.Multiplication
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Mul
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Request.Basic

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction.Order

/-!
# Coherence of Gaussian process multiplication

The original operand allowances bound both current ball radii and differences
between selected readings. Their product polynomial and common refinement
request certify the same paired-state multiplication process.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent

/-- The product ball's squared radius is bounded by the retained semantic product
allowance.

The original ball radii lie below their state allowances and their centres
meet the retained global bounds. Each original product-radius term is bounded
by the corresponding polynomial allowance term. -/
public theorem product_ball_radius_le
    {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right) (state : left.State × right.State) :
    ((left.ball state.1).mul (right.ball state.2)).radiusSq ≤
      productAllowance left.centerBound right.centerBound
        (leftCoherent.allowance state.1)
        (rightCoherent.allowance state.2) := by
  let leftRadius := (left.ball state.1).radiusSq
  let rightRadius := (right.ball state.2).radiusSq
  let leftAllowance := leftCoherent.allowance state.1
  let rightAllowance := rightCoherent.allowance state.2
  have leftRadiusLe : leftRadius ≤ leftAllowance :=
    leftCoherent.ball_radius_le state.1
  have rightRadiusLe : rightRadius ≤ rightAllowance :=
    rightCoherent.ball_radius_le state.2
  have firstTerm :
      leftRadius * Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center ≤
        leftAllowance * right.centerBound :=
    Arithmetic.mul_le_mul_direct leftRadiusLe
      (right.center_bounded state.2) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (leftCoherent.allowance_nonneg state.1)
  have secondTerm :
      Data.Gaussian.Norm.Basic.normSq (left.ball state.1).center * rightRadius ≤
        left.centerBound * rightAllowance :=
    Arithmetic.mul_le_mul_direct
      (left.center_bounded state.1) rightRadiusLe
      (right.ball state.2).radiusSq_nonneg left.centerBound_nonneg
  have productTerm : leftRadius * rightRadius ≤
      leftAllowance * rightAllowance :=
    Arithmetic.mul_le_mul_direct leftRadiusLe rightRadiusLe
      (right.ball state.2).radiusSq_nonneg
      (leftCoherent.allowance_nonneg state.1)
  have productNonnegative : 0 ≤ leftAllowance * rightAllowance :=
    Arithmetic.mul_nonneg_direct
      (leftCoherent.allowance_nonneg state.1)
      (rightCoherent.allowance_nonneg state.2)
  have leftSquareNonnegative : 0 ≤ leftAllowance * leftAllowance :=
    Arithmetic.mul_nonneg_direct
      (leftCoherent.allowance_nonneg state.1)
      (leftCoherent.allowance_nonneg state.1)
  have rightSquareNonnegative : 0 ≤ rightAllowance * rightAllowance :=
    Arithmetic.mul_nonneg_direct
      (rightCoherent.allowance_nonneg state.2)
      (rightCoherent.allowance_nonneg state.2)
  change 4 *
      (leftRadius * Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center +
        Data.Gaussian.Norm.Basic.normSq (left.ball state.1).center * rightRadius) +
      2 * (leftRadius * rightRadius) ≤
    productAllowance left.centerBound right.centerBound
      leftAllowance rightAllowance
  calc
    4 *
        (leftRadius * Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center +
          Data.Gaussian.Norm.Basic.normSq (left.ball state.1).center * rightRadius) +
        2 * (leftRadius * rightRadius) ≤
      4 * (leftAllowance * right.centerBound +
          left.centerBound * rightAllowance) +
        2 * (leftAllowance * rightAllowance) :=
      add_le_add
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide))
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          productTerm (by decide))
    _ ≤ 4 * (leftAllowance * right.centerBound +
          left.centerBound * rightAllowance) +
        2 * (leftAllowance * rightAllowance) +
        (2 * (leftAllowance * rightAllowance) +
          4 * (leftAllowance * leftAllowance) +
          4 * (rightAllowance * rightAllowance)) :=
      le_add_of_nonneg_right
        (add_nonneg
          (add_nonneg
            (Arithmetic.mul_nonneg_direct (by decide)
              productNonnegative)
            (Arithmetic.mul_nonneg_direct (by decide)
              leftSquareNonnegative))
          (Arithmetic.mul_nonneg_direct (by decide)
            rightSquareNonnegative))
    _ = productAllowance left.centerBound right.centerBound
        leftAllowance rightAllowance := by
      unfold productAllowance productBase
      ring1

/-- Products of possible readings at two paired states satisfy four times the
summed semantic product allowances.

Both operand processes retain their original two-state coherence bounds. The
four selected readings and their stored magnitude bounds control the squared
norm of the product difference. -/
public theorem product_possible_close
    {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right)
    {leftState rightState : left.State × right.State}
    {leftX leftY rightX rightY : Data.Gaussian.Basic.Canonical}
    (leftXPossible : left.Possible leftState.1 leftX)
    (leftYPossible : right.Possible leftState.2 leftY)
    (rightXPossible : left.Possible rightState.1 rightX)
    (rightYPossible : right.Possible rightState.2 rightY) :
    Data.Gaussian.Norm.Basic.normSq (leftX * leftY - rightX * rightY) ≤
      4 *
        (productAllowance left.centerBound right.centerBound
            (leftCoherent.allowance leftState.1)
            (rightCoherent.allowance leftState.2) +
          productAllowance left.centerBound right.centerBound
            (leftCoherent.allowance rightState.1)
            (rightCoherent.allowance rightState.2)) := by
  let leftOne := leftCoherent.allowance leftState.1
  let leftTwo := leftCoherent.allowance rightState.1
  let rightOne := rightCoherent.allowance leftState.2
  let rightTwo := rightCoherent.allowance rightState.2
  have leftClose : Data.Gaussian.Norm.Basic.normSq (leftX - rightX) ≤
      4 * (leftOne + leftTwo) :=
    leftCoherent.possible_close leftXPossible rightXPossible
  have rightClose : Data.Gaussian.Norm.Basic.normSq (leftY - rightY) ≤
      4 * (rightOne + rightTwo) :=
    rightCoherent.possible_close leftYPossible rightYPossible
  have rightOneNorm : Data.Gaussian.Norm.Basic.normSq leftY ≤
      2 * (rightOne + right.centerBound) :=
    possible_normSq_le rightCoherent leftYPossible
  have leftTwoNorm : Data.Gaussian.Norm.Basic.normSq rightX ≤
      2 * (leftTwo + left.centerBound) :=
    possible_normSq_le leftCoherent rightXPossible
  have leftSumNonnegative : 0 ≤ 4 * (leftOne + leftTwo) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (leftCoherent.allowance_nonneg leftState.1)
        (leftCoherent.allowance_nonneg rightState.1))
  have leftNormBoundNonnegative :
      0 ≤ 2 * (leftTwo + left.centerBound) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (leftCoherent.allowance_nonneg rightState.1)
        left.centerBound_nonneg)
  have firstTerm :
      Data.Gaussian.Norm.Basic.normSq ((leftX - rightX) * leftY) ≤
        (4 * (leftOne + leftTwo)) *
          (2 * (rightOne + right.centerBound)) := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      leftClose rightOneNorm (Data.Gaussian.Norm.Basic.normSq_nonneg leftY) leftSumNonnegative
  have secondTerm :
      Data.Gaussian.Norm.Basic.normSq (rightX * (leftY - rightY)) ≤
        (2 * (leftTwo + left.centerBound)) *
          (4 * (rightOne + rightTwo)) := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      leftTwoNorm rightClose (Data.Gaussian.Norm.Basic.normSq_nonneg (leftY - rightY))
      leftNormBoundNonnegative
  have difference :
      leftX * leftY - rightX * rightY =
        (leftX - rightX) * leftY + rightX * (leftY - rightY) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1
  have crossBound := product_cross_bound
    left.centerBound right.centerBound leftOne leftTwo rightOne rightTwo
    (leftCoherent.allowance_nonneg leftState.1)
    (rightCoherent.allowance_nonneg rightState.2)
  rw [difference]
  calc
    Data.Gaussian.Norm.Basic.normSq
        ((leftX - rightX) * leftY + rightX * (leftY - rightY)) ≤
      2 * (Data.Gaussian.Norm.Basic.normSq ((leftX - rightX) * leftY) +
        Data.Gaussian.Norm.Basic.normSq (rightX * (leftY - rightY))) :=
      Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 *
        ((4 * (leftOne + leftTwo)) *
            (2 * (rightOne + right.centerBound)) +
          (2 * (leftTwo + left.centerBound)) *
            (4 * (rightOne + rightTwo))) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstTerm secondTerm) (by decide)
    _ = 16 *
        ((leftOne + leftTwo) * (rightOne + right.centerBound) +
          (leftTwo + left.centerBound) * (rightOne + rightTwo)) := by ring1
    _ ≤ 16 *
        (productBase left.centerBound right.centerBound leftOne rightOne +
          productBase left.centerBound right.centerBound leftTwo rightTwo) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        crossBound (by decide)
    _ = 4 *
        (productAllowance left.centerBound right.centerBound
            (leftCoherent.allowance leftState.1)
            (rightCoherent.allowance leftState.2) +
          productAllowance left.centerBound right.centerBound
            (leftCoherent.allowance rightState.1)
            (rightCoherent.allowance rightState.2)) := by
      dsimp only [leftOne, leftTwo, rightOne, rightTwo]
      unfold productAllowance
      ring1

/-- A strictly positive coefficient for the conservative semantic product
allowance.

The coefficient retains the two original global centre bounds together with
the fixed three-unit square margin. Scaling their sum by four bounds the
polynomial product allowance. -/
@[expose] public def productCoefficient (left right : Process) : Fraction.Rational :=
  4 * (3 + left.centerBound + right.centerBound)

/-- The semantic product error coefficient computed from the original centre
bounds is strictly positive.

The two original centre bounds are nonnegative. The fixed positive three-unit
margin survives both additions and multiplication by four. -/
public theorem productCoefficient_pos (left right : Process) :
    0 < productCoefficient left right := by
  unfold productCoefficient
  exact Arithmetic.mul_pos_direct (by decide)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) left.centerBound_nonneg)
      right.centerBound_nonneg)

/-- A finite operand-allowance target which is below one and whose product with
`productCoefficient` is below the requested result allowance.

The requested target is divided by its sum with the original positive
coefficient. The exact same rational request simultaneously controls the unit
bound and the scaled error budget. -/
@[expose] public def productInputTarget (left right : Process) (target : Fraction.Rational) :
    Fraction.Rational :=
  target / (target + productCoefficient left right)

/-- A positive semantic output target gives a positive common operand allowance
request.

The positive target and the retained positive coefficient give a positive
denominator. The original quotient request is therefore positive. -/
public theorem productInputTarget_pos (left right : Process) {target : Fraction.Rational}
    (positive : 0 < target) : 0 < productInputTarget left right target :=
  Fraction.Order.Field.div_pos_direct positive
    (Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (Arithmetic.le_of_lt_direct
        (productCoefficient_pos left right)))

/-- The common semantic product input target is strictly below one.

The original coefficient is strictly positive. Adding it to the positive
target makes the denominator strictly greater than the numerator. -/
public theorem productInputTarget_lt_one (left right : Process)
    {target : Fraction.Rational} (positive : 0 < target) :
    productInputTarget left right target < 1 := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (Arithmetic.le_of_lt_direct
        (productCoefficient_pos left right)))).2
  calc
    target < target + productCoefficient left right :=
      by
        have shifted := Arithmetic.add_lt_add_left_direct
          (productCoefficient_pos left right) target
        rewrite [_root_.add_zero] at shifted
        exact shifted
    _ = 1 * (target + productCoefficient left right) := by ring1

/-- The common product input target times its error coefficient lies strictly
below the positive output allowance.

The denominator exceeds the original coefficient by the positive target.
Multiplying the same request by that coefficient gives a strict bound below
the target. -/
public theorem productInputTarget_budget_lt (left right : Process)
    {target : Fraction.Rational} (positive : 0 < target) :
    productInputTarget left right target * productCoefficient left right <
      target := by
  have denominatorPositive :
      0 < target + productCoefficient left right :=
    Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (Arithmetic.le_of_lt_direct
        (productCoefficient_pos left right))
  change target / (target + productCoefficient left right) *
      productCoefficient left right < target
  calc
    target / (target + productCoefficient left right) *
        productCoefficient left right =
      (target * productCoefficient left right) /
        (target + productCoefficient left right) :=
      Fraction.Field.quotient_mul_reorder _ _ _
    _ < target := by
      apply (Fraction.Order.Field.div_lt_iff_pos
        denominatorPositive).2
      have coefficientLt : productCoefficient left right <
          target + productCoefficient left right := by
        calc
          productCoefficient left right =
              0 + productCoefficient left right :=
            (show (0 : Fraction.Rational) + productCoefficient left right =
                productCoefficient left right from _root_.zero_add _).symm
          _ < target + productCoefficient left right :=
            Arithmetic.add_lt_add_right_direct positive _
      exact Arithmetic.mul_lt_mul_of_pos_left_direct
        positive coefficientLt

/-- Nonnegative operand allowances below the common product input target yield
semantic product allowance below the output target.

Both nonnegative operand allowances lie strictly below the same original input
target. Its unit bound controls the square terms and its coefficient bound
controls their complete product allowance. -/
public theorem mul_allowances_lt_target
    {left right : Process} {leftAllowance rightAllowance target : Fraction.Rational}
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance)
    (targetPositive : 0 < target)
    (leftSmall : leftAllowance < productInputTarget left right target)
    (rightSmall : rightAllowance < productInputTarget left right target) :
    productAllowance left.centerBound right.centerBound
        leftAllowance rightAllowance < target := by
  generalize epsilonIdentity :
    productInputTarget left right target = epsilon at leftSmall rightSmall
  have epsilonPositive : 0 < epsilon :=
    epsilonIdentity ▸ productInputTarget_pos left right targetPositive
  have epsilonLtOne : epsilon < 1 :=
    epsilonIdentity ▸ productInputTarget_lt_one left right targetPositive
  have leftLtOne : leftAllowance < 1 := leftSmall.trans epsilonLtOne
  have rightLtOne : rightAllowance < 1 := rightSmall.trans epsilonLtOne
  have productSmall : leftAllowance * rightAllowance < epsilon := by
    calc
      leftAllowance * rightAllowance ≤ epsilon * rightAllowance :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          leftSmall.le rightNonnegative
      _ < epsilon * 1 :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          epsilonPositive rightLtOne
      _ = epsilon := Fraction.Field.mul_one_direct _
  have leftSquareSmall : leftAllowance * leftAllowance < epsilon := by
    calc
      leftAllowance * leftAllowance ≤ epsilon * leftAllowance :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          leftSmall.le leftNonnegative
      _ < epsilon * 1 :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          epsilonPositive leftLtOne
      _ = epsilon := Fraction.Field.mul_one_direct _
  have rightSquareSmall : rightAllowance * rightAllowance < epsilon := by
    calc
      rightAllowance * rightAllowance ≤ epsilon * rightAllowance :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          rightSmall.le rightNonnegative
      _ < epsilon * 1 :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          epsilonPositive rightLtOne
      _ = epsilon := Fraction.Field.mul_one_direct _
  have leftLinear : leftAllowance * right.centerBound ≤
      epsilon * right.centerBound :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      leftSmall.le right.centerBound_nonneg
  have rightLinear : left.centerBound * rightAllowance ≤
      left.centerBound * epsilon :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      rightSmall.le left.centerBound_nonneg
  have firstTwo := Arithmetic.add_lt_add_direct
    productSmall leftSquareSmall
  have firstThree := Arithmetic.add_lt_add_direct
    firstTwo rightSquareSmall
  have withLeftLinear :
      leftAllowance * rightAllowance +
          leftAllowance * leftAllowance +
          rightAllowance * rightAllowance +
          leftAllowance * right.centerBound <
        epsilon + epsilon + epsilon + epsilon * right.centerBound :=
    (Arithmetic.add_lt_add_right_direct firstThree
      (leftAllowance * right.centerBound)).trans_le
        (add_le_add_right leftLinear (epsilon + epsilon + epsilon))
  have baseSmall :
      leftAllowance * rightAllowance +
          leftAllowance * leftAllowance +
          rightAllowance * rightAllowance +
          leftAllowance * right.centerBound +
          left.centerBound * rightAllowance <
        epsilon + epsilon + epsilon + epsilon * right.centerBound +
          left.centerBound * epsilon :=
    (Arithmetic.add_lt_add_right_direct withLeftLinear
      (left.centerBound * rightAllowance)).trans_le
        (add_le_add_right rightLinear
          (epsilon + epsilon + epsilon + epsilon * right.centerBound))
  have scaledBaseSmall :=
    Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide : (0 : Fraction.Rational) < 4) baseSmall
  calc
    productAllowance left.centerBound right.centerBound
        leftAllowance rightAllowance <
      4 *
        ((epsilon + epsilon + epsilon) +
          epsilon * right.centerBound + left.centerBound * epsilon) := by
      exact scaledBaseSmall
    _ = epsilon * productCoefficient left right := by
      unfold productCoefficient
      ring1
    _ < target := by
      rw [← epsilonIdentity]
      exact productInputTarget_budget_lt left right targetPositive

/-- Finite process coherence is preserved by multiplication. The semantic
allowance includes the two squared operand allowances needed to absorb cross-
state uncertainty; the computed process request is correspondingly smaller
than the final requested product allowance.

The original paired states retain both operand allowances and request
procedures. The same product budget and common request provide the coherence
bounds and refinement certificates for the original multiplication process. -/
@[expose] public def mul {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right) : Coherent (left.mul right) where
  allowance state :=
    productAllowance left.centerBound right.centerBound
      (leftCoherent.allowance state.1) (rightCoherent.allowance state.2)
  allowance_nonneg state :=
    Arithmetic.mul_nonneg_direct (by decide)
      (productBase_nonneg left.centerBound_nonneg right.centerBound_nonneg
        (leftCoherent.allowance_nonneg state.1)
        (rightCoherent.allowance_nonneg state.2))
  ball_radius_le := product_ball_radius_le leftCoherent rightCoherent
  possible_close := by
    rintro leftState rightState leftValue rightValue
      ⟨leftX, leftY, leftXPossible, leftYPossible, rfl⟩
      ⟨rightX, rightY, rightXPossible, rightYPossible, rfl⟩
    exact product_possible_close leftCoherent rightCoherent
      leftXPossible leftYPossible rightXPossible rightYPossible
  accuracyRequest target :=
    let semanticInputTarget := productInputTarget left right target
    commonRequest
      (leftCoherent.accuracyRequest semanticInputTarget)
      (rightCoherent.accuracyRequest semanticInputTarget)
  accuracyRequest_pos := by
    intro target positive
    let semanticInputTarget := productInputTarget left right target
    have semanticPositive : 0 < semanticInputTarget :=
      productInputTarget_pos left right positive
    exact commonRequest_pos
      (leftCoherent.accuracyRequest_pos semanticPositive)
      (rightCoherent.accuracyRequest_pos semanticPositive)
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    let semanticInputTarget := productInputTarget left right target
    have semanticPositive : 0 < semanticInputTarget :=
      productInputTarget_pos left right positive
    let leftRequest := leftCoherent.accuracyRequest semanticInputTarget
    let rightRequest := rightCoherent.accuracyRequest semanticInputTarget
    have leftRequestPositive : 0 < leftRequest :=
      leftCoherent.accuracyRequest_pos semanticPositive
    have rightRequestPositive : 0 < rightRequest :=
      rightCoherent.accuracyRequest_pos semanticPositive
    let sharedRequest := commonRequest leftRequest rightRequest
    have sharedPositive : 0 < sharedRequest :=
      commonRequest_pos leftRequestPositive rightRequestPositive
    change request < sharedRequest at requestSmall
    let leftName :=
      Name.centerOnly
        (left.ball state.1).center left.centerBound left.centerBound_nonneg
        (left.center_bounded state.1)
    let rightName :=
      Name.centerOnly
        (right.ball state.2).center right.centerBound right.centerBound_nonneg
        (right.center_bounded state.2)
    let processInputTarget :=
      Name.multiplicativeInputTarget
        leftName rightName request
    have processInputPositive : 0 < processInputTarget :=
      Name.multiplicativeInputTarget_pos
        leftName rightName requestPositive
    have processInputLtRequest : processInputTarget < request :=
      processMultiplicativeInputTarget_lt_target
        leftName rightName requestPositive
    have processInputLtShared : processInputTarget < sharedRequest :=
      processInputLtRequest.trans requestSmall
    have processInputLtLeft : processInputTarget < leftRequest :=
      processInputLtShared.trans
        (commonRequest_lt_left leftRequestPositive rightRequestPositive)
    have processInputLtRight : processInputTarget < rightRequest :=
      processInputLtShared.trans
        (commonRequest_lt_right leftRequestPositive rightRequestPositive)
    have leftSmall :
        leftCoherent.allowance
            (left.refine state.1 processInputTarget processInputPositive) <
          semanticInputTarget :=
      leftCoherent.refine_accurate state.1 semanticInputTarget semanticPositive
        processInputTarget processInputPositive processInputLtLeft
    have rightSmall :
        rightCoherent.allowance
            (right.refine state.2 processInputTarget processInputPositive) <
          semanticInputTarget :=
      rightCoherent.refine_accurate state.2 semanticInputTarget semanticPositive
        processInputTarget processInputPositive processInputLtRight
    change productAllowance left.centerBound right.centerBound
        (leftCoherent.allowance
          (left.refine state.1 processInputTarget processInputPositive))
        (rightCoherent.allowance
          (right.refine state.2 processInputTarget processInputPositive)) <
      target
    exact mul_allowances_lt_target
      (leftCoherent.allowance_nonneg _)
      (rightCoherent.allowance_nonneg _) positive leftSmall rightSmall

end Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent
