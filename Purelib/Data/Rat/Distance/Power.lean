module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Concentration of squared-sensitive probes inside one finite CCL cylinder

For a probe satisfying a squared-separation sensitivity estimate, CCL's
`2^-k` squared-chordal cylinder contraction gives a `factor * 2^-k` second
moment bound directly.  This is the natural rate for nonconstant Lipschitz
observables and avoids selecting a square root.

Every statement concerns an explicitly supplied finite distribution and
finite realization traces.  No measure on an infinite cylinder is formed.
-/

namespace Purelib.CCL.Measure

end Purelib.CCL.Measure

end

section
@[expose] public section

/-!
# Threshold stability for squared-sensitive finite CCL probes

Discontinuous threshold events cannot be controlled from a shrinking metric
bound alone when a value may lie on the threshold.  An explicit positive
rational witness margin repairs this constructively.  Squared-probe
sensitivity then requires a finite request at `margin^2`; after that request
every compatible realization has exactly the witness's Boolean
classification, so all resulting finite probabilities are equal.
-/

namespace Purelib.CCL.Measure

end Purelib.CCL.Measure

end

section
section
@[expose] public section

/-!
# Natural-powered finite Lp geometry

Natural powers of rational separations satisfy a uniform constructive
quasi-triangle estimate.  The factor `2 ^ exponent` is intentionally coarse:
it is obtained from a finite maximum comparison and works also at exponent
zero, without roots, real exponentiation, or convexity machinery.
-/

namespace Purelib.Data.Rat.Distance

section
open Purelib.Data.Rat
/-- A nonnegative value below the sum of two nonnegative rationals has each natural power bounded by two to that power
times their power sum. -/
theorem pow_le_two_pow_mul_add
    (exponent : Nat) (value left right : Fraction.Rational)
    (valueNonnegative : 0 ≤ value)
    (leftNonnegative : 0 ≤ left)
    (rightNonnegative : 0 ≤ right)
    (bound : value ≤ left + right) :
    value ^ exponent ≤
      (2 : Fraction.Rational) ^ exponent *
        (left ^ exponent + right ^ exponent) := by
  have sumNonnegative : 0 ≤ left + right :=
    add_nonneg leftNonnegative rightNonnegative
  have sumLe : left + right ≤ 2 * max left right := by
    by_cases order : left ≤ right
    · rw [Fraction.Order.Basic.max_eq_right order]
      calc
        left + right ≤ right + right :=
          Fraction.Order.Arithmetic.add_le_add_direct order le_rfl
        _ = 2 * right := by ring1
    · have reverse : right ≤ left :=
        (Fraction.Order.Arithmetic.lt_of_not_ge_direct order).le
      rw [Fraction.Order.Basic.max_eq_left reverse]
      calc
        left + right ≤ left + left :=
          Fraction.Order.Arithmetic.add_le_add_direct le_rfl reverse
        _ = 2 * left := by ring1
  have valueLeTwice : value ≤ 2 * max left right :=
    bound.trans sumLe
  have valuePowerLe : value ^ exponent ≤
      (2 * max left right) ^ exponent :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      valueNonnegative valueLeTwice exponent
  have maximumPowerLe : (max left right) ^ exponent ≤
      left ^ exponent + right ^ exponent := by
    by_cases order : left ≤ right
    · rw [Fraction.Order.Basic.max_eq_right order]
      calc
        right ^ exponent = 0 + right ^ exponent := by ring1
        _ ≤ left ^ exponent + right ^ exponent :=
          Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Arithmetic.pow_nonneg_direct
              leftNonnegative exponent) le_rfl
    · have reverse : right ≤ left :=
        (Fraction.Order.Arithmetic.lt_of_not_ge_direct order).le
      rw [Fraction.Order.Basic.max_eq_left reverse]
      calc
        left ^ exponent = left ^ exponent + 0 := by ring1
        _ ≤ left ^ exponent + right ^ exponent :=
          Fraction.Order.Arithmetic.add_le_add_direct le_rfl
            (Fraction.Order.Arithmetic.pow_nonneg_direct
              rightNonnegative exponent)
  have scaledMaximumPowerLe :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      maximumPowerLe
      (Fraction.Order.Arithmetic.pow_nonneg_direct
        (by decide : (0 : Fraction.Rational) ≤ 2) exponent)
  calc
    value ^ exponent ≤ (2 * max left right) ^ exponent := valuePowerLe
    _ = (2 : Fraction.Rational) ^ exponent * (max left right) ^ exponent := by
      clear valuePowerLe maximumPowerLe scaledMaximumPowerLe
      induction exponent with
      | zero => ring1
      | succ exponent inductionHypothesis =>
          rw [pow_succ, pow_succ, pow_succ, inductionHypothesis]
          ring1
    _ ≤ (2 : Fraction.Rational) ^ exponent *
          (left ^ exponent + right ^ exponent) := scaledMaximumPowerLe

/-- The natural power of a sum's distance from zero is bounded by two to that power times the sum of the component
distance powers. -/
theorem rationalSeparation_add_pow_le_two_pow_mul
    (exponent : Nat) (left right : Fraction.Rational) :
    Distance.rationalSeparation (left + right) 0 ^ exponent ≤
      (2 : Fraction.Rational) ^ exponent *
        (Distance.rationalSeparation left 0 ^ exponent +
          Distance.rationalSeparation right 0 ^ exponent) :=
  pow_le_two_pow_mul_add exponent
    (Distance.rationalSeparation (left + right) 0)
    (Distance.rationalSeparation left 0) (Distance.rationalSeparation right 0)
    (Distance.rationalSeparation_nonneg _ _)
    (Distance.rationalSeparation_nonneg _ _)
    (Distance.rationalSeparation_nonneg _ _)
    (Distance.rationalSeparation_add_zero_le left right)

/-- The natural power of an endpoint separation is bounded by two to that power times the sum of the two separations
through a middle point. -/
theorem rationalSeparation_pow_triangle_le_two_pow_mul
    (exponent : Nat) (left middle right : Fraction.Rational) :
    Distance.rationalSeparation left right ^ exponent ≤
      (2 : Fraction.Rational) ^ exponent *
        (Distance.rationalSeparation left middle ^ exponent +
          Distance.rationalSeparation middle right ^ exponent) :=
  pow_le_two_pow_mul_add exponent
    (Distance.rationalSeparation left right)
    (Distance.rationalSeparation left middle) (Distance.rationalSeparation middle right)
    (Distance.rationalSeparation_nonneg _ _)
    (Distance.rationalSeparation_nonneg _ _)
    (Distance.rationalSeparation_nonneg _ _)
    (Distance.rationalSeparation_triangle left middle right)

end

namespace Content
end Content

namespace Distribution
end Distribution

end Purelib.Data.Rat.Distance

end

end

section
@[expose] public section

/-!
# Natural-powered finite Lp quantities

Natural powers of rational separation remain rational.  They provide exact
finite powered-Lp quantities and tail estimates without selecting roots or
constructing completed normed spaces.
-/

namespace Purelib.Data.Rat.Distance

open Purelib.Data.Rat
/-- The square of rational separation equals the square of the endpoint difference. -/
theorem NaturalLp.rationalSeparation_sq (left right : Fraction.Rational) :
    Distance.rationalSeparation left right ^ 2 = (left - right) ^ 2 := by
  have separationSub : Distance.rationalSeparation left right =
      Distance.rationalSeparation (left - right) 0 := by
    unfold Distance.rationalSeparation
    congr 1 <;> ring1
  rw [separationSub]
  calc
    Distance.rationalSeparation (left - right) 0 ^ 2 =
        Distance.rationalSeparation (left - right) 0 *
          Distance.rationalSeparation (left - right) 0 := by
      ring1
    _ = Distance.rationalSeparation ((left - right) * (left - right)) 0 :=
      (Distance.rationalSeparation_mul_zero (left - right) (left - right)).symm
    _ = (left - right) * (left - right) := by
      apply Distance.rationalSeparation_zero_of_nonneg
      have squareNonnegative :=
        Fraction.Order.Arithmetic.sq_nonneg_direct (left - right)
      simpa only [pow_two] using squareNonnegative
    _ = (left - right) ^ 2 := by ring1

/-- A squared separation below a positive tolerance square gives separation below that tolerance. -/
theorem rationalSeparation_lt_of_sq_lt_sq
    {left right tolerance : Fraction.Rational} (positive : 0 < tolerance)
    (small : Distance.rationalSeparation left right ^ 2 < tolerance ^ 2) :
    Distance.rationalSeparation left right < tolerance := by
  rcases lt_trichotomy (Distance.rationalSeparation left right) tolerance with
    less | equal | greater
  · exact less
  · subst tolerance
    exact (lt_irrefl _ small).elim
  · have squareOrder := Fraction.Order.Arithmetic.pow_le_pow_direct
      positive.le greater.le 2
    exact ((not_lt_of_ge squareOrder) small).elim

end Purelib.Data.Rat.Distance

end

section
@[expose] public section

/-!
# Finite uniform-integrability tail budgets

The absolute tail of one rational observable is an executable threshold event
and an exact rational integral.  A second-moment bound controls this tail by
`poweredL2 / threshold`.  A displayed finite family with one common
second-moment ceiling therefore has one uniform rational tail budget.

This retains the quantitative finite content used in uniform-integrability
arguments without quantifying over an infinite family or taking a limit as
the threshold tends to infinity.
-/

namespace Purelib.Data.Rat.Distance

open Purelib.Data.Rat in
/-- The square of a rational's separation from zero equals the rational square. -/
theorem rationalSeparation_zero_sq (value : Fraction.Rational) :
    Distance.rationalSeparation value 0 ^ 2 = value ^ 2 := by
  have multiplicative := Distance.rationalSeparation_mul_zero value value
  have squareNonnegative : 0 ≤ value * value := by
    simpa only [pow_two] using
      Fraction.Order.Arithmetic.sq_nonneg_direct value
  rw [Distance.rationalSeparation_zero_of_nonneg squareNonnegative] at multiplicative
  simpa only [pow_two] using multiplicative.symm

end Purelib.Data.Rat.Distance

end

section
@[expose] public section

/-!
# Uniform stability of finite rational variance

Uniformly close rational observables taking values in `[0, 1]` have close
exact finite variances.  The proof compares their second moments and squared
means directly, using only finite expectations and rational separation.
-/

namespace Purelib.Data.Rat.Distance

open Purelib.Data.Rat in
/-- Squaring two rationals in the unit interval increases their separation by at most a factor of two. -/
theorem rationalSeparation_sq_le_two_mul
    {left right : Fraction.Rational}
    (leftNonnegative : 0 ≤ left) (leftLeOne : left ≤ 1)
    (rightNonnegative : 0 ≤ right) (rightLeOne : right ≤ 1) :
    Distance.rationalSeparation (left ^ 2) (right ^ 2) ≤
      2 * Distance.rationalSeparation left right := by
  have sumNonnegative : 0 ≤ left + right :=
    add_nonneg leftNonnegative rightNonnegative
  have sumLeTwo : left + right ≤ 2 := by
    calc
      left + right ≤ 1 + 1 :=
        Fraction.Order.Arithmetic.add_le_add_direct leftLeOne rightLeOne
      _ = 2 := by ring1
  have separationNonnegative := Distance.rationalSeparation_nonneg left right
  unfold Distance.rationalSeparation
  apply Fraction.Order.Basic.max_le
  · calc
      left ^ 2 - right ^ 2 = (left - right) * (left + right) := by ring1
      _ ≤ max (left - right) (right - left) * (left + right) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Basic.le_max_left _ _) sumNonnegative
      _ ≤ max (left - right) (right - left) * 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          sumLeTwo separationNonnegative
      _ = 2 * max (left - right) (right - left) := by ring1
  · calc
      right ^ 2 - left ^ 2 = (right - left) * (left + right) := by ring1
      _ ≤ max (left - right) (right - left) * (left + right) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Basic.le_max_right _ _) sumNonnegative
      _ ≤ max (left - right) (right - left) * 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          sumLeTwo separationNonnegative
      _ = 2 * max (left - right) (right - left) := by ring1

end Purelib.Data.Rat.Distance

end

section
@[expose] public section

/-!
# An L2 finite Vitali bridge

An in-measure certificate controls the probability of one threshold-error
event.  Cauchy--Schwarz controls the error integral on that event by its
powered-L2 size.  To remain rational and executable, the conclusion squares
the nonnegative L1 excess instead of introducing a square root.
-/

namespace Purelib.Data.Rat.Distance.VitaliL2

open Purelib.Data.Rat in
/-- The square of rational separation equals the square of the endpoint difference. -/
theorem rationalSeparation_sq_eq_sub_sq (left right : Fraction.Rational) :
    Distance.rationalSeparation left right ^ 2 = (left - right) ^ 2 := by
  have same : Distance.rationalSeparation left right =
      Distance.rationalSeparation (left - right) 0 := by
    unfold Distance.rationalSeparation
    congr 1 <;> ring1
  rw [same, Distance.rationalSeparation_zero_sq]

end Purelib.Data.Rat.Distance.VitaliL2

end
