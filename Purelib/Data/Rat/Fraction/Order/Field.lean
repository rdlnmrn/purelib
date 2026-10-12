module
import Purelib.Algebra.NatCast
public import Purelib.Algebra.Semiring.Nat
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.Ring
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Data.Rat.Fraction.Order.Basic

section
public section

/-!
# Compatibility surface for canonical fractions

This module provides the compatibility operations now owned by
`Purelib.Data.Rat.Fraction.Compatibility` over the quotient-free rational carrier.  All operations use the canonical
structural rational carrier.

The signed-denominator `SignedFraction` record remains available as input syntax.
Its positivity proof makes conversion to the canonical natural-denominator
display total and executable.  Semantic rationals themselves are reduced
structural records; `representative` therefore exposes data already present
in the value rather than selecting a member of a quotient.
-/

namespace Purelib.Data.Rat.Fraction.Order.Field

open Purelib.Data.Rat
/-- Division by a positive rational converts a weak upper bound to multiplication by that denominator. -/
theorem div_le_iff_pos {left right denominator : Fraction.Rational}
    (denominatorPositive : 0 < denominator) :
    left / denominator ≤ right ↔ left ≤ right * denominator := by
  constructor
  · intro lessEqual
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct lessEqual
      denominatorPositive.le
    rwa [Fraction.Field.div_mul_cancel_of_ne left denominator denominatorPositive.ne'] at scaled
  · intro lessEqual
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := denominator) _
      denominatorPositive
    rwa [Fraction.Field.div_mul_cancel_of_ne left denominator denominatorPositive.ne']

/-- A weak lower bound on a quotient with positive denominator is equivalent to its multiplied bound. -/
theorem le_div_iff_pos {left right denominator : Fraction.Rational}
    (denominatorPositive : 0 < denominator) :
    left ≤ right / denominator ↔ left * denominator ≤ right := by
  constructor
  · intro lessEqual
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct lessEqual
      denominatorPositive.le
    rwa [Fraction.Field.div_mul_cancel_of_ne right denominator denominatorPositive.ne'] at scaled
  · intro lessEqual
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := denominator) _
      denominatorPositive
    rwa [Fraction.Field.div_mul_cancel_of_ne right denominator denominatorPositive.ne']

/-- Division by a positive rational converts a strict upper bound to multiplication by that denominator. -/
theorem div_lt_iff_pos {left right denominator : Fraction.Rational}
    (denominatorPositive : 0 < denominator) :
    left / denominator < right ↔ left < right * denominator := by
  constructor
  · intro less
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct less denominatorPositive
    rwa [Fraction.Field.div_mul_cancel_of_ne left denominator denominatorPositive.ne'] at scaled
  · intro less
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := denominator) _
      denominatorPositive
    rwa [Fraction.Field.div_mul_cancel_of_ne left denominator denominatorPositive.ne']

/-- A strict lower bound on a quotient with positive denominator is equivalent to its multiplied bound. -/
theorem lt_div_iff_pos {left right denominator : Fraction.Rational}
    (denominatorPositive : 0 < denominator) :
    left < right / denominator ↔ left * denominator < right := by
  constructor
  · intro less
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct less denominatorPositive
    rwa [Fraction.Field.div_mul_cancel_of_ne right denominator denominatorPositive.ne'] at scaled
  · intro less
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := denominator) _
      denominatorPositive
    rwa [Fraction.Field.div_mul_cancel_of_ne right denominator denominatorPositive.ne']

/-- The reciprocal of a positive rational is positive. -/
theorem inv_pos_direct {source : Fraction.Rational} (positive : 0 < source)
  :
    0 < source⁻¹ := by
  have productPositive : 0 < source * source⁻¹ := by
    rw [Fraction.Field.mul_inv_cancel source positive.ne']
    decide
  exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct productPositive positive.le

/-- Reciprocals reverse weak comparison between positive rationals. -/
theorem inv_le_inv_of_pos_direct {left right : Fraction.Rational}
    (leftPositive : 0 < left) (lessEqual : left ≤ right) :
    right⁻¹ ≤ left⁻¹ := by
  have rightPositive : 0 < right := leftPositive.trans_le lessEqual
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := left) _ leftPositive
  calc
    right⁻¹ * left ≤ right⁻¹ * right :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lessEqual (Fraction.Order.Field.inv_pos_direct
        rightPositive).le
    _ = 1 := Fraction.Field.inv_mul_cancel right rightPositive.ne'
    _ = left⁻¹ * left := (Fraction.Field.inv_mul_cancel left leftPositive.ne').symm

/-- A quotient of positive rationals is positive. -/
theorem div_pos_direct {numerator denominator : Fraction.Rational}
    (numeratorPositive : 0 < numerator)
    (denominatorPositive : 0 < denominator) :
    0 < numerator / denominator := by
  change 0 < numerator * denominator⁻¹
  exact Fraction.Order.Arithmetic.mul_pos_direct numeratorPositive (Fraction.Order.Field.inv_pos_direct
    denominatorPositive)

/-- A quotient of nonnegative rationals is nonnegative, including the total zero-denominator case. -/
theorem div_nonneg_direct {numerator denominator : Fraction.Rational}
    (numeratorNonnegative : 0 ≤ numerator)
    (denominatorNonnegative : 0 ≤ denominator) :
    0 ≤ numerator / denominator := by
  by_cases numeratorZero : numerator = 0
  · rw [numeratorZero, Fraction.Field.zero_div_direct]
  · by_cases denominatorZero : denominator = 0
    · rw [denominatorZero, Fraction.Field.div_zero_direct]
    · exact (Fraction.Order.Field.div_pos_direct
        ⟨numeratorNonnegative, fun reverse => numeratorZero
          (Order.Basic.le_antisymm numerator 0
            reverse numeratorNonnegative)⟩
        ⟨denominatorNonnegative, fun reverse => denominatorZero
          (Order.Basic.le_antisymm denominator 0
            reverse denominatorNonnegative)⟩).le

/-- Increasing a positive denominator decreases the quotient of a fixed nonnegative numerator. -/
theorem div_le_div_of_nonneg_left_direct {numerator left right :
  Fraction.Rational}
    (numeratorNonnegative : 0 ≤ numerator)
    (leftPositive : 0 < left) (lessEqual : left ≤ right) :
    numerator / right ≤ numerator / left := by
  change numerator * right⁻¹ ≤ numerator * left⁻¹
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Field.inv_le_inv_of_pos_direct leftPositive lessEqual)
    numeratorNonnegative
end Purelib.Data.Rat.Fraction.Order.Field

end

end

section
public section

/-!
# Requested error budgets for finite sums

The local squared-error request pays both factors of the actual term count.
The positive `count + 1` denominator also handles an empty sum without a
nonemptiness premise.  Nothing here holds the term count fixed across requests.
-/

namespace Purelib.Data.Rat.Fraction.Order.Field

open Purelib.Data.Rat
/-- Division by a fixed positive rational preserves weak numerator comparison. -/
theorem divide_mono {first second denominator : Fraction.Rational} (order :
  first ≤ second)
    (positive : 0 < denominator) : first / denominator ≤ second / denominator := by
  rw [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct order
    (Fraction.Order.Field.inv_pos_direct positive).le

/-- Dividing a nonnegative rational by a denominator at least one cannot increase it. -/
theorem divide_le_self {value denominator : Fraction.Rational} (nonnegative
  : 0 ≤ value)
    (atLeastOne : 1 ≤ denominator) : value / denominator ≤ value := by
  apply (Fraction.Order.Field.div_le_iff_pos ((by decide : (0 : Fraction.Rational) < 1).trans_le atLeastOne)).mpr
  simpa only [Fraction.Field.mul_one_direct] using
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct atLeastOne nonnegative
end Purelib.Data.Rat.Fraction.Order.Field

end

section
public section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace Purelib.Data.Rat.Fraction.Order.Field

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- Positive-denominator rational quotients are weakly ordered when their cross-products are. -/
public theorem div_le_div_of_cross
    {leftNumerator rightNumerator leftDenominator rightDenominator :
      Fraction.Rational}
    (leftDenominatorPositive : 0 < leftDenominator)
    (rightDenominatorPositive : 0 < rightDenominator)
    (cross : leftNumerator * rightDenominator ≤
      rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator ≤
      rightNumerator / rightDenominator := by
  apply (Fraction.Order.Field.le_div_iff_pos
    rightDenominatorPositive).2
  have quotientIdentity :
      (leftNumerator / leftDenominator) * rightDenominator =
        (leftNumerator * rightDenominator) / leftDenominator := by
    simp only [_root_.Purelib.Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      (leftNumerator * leftDenominator⁻¹) * rightDenominator =
          leftNumerator * (leftDenominator⁻¹ * rightDenominator) :=
        _root_.mul_assoc _ _ _
      _ = leftNumerator * (rightDenominator * leftDenominator⁻¹) :=
        congrArg (fun value => leftNumerator * value)
          (_root_.mul_comm _ _)
      _ = (leftNumerator * rightDenominator) * leftDenominator⁻¹ :=
        (_root_.mul_assoc _ _ _).symm
  rw [quotientIdentity]
  exact (Fraction.Order.Field.div_le_iff_pos
    leftDenominatorPositive).2 cross

end Purelib.Data.Rat.Fraction.Order.Field

end

section
public section

/-!
# Riemann compatibility facade for finite quotient variation

The constructive Gaussian-rational estimates now live in the arithmetic core,
where progressive division can use them without importing the Riemann layer.
These declarations preserve the established Riemann names for downstream
modules without duplicating their proof bodies.
-/

namespace Purelib.Data.Rat.Fraction.Order.Field

open Purelib.Data.Rat in
/-- A fixed nonnegative numerator divided by a squared positive denominator decreases when that denominator increases.
-/
theorem scaled_div_square_antitone
    {numerator lower higher : Fraction.Rational}
    (numeratorNonnegative : 0 <= numerator)
    (lowerPositive : 0 < lower) (order : lower <= higher) :
    numerator / (higher * higher) <= numerator / (lower * lower) := by
  have squareOrder : lower * lower <= higher * higher := by
    simpa only [pow_two] using
      (Fraction.Order.Arithmetic.pow_le_pow_direct lowerPositive.le order 2)
  exact Fraction.Order.Field.div_le_div_of_nonneg_left_direct
    numeratorNonnegative
    (Fraction.Order.Arithmetic.mul_pos_direct lowerPositive lowerPositive)
    squareOrder
end Purelib.Data.Rat.Fraction.Order.Field

end

end

section
public section

namespace Purelib.Data.Rat.Fraction.Order.Field

open Purelib.Data.Rat in
/-- Half of a positive rational is strictly smaller than that rational. -/
theorem half_lt_self
    {epsilon : Fraction.Rational} (positive : 0 < epsilon) :
    epsilon / 2 < epsilon := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  calc
    epsilon = epsilon * 1 := by ring1
    _ < epsilon * 2 :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        positive (by decide)

end Purelib.Data.Rat.Fraction.Order.Field

end

namespace Purelib.Data.Rat.Fraction.Order.Field

open Purelib.Data.Rat

/-- A point between ordered rational endpoints has normalized coordinate in the unit interval.

The positive endpoint difference certifies division of the retained nonnegative
point difference. The upper endpoint bound puts that quotient at most one. -/
public theorem fraction_inside {lower upper point : Fraction.Rational}
    (ordered : lower < upper) (inside : lower ≤ point ∧ point ≤ upper) :
    0 ≤ (point - lower) / (upper - lower) ∧
      (point - lower) / (upper - lower) ≤ 1 := by
  have positive := Fraction.Order.Arithmetic.sub_pos_direct ordered
  refine ⟨div_nonneg_direct (Fraction.Order.Arithmetic.sub_nonneg_direct inside.1) positive.le, ?_⟩
  apply (div_le_iff_pos positive).mpr
  exact (Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2 lower).trans_eq (by ring1)

end Purelib.Data.Rat.Fraction.Order.Field

public section

namespace Purelib.Data.Rat.Fraction.Order.Field

open Purelib.Data.Rat
/-- Multiplying a nonnegative cost by its capped inverse allocation pays a positive target.

The positive cost increment gives strict growth at the retained minimum. Its
second branch then cancels the same nonzero denominator to recover the target. -/
public theorem mul_min_one_div_lt {cost target : Fraction.Rational} (nonnegative : 0 ≤ cost) (positive : 0 < target) :
    cost * min 1 (target / (cost + 1)) < target := by
  have denominator : 0 < cost + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by decide)
  have tolerancePositive : 0 < min 1 (target / (cost + 1)) :=
    Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Field.div_pos_direct positive denominator)
  have strict : cost * min 1 (target / (cost + 1)) < (cost + 1) * min 1 (target / (cost + 1)) :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (by
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1) cost
        simpa only [add_zero, -eq_self, -iff_self] using translated) tolerancePositive
  apply strict.trans_le
  have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Basic.min_le_right (1 : Fraction.Rational) (target / (cost + 1))) denominator.le
  exact bounded.trans_eq ((Fraction.Field.mul_comm _ _).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ denominator.ne'))

/-- Transport the cleared natural square inequality to a rational lower-square bound with positive denominators.

The retained positive denominators permit scalar multiplication of the bound. The original natural cross-product
inequality then compares the displayed rational square and quotient. -/
public theorem nat_square_div_le_div
    {root numerator rootDenominator valueDenominator : Nat}
    (rootDenominatorPositive : 0 < rootDenominator)
    (valueDenominatorPositive : 0 < valueDenominator)
    (cleared : root ^ 2 * valueDenominator ≤
      numerator * rootDenominator ^ 2) :
    ((root : Fraction.Rational) / (rootDenominator : Fraction.Rational)) ^ 2 ≤
      (numerator : Fraction.Rational) / (valueDenominator : Fraction.Rational) := by
  have rootDenominatorCastPositive :=
    Fraction.Cast.Order.natCast_pos_direct rootDenominatorPositive
  have valueDenominatorCastPositive :=
    Fraction.Cast.Order.natCast_pos_direct valueDenominatorPositive
  rw [show ((root : Fraction.Rational) / (rootDenominator : Fraction.Rational)) ^ 2 =
      (root : Fraction.Rational) ^ 2 / (rootDenominator : Fraction.Rational) ^ 2 by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    rw [Fraction.Field.inv_pow_direct]
    ring1]
  apply (Fraction.Order.Field.div_le_iff_pos
    (Fraction.Order.Arithmetic.pow_pos_direct
      rootDenominatorCastPositive 2)).2
  rw [show ((numerator : Fraction.Rational) / (valueDenominator : Fraction.Rational)) *
      (rootDenominator : Fraction.Rational) ^ 2 =
      ((numerator : Fraction.Rational) * (rootDenominator : Fraction.Rational) ^ 2) /
        (valueDenominator : Fraction.Rational) by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1]
  apply (Fraction.Order.Field.le_div_iff_pos
    valueDenominatorCastPositive).2
  have castCleared := Fraction.Cast.Order.natCast_le_direct cleared
  simpa only [Purelib.Algebra.NatCast.mul, Purelib.Algebra.NatCast.pow, -eq_self, -iff_self] using castCleared

/-- Transport the cleared strict natural square inequality to a rational upper-square bound with positive denominators.

The retained positive denominators permit scalar multiplication of the strict bound. The original natural cross-product
inequality then compares the quotient with the displayed rational square. -/
public theorem nat_div_lt_square_div
    {numerator upper rootDenominator valueDenominator : Nat}
    (rootDenominatorPositive : 0 < rootDenominator)
    (valueDenominatorPositive : 0 < valueDenominator)
    (cleared : numerator * rootDenominator ^ 2 <
      upper ^ 2 * valueDenominator) :
    (numerator : Fraction.Rational) / (valueDenominator : Fraction.Rational) <
      ((upper : Fraction.Rational) / (rootDenominator : Fraction.Rational)) ^ 2 := by
  have rootDenominatorCastPositive :=
    Fraction.Cast.Order.natCast_pos_direct rootDenominatorPositive
  have valueDenominatorCastPositive :=
    Fraction.Cast.Order.natCast_pos_direct valueDenominatorPositive
  rw [show ((upper : Fraction.Rational) / (rootDenominator : Fraction.Rational)) ^ 2 =
      (upper : Fraction.Rational) ^ 2 / (rootDenominator : Fraction.Rational) ^ 2 by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    rw [Fraction.Field.inv_pow_direct]
    ring1]
  apply (Fraction.Order.Field.lt_div_iff_pos
    (Fraction.Order.Arithmetic.pow_pos_direct
      rootDenominatorCastPositive 2)).2
  rw [show ((numerator : Fraction.Rational) / (valueDenominator : Fraction.Rational)) *
      (rootDenominator : Fraction.Rational) ^ 2 =
      ((numerator : Fraction.Rational) * (rootDenominator : Fraction.Rational) ^ 2) /
        (valueDenominator : Fraction.Rational) by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1]
  apply (Fraction.Order.Field.div_lt_iff_pos
    valueDenominatorCastPositive).2
  have castCleared := Fraction.Cast.Order.natCast_lt_direct cleared
  simpa only [Purelib.Algebra.NatCast.mul, Purelib.Algebra.NatCast.pow, -eq_self, -iff_self] using castCleared

end Purelib.Data.Rat.Fraction.Order.Field

end
