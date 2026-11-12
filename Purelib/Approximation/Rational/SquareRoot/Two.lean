module

public import Purelib.Approximation.Rational.SquareRootBracket
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Finite brackets for the positive square root of two

The dyadic stage chooses the existing integer-floor bracket at denominator
`2 ^ stage`. Its retained endpoints enclose the positive square root by their
sign and square certificates.
-/

namespace Purelib.Approximation.Rational.SquareRoot.Two

open Purelib.Approximation.Rational.SquareRootBracket.KernelApproximation
open Purelib.Data.Rat
open Purelib.NumberTheory.SquareClass.Rational.Basic
open Purelib.Data.Rat.Fraction.Order

/-- The positive rational target two, retaining its original square-class representative. -/
@[expose] public def target : TheoremSixtyTwo.PositiveSquareClassRepresentative where
  representative := ⟨2, by decide⟩
  positive := by decide

/-- The original finite square-root bracket at dyadic denominator `2 ^ stage`. -/
@[expose] public def bracket (stage : Nat) : SqrtBracket target (2 ^ stage - 1) :=
  sqrtBracket target (2 ^ stage - 1)

/-- The bracket's retained denominator is exactly the requested power of two. -/
public theorem denominator_eq (stage : Nat) : (bracket stage).denominator = 2 ^ stage := by
  rw [(bracket stage).denominator_eq]
  have positive : 0 < 2 ^ stage := Nat.pow_pos (by decide)
  change 1 * (2 ^ stage - 1 + 1) = 2 ^ stage
  omega0

/-- The retained integer radicand is two times the squared dyadic denominator. -/
public theorem radicand_eq (stage : Nat) :
    (bracket stage).radicand = 2 * (2 ^ stage) ^ 2 := by
  rw [(bracket stage).radicand_eq]
  have cells : 2 ^ stage - 1 + 1 = 2 ^ stage :=
    Nat.sub_add_cancel (Nat.pow_pos (by decide))
  change 2 * 1 * (2 ^ stage - 1 + 1) ^ 2 = _
  rw [cells]

/-- The lower numerator is the original integer square-root floor of the dyadic radicand. -/
public theorem lowerNumerator_eq (stage : Nat) :
    (bracket stage).lowerNumerator =
      Purelib.Data.Nat.SquareRoot.floor (2 * (2 ^ stage) ^ 2) := by
  rw [(bracket stage).lowerNumerator_eq, radicand_eq]

/-- The lower endpoint is nonnegative and its square does not exceed two. -/
public theorem lower_spec (stage : Nat) :
    0 ≤ (bracket stage).lower ∧ (bracket stage).lower ^ 2 ≤ 2 :=
  ⟨(bracket stage).lower_nonnegative, (bracket stage).lower_square_le⟩

/-- The upper endpoint is positive and its square strictly exceeds two. -/
public theorem upper_spec (stage : Nat) :
    0 < (bracket stage).upper ∧ 2 < (bracket stage).upper ^ 2 :=
  ⟨(bracket stage).upper_positive, (bracket stage).value_lt_upper_square⟩

/-- The two retained endpoints differ by the reciprocal dyadic denominator. -/
public theorem width_eq (stage : Nat) :
    (bracket stage).upper - (bracket stage).lower =
      1 / (2 ^ stage : Nat) := by
  rw [(bracket stage).width_eq, denominator_eq]

/-- Any lower endpoint lies below every upper endpoint.

Both endpoints have the positive-root signs, and their squares lie on
opposite sides of the same target. No nested-floor assumption is needed. -/
public theorem lower_le_upper (left right : Nat) :
    (bracket left).lower ≤ (bracket right).upper := by
  apply Arithmetic.le_of_sq_le_sq_direct (upper_spec right).1.le
  exact (lower_spec left).2.trans (upper_spec right).2.le

/-- The dyadic bracket widths decrease with the stage. -/
public theorem width_antitone {earlier later : Nat} (ordered : earlier ≤ later) :
    (1 : Fraction.Rational) / (2 ^ later : Nat) ≤ 1 / (2 ^ earlier : Nat) := by
  have powers : 2 ^ earlier ≤ 2 ^ later := Nat.pow_le_pow_right (by decide) ordered
  have castPowers := Fraction.Cast.Order.natCast_le_direct powers
  have positive : (0 : Fraction.Rational) < (2 ^ earlier : Nat) :=
    Fraction.Cast.Order.natCast_pos_direct (Nat.pow_pos (by decide))
  exact Field.div_le_div_of_nonneg_left_direct (by decide) positive castPowers

/-- The upper endpoints of two stages are within the earlier dyadic width.

The two cross-bracket comparisons bound each directed difference. The later
width is no greater than the earlier width. -/
public theorem upper_abs_difference_le {earlier later : Nat} (ordered : earlier ≤ later) :
    Fraction.abs ((bracket later).upper - (bracket earlier).upper) ≤
      1 / (2 ^ earlier : Nat) := by
  have forward : (bracket later).upper - (bracket earlier).upper ≤
      1 / (2 ^ earlier : Nat) := by
    calc
      (bracket later).upper - (bracket earlier).upper ≤
          (bracket later).upper - (bracket later).lower :=
        Arithmetic.sub_le_sub_left_direct (lower_le_upper later earlier) _
      _ = 1 / (2 ^ later : Nat) := width_eq later
      _ ≤ 1 / (2 ^ earlier : Nat) := width_antitone ordered
  have reverse : (bracket earlier).upper - (bracket later).upper ≤
      1 / (2 ^ earlier : Nat) := by
    calc
      (bracket earlier).upper - (bracket later).upper ≤
          (bracket earlier).upper - (bracket earlier).lower :=
        Arithmetic.sub_le_sub_left_direct (lower_le_upper earlier later) _
      _ = 1 / (2 ^ earlier : Nat) := width_eq earlier
  change max ((bracket later).upper - (bracket earlier).upper)
    (-((bracket later).upper - (bracket earlier).upper)) ≤ _
  apply Basic.max_le forward
  have opposite : -((bracket later).upper - (bracket earlier).upper) =
      (bracket earlier).upper - (bracket later).upper := by ring1
  rw [opposite]
  exact reverse

/-- The square of the dyadic width is the quarter-radius at that stage. -/
public theorem width_sq (stage : Nat) :
    (1 / ((2 ^ stage : Nat) : Fraction.Rational)) ^ 2 =
      Geometric.Basic.quarterRadius 1 stage := by
  have castPower : ((2 ^ stage : Nat) : Fraction.Rational) = (2 : Fraction.Rational) ^ stage :=
    Purelib.Algebra.NatCast.pow 2 stage
  have powerSquare : ((2 : Fraction.Rational) ^ stage) ^ 2 = (4 : Fraction.Rational) ^ stage := by
    calc
      ((2 : Fraction.Rational) ^ stage) ^ 2 =
          (2 : Fraction.Rational) ^ stage * (2 : Fraction.Rational) ^ stage := by ring1
      _ = ((2 : Fraction.Rational) * 2) ^ stage :=
        (Purelib.Algebra.Semiring.Normalization.product_pow 2 2 stage).symm
      _ = (4 : Fraction.Rational) ^ stage :=
        congrArg (fun value : Fraction.Rational => value ^ stage) (by decide)
  rw [castPower, Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.mul_pow_direct,
    ← Fraction.Field.inv_pow_direct, powerSquare]
  change Geometric.Basic.quarterRadius 1 stage = _
  rfl

/-- Every upper endpoint lies between one and three.

The square bounds place the lower endpoint below two and the upper endpoint
above one; the exact dyadic width is at most one. -/
public theorem upper_bounds (stage : Nat) :
    1 ≤ (bracket stage).upper ∧ (bracket stage).upper ≤ 3 := by
  have lowerLeTwo : (bracket stage).lower ≤ 2 := by
    apply Arithmetic.le_of_sq_le_sq_direct (by decide)
    exact (lower_spec stage).2.trans (by decide)
  have oneLeUpper : (1 : Fraction.Rational) ≤ (bracket stage).upper := by
    apply Arithmetic.le_of_sq_le_sq_direct (upper_spec stage).1.le
    exact (show (1 : Fraction.Rational) ^ 2 ≤ 2 by decide).trans (upper_spec stage).2.le
  have widthLeOne : (bracket stage).upper - (bracket stage).lower ≤ 1 := by
    rw [width_eq]
    have atLeast : (1 : Fraction.Rational) ≤ (2 ^ stage : Nat) :=
      Fraction.Cast.Order.natCast_le_direct (Nat.pow_pos (by decide))
    calc
      (1 : Fraction.Rational) / (2 ^ stage : Nat) ≤ 1 / (1 : Fraction.Rational) :=
        Field.div_le_div_of_nonneg_left_direct (by decide) (by decide) atLeast
      _ = 1 := by decide
  have combined := Arithmetic.add_le_add_direct lowerLeTwo widthLeOne
  constructor
  · exact oneLeUpper
  · calc
      (bracket stage).upper = (bracket stage).lower +
          ((bracket stage).upper - (bracket stage).lower) := by ring1
      _ ≤ 2 + 1 := combined
      _ = 3 := by decide

/-- The upper endpoint's square exceeds two by at most seven dyadic widths. -/
public theorem upper_square_error_le (stage : Nat) :
    (bracket stage).upper ^ 2 - 2 ≤ 7 / (2 ^ stage : Nat) := by
  have bound := sqrtBracket_square_error_le target (2 ^ stage - 1) (bracket stage)
  have cells : 2 ^ stage - 1 + 1 = 2 ^ stage :=
    Nat.sub_add_cancel (Nat.pow_pos (by decide))
  change (bracket stage).upper ^ 2 - 2 ≤
    (2 * (2 : Fraction.Rational) + 3) / (2 ^ stage - 1 + 1 : Nat) at bound
  rw [cells] at bound
  exact bound

end Purelib.Approximation.Rational.SquareRoot.Two
