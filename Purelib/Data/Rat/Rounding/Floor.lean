module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Order
import Purelib.Data.Int.Division
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Group.Negation
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Euclidean floor and ceiling of canonical rational displays

The original signed numerator and positive denominator determine the same
integer Euclidean quotient. Ceiling negates that original floor after rational
negation; natural ceiling retains the same integer-to-natural readback.
-/

open Purelib.Data.Rat
open Purelib.Data.Int
open Purelib.Algebra.Ring

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

namespace Purelib.Data.Rat.Rounding.Floor

/-- Compute the Euclidean integer floor of the retained canonical fraction.

Divide its signed numerator by its strictly positive denominator using integer
Euclidean division. The same original quotient is the lower integer endpoint
for both positive and negative inputs. -/
@[expose] public def floor (source : Fraction.Rational) : Int :=
  source.num / (source.den : Int)

/-- An integer cast lies below a rational exactly when it lies below its floor.

The original positive denominator transports the retained integer cross-product
comparison to the same Euclidean quotient. Direct quotient monotonicity and
reconstruction establish both directions without changing the quotient. -/
public theorem intCast_le_iff_floor (integer : Int) (source : Fraction.Rational) :
    (integer : Fraction.Rational) ≤ source ↔ integer ≤ floor source := by
  rw [Fraction.Cast.intCast_eq_fromInt]
  change integer * (source.den : Int) ≤ source.num * 1 ↔
    integer ≤ source.num / (source.den : Int)
  rewrite [Arithmetic.mul_one]
  have denominatorPositive : 0 < (source.den : Int) :=
    Order.natCast_pos source.den_pos
  have denominatorNonzero : (source.den : Int) ≠ 0 :=
    fun zero => Order.lt_irrefl 0 (zero ▸ denominatorPositive)
  constructor
  · intro comparison
    have quotients := Division.ediv_le_ediv_right comparison source.den_pos
    have reconstructed :
        (integer * (source.den : Int)) / (source.den : Int) = integer := by
      rw [Arithmetic.mul_comm]
      exact Division.mul_ediv_cancel_left integer denominatorNonzero
    rewrite [reconstructed] at quotients
    exact quotients
  · intro comparison
    have scaled := Order.mul_le_mul_of_nonneg_right comparison
      (Order.le_of_lt denominatorPositive)
    have reconstructed :
        (source.num / (source.den : Int)) * (source.den : Int) ≤ source.num := by
      rw [Arithmetic.mul_comm]
      exact Division.mul_ediv_self_le source.num source.den_pos
    exact Order.le_trans scaled reconstructed

/-- Compute the ceiling as the negative floor of the negated canonical rational.

The original rational negation retains its denominator. Negating its original
integer floor reverses the same endpoint bounds and returns the least integer
upper bound without a second quotient procedure. -/
@[expose] public def ceil (source : Fraction.Rational) : Int := -floor (-source)

/-- The computed ceiling lies below an integer exactly when its cast bounds the rational.

Negating both integer endpoints reverses their direct weak order. The original
floor characterization on the same negated rational then transports the bound
through the retained integer cast and rational negation. -/
public theorem ceil_le_intCast_iff (source : Fraction.Rational) (integer : Int) :
    ceil source ≤ integer ↔ source ≤ (integer : Fraction.Rational) := by
  have castNegative : ((-integer : Int) : Fraction.Rational) =
      -(integer : Fraction.Rational) := IntCast.neg integer
  rw [ceil]
  constructor
  · intro lessEqual
    have negativeInteger := Order.neg_le_neg lessEqual
    rewrite [Int.neg_neg] at negativeInteger
    have castComparison :=
      (intCast_le_iff_floor (-integer) (-source)).mpr negativeInteger
    rewrite [castNegative] at castComparison
    exact (Fraction.Order.Arithmetic.neg_le_neg_iff_direct
      (integer : Fraction.Rational) source).mp castComparison
  · intro lessEqual
    have negativeComparison : ((-integer : Int) : Fraction.Rational) ≤ -source := by
      rw [castNegative]
      exact (Fraction.Order.Arithmetic.neg_le_neg_iff_direct
        (integer : Fraction.Rational) source).mpr lessEqual
    have floorComparison :=
      (intCast_le_iff_floor (-integer) (-source)).mp negativeComparison
    have reversed := Order.neg_le_neg floorComparison
    rewrite [Int.neg_neg] at reversed
    exact reversed

/-- Every canonical rational lies below the cast of its computed ceiling.

Reflexivity bounds the same original integer ceiling by itself. Its direct
characterization therefore certifies the original rational upper endpoint. -/
public theorem le_intCast_ceil (source : Fraction.Rational) :
    source ≤ (ceil source : Fraction.Rational) :=
  (ceil_le_intCast_iff source (ceil source)).mp (Order.le_refl _)

/-- Read the computed integer ceiling as a natural number.

The original integer-to-natural conversion retains nonnegative ceilings
and truncates negative ceilings to zero. No different rational quotient
or integer endpoint is computed. -/
@[expose] public def ceilNat (source : Fraction.Rational) : Nat := (ceil source).toNat

/-- A nonnegative rational lies below the cast of its computed natural ceiling.

Its original integer ceiling is nonnegative because its cast bounds the same
nonnegative rational. Structural sign readback preserves that retained integer
as its natural value, so its already established upper bound remains exact. -/
public theorem le_natCast_ceilNat_of_nonneg {source : Fraction.Rational}
    (nonnegative : 0 ≤ source) : source ≤ (ceilNat source : Nat) := by
  have castNonnegative : (0 : Fraction.Rational) ≤ (ceil source : Fraction.Rational) :=
    Fraction.Order.Basic.le_trans _ _ _ nonnegative (le_intCast_ceil source)
  have ceilingNonnegative : (0 : Int) ≤ ceil source :=
    (Fraction.Cast.Order.intCast_le_intCast_iff_direct 0 (ceil source)).mp (by
      change (0 : Fraction.Rational) ≤ (ceil source : Fraction.Rational)
      exact castNonnegative)
  have ceilingCast : ((ceil source).toNat : Int) = ceil source := by
    cases ceiling : ceil source with
    | ofNat value => rfl
    | negSucc value =>
        rw [ceiling] at ceilingNonnegative
        cases ceilingNonnegative
  calc
    source ≤ (ceil source : Fraction.Rational) := le_intCast_ceil source
    _ = (((ceil source).toNat : Int) : Fraction.Rational) :=
      (congrArg (fun value : Int => (value : Fraction.Rational)) ceilingCast).symm
    _ = (((ceil source).toNat : Nat) : Fraction.Rational) := by rw [Int.cast_natCast]
    _ = (ceilNat source : Nat) := rfl

/-- The cast of the computed Euclidean floor lies below the original rational.

The direct floor characterization applies to the same retained quotient.
Its original integer reflexivity certificate establishes the lower endpoint. -/
public theorem intCast_floor_le (source : Fraction.Rational) :
    ((floor source : Int) : Fraction.Rational) ≤ source :=
  (intCast_le_iff_floor _ _).mpr (Order.le_refl _)

/-- Every canonical rational lies strictly below the integer above its floor.

The original floor characterization excludes the reversed upper-endpoint bound:
that would place a successor integer below its own predecessor. The retained
rational total cross order supplies the forward weak bound directly. -/
public theorem lt_intCast_floor_add_one (source : Fraction.Rational) :
    source < ((floor source + 1 : Int) : Fraction.Rational) := by
  have reverseExcluded : ¬((floor source + 1 : Int) : Fraction.Rational) ≤ source := by
    intro reverse
    have impossible := (intCast_le_iff_floor (floor source + 1) source).mp reverse
    have successorGreater : floor source < floor source + 1 :=
      Order.lt_intro (difference := 0) rfl
    exact (Order.lt_iff_le_and_not_ge.mp successorGreater).2 impossible
  change source ≤ ((floor source + 1 : Int) : Fraction.Rational) ∧
    ¬((floor source + 1 : Int) : Fraction.Rational) ≤ source
  cases Fraction.Order.Basic.le_total source
      ((floor source + 1 : Int) : Fraction.Rational) with
  | inl forward => exact ⟨forward, reverseExcluded⟩
  | inr reverse => exact (reverseExcluded reverse).elim

end Purelib.Data.Rat.Rounding.Floor
