module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Order
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

import Mathlib.Algebra.Ring.MinimalAxioms

import Purelib.Tactic.Ring

open Purelib.Data.Rat

open scoped Purelib.Data.Nat

section
@[expose] public section

/-!
# Constructive finite CCF contraction certificate

This file isolates the finite integer and half-open-square estimates used by
the three-step coordinate-floor CCF contraction theorem.  The exceptional
digit set is an eight-constructor type; no unbounded search or ambient
quantifier-elimination principle is involved.
-/

namespace Purelib.Data.Rat.Fraction.Order.Square

/-- Adding a nonnegative increment to a nonnegative rational cannot decrease its square. -/
public theorem square_le_square_add_of_nonnegative
    (base increment : Fraction.Rational) (baseNonnegative : 0 ≤ base)
    (incrementNonnegative : 0 ≤ increment) :
    base ^ 2 ≤ (base + increment) ^ 2 := by
  have twiceBaseNonnegative : 0 ≤ base + base :=
    add_nonneg baseNonnegative baseNonnegative
  have secondFactorNonnegative : 0 ≤ base + base + increment :=
    add_nonneg twiceBaseNonnegative incrementNonnegative
  have productNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    incrementNonnegative secondFactorNonnegative
  calc
    base ^ 2 ≤ base ^ 2 + increment * (base + base + increment) :=
      le_add_of_nonneg_right productNonnegative
    _ = (base + increment) ^ 2 := by ring1

/-- On a nonpositive translated interval, replacing the unit increment by a smaller increment cannot decrease the
square. -/
public theorem negative_square_growth
    (base increment : Fraction.Rational) (incrementAtMostOne : increment ≤ 1)
    (basePlusOneNonpositive : base + 1 ≤ 0) :
    (base + 1) ^ 2 ≤ (base + increment) ^ 2 := by
  have shiftedOrder : base + increment ≤ base + 1 := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      incrementAtMostOne base
    calc
      base + increment = increment + base := _root_.add_comm _ _
      _ ≤ 1 + base := shifted
      _ = base + 1 := _root_.add_comm _ _
  have firstNonnegative :=
    Fraction.Order.Arithmetic.sub_nonneg_direct shiftedOrder
  have sumNonpositive : (base + 1) + (base + increment) ≤ 0 :=
    calc
      (base + 1) + (base + increment) ≤ 0 + 0 :=
        add_le_add basePlusOneNonpositive
          (shiftedOrder.trans basePlusOneNonpositive)
      _ = 0 := add_zero 0
  have secondNonnegative :
      0 ≤ -((base + 1) + (base + increment)) := by
    have difference := Fraction.Order.Arithmetic.sub_nonneg_direct
      sumNonpositive
    rw [show (0 : Fraction.Rational) -
        ((base + 1) + (base + increment)) =
          -((base + 1) + (base + increment)) by ring1] at difference
    exact difference
  have productNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    firstNonnegative secondNonnegative
  calc
    (base + 1) ^ 2 ≤ (base + 1) ^ 2 +
        ((base + 1) - (base + increment)) *
          (-((base + 1) + (base + increment))) :=
      le_add_of_nonneg_right productNonnegative
    _ = (base + increment) ^ 2 := by ring1

end Purelib.Data.Rat.Fraction.Order.Square

end

section
@[expose] public section

/-!
# Constructive coordinate-floor complex continued fractions

The coordinate-floor return map and its digit cone, stated entirely in the
explicit finite rational and Gaussian representations used by CCL-1.
-/

namespace Purelib.Data.Rat.Fraction.Order.Square

/-- A canonical rational in the half-open interval from zero to one has square strictly below one. -/
public theorem square_lt_one_of_unit {x : Fraction.Rational}
    (nonnegative : 0 ≤ x) (small : x < 1) : x ^ 2 < 1 := by
  by_cases zero : x = 0
  · subst x
    decide
  · have positive : 0 < x := lt_of_le_of_ne nonnegative (Ne.symm zero)
    have first := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      positive small
    calc
      x ^ 2 = x * x := pow_two x
      _ < x * 1 := first
      _ = x := by ring1
      _ < 1 := small

end Purelib.Data.Rat.Fraction.Order.Square

end

section
@[expose] public section

/-!
# Persistent CCL events after exact box-condition splitting

Every original squarefree curve factor has been split by executable gcd
against all four cleared box-edge polynomials.  This module runs the aligned
Sturm-event construction on each final profile factor and exposes the same
finite residual estimate used by the unsplit event layer.

Each profile already records, for every edge, either exact equality ownership
or explicit Bezout coprimality.  The next owner layer can therefore stabilize
the signs of only the genuinely apart edges.
-/

namespace Purelib.CCL.Persistent.ConditionProfiles
namespace ProfileEventLeaf

end ProfileEventLeaf
end Purelib.CCL.Persistent.ConditionProfiles

end

section
@[expose] public section

/-!
# Persistent projective shrinking of nonzero CCL curve events

Every nonconstant curve analysis has already been split into squarefree
coordinate factors and an aligned finite partition.  This module extracts the
nonzero-count leaves as explicit finite event records.  Each record carries
the existing central-third Sturm transducer and, simultaneously, a homogeneous
projective image bound for its rational boundary chart.

The homogeneous estimate remains valid across an affine pole.  It is therefore
combined with each chart's positive homogeneous-weight lower bound to obtain
the genuine finite `chi^2` shrinking fact needed to couple a narrowing
parameter event to a narrowing winding box without choosing a completed
parameter or root.
-/

namespace Purelib.CCL.Persistent.CurveEvents
namespace EventLeaf

end EventLeaf

end Purelib.CCL.Persistent.CurveEvents

end

section
@[expose] public section

/-!
# Canonical Gaussian rationals

Gaussian values are structural pairs of quotient-free canonical rationals.
All operations remain finite component calculations.  In particular, the
proof that the norm denominator is nonzero inspects the signs of the stored
rational numerators; it does not embed the pair in a completed complex field.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib.Data

/-- Weak positivity is exactly weak positivity of the stored numerator. -/
theorem Order.Square.zero_le_iff_num_nonneg (source : Rational) :
    0 ≤ source ↔ 0 ≤ source.num := by
  constructor
  · intro nonnegative
    change (0 : Int) * (source.den : Int) ≤ source.num * 1 at nonnegative
    rw [Int.Arithmetic.zero_mul, Int.Arithmetic.mul_one]
      at nonnegative
    exact nonnegative
  · intro nonnegative
    change (0 : Int) * (source.den : Int) ≤ source.num * 1
    rw [Int.Arithmetic.zero_mul, Int.Arithmetic.mul_one]
    exact nonnegative

/-- A finite rational square is nonnegative in the concrete cross order.

Zero has a zero square. Otherwise the nonzero integer numerator has a positive
square, and the positive-denominator product display preserves that sign. -/
theorem Order.Square.mul_self_nonneg (source : Rational) : 0 ≤ source * source := by
  apply (Order.Square.zero_le_iff_num_nonneg (source * source)).mpr
  by_cases sourceZero : source = 0
  · rw [sourceZero, zero_mul]
    exact Int.Order.le_refl 0
  · have numeratorNonzero : source.num ≠ 0 := fun numeratorZero =>
      sourceZero ((eq_zero_iff_num_zero source).mpr numeratorZero)
    have rawPositive : 0 < (referenceMulRaw source source).num := by
      change 0 < source.num * source.num
      exact Int.Order.mul_self_pos numeratorNonzero
    exact Int.Order.le_of_lt
      ((Order.Basic.numerator_pos_iff_of_equivalent (mul_equivalent source source)).mpr
        rawPositive)

/-- A finite rational square is zero exactly when its factor is zero. -/
theorem Order.Square.mul_self_eq_zero (source : Rational) :
    source * source = 0 ↔ source = 0 := by
  constructor
  · intro squareZero
    by_cases sourceZero : source = 0
    · exact sourceZero
    · exact (mul_ne_zero sourceZero sourceZero squareZero).elim
  · intro sourceZero
    rw [sourceZero, zero_mul]

end Purelib.Data.Rat.Fraction

end

end

public section

namespace Purelib.Data.Rat.Fraction.Order.Square

open Purelib.Data
open Purelib.Data.Rat

/-- A rational value whose square is below one lies strictly above minus one.

The weak squared-norm bound gives the negative unit lower endpoint. Equality at that endpoint contradicts the retained
strict square bound. -/
public theorem neg_one_lt_of_square_lt_one {value : Fraction.Rational}
    (small : value ^ 2 < 1) : -1 < value := by
  have lower : (-1 : Fraction.Rational) ≤ value :=
    Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct
      (show (0 : Fraction.Rational) ≤ 1 by decide) small.le
  refine ⟨lower, ?_⟩
  intro reverse
  have equal : value = -1 := le_antisymm reverse lower
  rw [equal] at small
  exact (not_lt_of_ge (show (1 : Fraction.Rational) ≤ 1 by decide) small)

/-- Squaring preserves a strict rational inequality when its lower endpoint is nonnegative.

The lower endpoint is nonnegative and the upper endpoint is positive. Weak and strict multiplication transport the
original two inputs without changing their squares. -/
public theorem square_lt_square_of_nonneg_of_lt
    {left right : Fraction.Rational} (leftNonnegative : 0 ≤ left)
    (strict : left < right) : left ^ 2 < right ^ 2 := by
  have rightPositive : 0 < right := leftNonnegative.trans_lt strict
  have first : left * left ≤ left * right :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      strict.le leftNonnegative
  have second : left * right < right * right :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      strict rightPositive
  simpa only [pow_two] using first.trans_lt second

end Purelib.Data.Rat.Fraction.Order.Square
