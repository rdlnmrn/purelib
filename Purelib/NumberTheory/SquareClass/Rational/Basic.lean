module

import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Data.Int.ToNat
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

/-!
# Positive canonical rational square-class representatives

The representative retains its exact positive canonical fraction. Its
natural numerator and denominator read those same stored coordinates;
their displayed quotient reconstructs the retained original value.
-/

namespace Purelib.NumberTheory.SquareClass.Rational.Basic.TheoremSixtyTwo

@[expose] public section

set_option genInjectivity false in
/-- Retain a nonzero canonical rational square-class value with strict positivity.

The original square-class representative is the nominal parent. Positivity
certifies that same retained value without selecting another representative. -/
structure PositiveSquareClassRepresentative where
  /-- The retained nonzero rational square-class representative. -/ representative :
    Algebra.Field.SquareClass.Basic.SquareClassRepresentative Fraction.Rational
  /-- The retained representative value is strictly positive. -/ positive : 0 < representative.value

constructive_injectivity PositiveSquareClassRepresentative

end

namespace PositiveSquareClassRepresentative

/-- Read the natural numerator from the original positive canonical rational.

The retained signed numerator is converted directly to its natural value;
the strict positivity certificate establishes its unchanged positive reading. -/
@[expose] public def numerator (target : PositiveSquareClassRepresentative) : Nat :=
  target.representative.value.num.toNat

/-- Read the original positive natural denominator of the canonical rational.

This projection retains the denominator stored by the original fraction;
no reduction or alternative quotient presentation is computed. -/
@[expose] public def denominator (target : PositiveSquareClassRepresentative) : Nat :=
  target.representative.value.den

/-- The retained natural numerator of a positive canonical rational is positive.

Its sign follows from the exact signed numerator criterion for the original
fraction. Direct integer-to-natural readback preserves that positivity. -/
public theorem numerator_positive (target : PositiveSquareClassRepresentative) :
    0 < target.numerator := by
  apply Data.Int.ToNat.toNat_pos_direct
  exact
    (Fraction.Order.Basic.zero_lt_iff_num_pos
      target.representative.value).mp target.positive

/-- The retained canonical denominator is positive.

The original fraction's denominator-positivity certificate applies directly
to its unchanged natural denominator projection. -/
public theorem denominator_positive (target : PositiveSquareClassRepresentative) :
    0 < target.denominator :=
  target.representative.value.den_pos

/-- The retained positive denominator has nonzero canonical rational cast.

Injectivity of the natural cast would send a zero cast to a zero natural
denominator, contradicting the original positivity certificate. -/
public theorem denominator_cast_ne_zero
    (target : PositiveSquareClassRepresentative) :
    (target.denominator : Fraction.Rational) ≠ 0 := by
  intro castZero
  have naturalZero : target.denominator = 0 :=
    Fraction.Cast.Compatibility.natCast_injective_direct (by
      simpa only [Nat.cast_zero] using castZero)
  exact (Nat.ne_of_gt target.denominator_positive) naturalZero

/-- Casting the retained natural numerator recovers the original integer numerator.

Strict positivity excludes the negative integer constructor. The original
natural readback therefore converts back to the same stored numerator, and
scalar congruence retains that equality over the canonical rational carrier. -/
public theorem numerator_cast (target : PositiveSquareClassRepresentative) :
    (target.numerator : Fraction.Rational) =
      (target.representative.value.num : Fraction.Rational) := by
  have numeratorPositive : 0 < target.representative.value.num :=
    (Fraction.Order.Basic.zero_lt_iff_num_pos
      target.representative.value).mp target.positive
  have integerEquality :
      (target.representative.value.num.toNat : Int) =
        target.representative.value.num :=
    Data.Int.ToNat.toNat_of_pos numeratorPositive
  have castEquality :=
    congrArg (fun value : Int => (value : Fraction.Rational)) integerEquality
  change (target.representative.value.num.toNat : Fraction.Rational) =
    (target.representative.value.num : Fraction.Rational)
  rewrite [Int.cast_natCast] at castEquality
  exact castEquality

/-- The retained natural numerator and denominator reconstruct the exact value.

Multiplying by the original nonzero denominator reads back its stored signed
numerator. The natural numerator cast and direct division cancellation then
identify the quotient with the same canonical rational representative. -/
public theorem value_eq_div (target : PositiveSquareClassRepresentative) :
    target.representative.value =
      (target.numerator : Fraction.Rational) / (target.denominator : Fraction.Rational) := by
  apply Fraction.Field.mul_right_cancel_of_ne
    target.denominator_cast_ne_zero
  calc
    target.representative.value * (target.denominator : Fraction.Rational) =
        (target.representative.value.num : Fraction.Rational) :=
      Fraction.Cast.representative_mul_den
        target.representative.value
    _ = (target.numerator : Fraction.Rational) := target.numerator_cast.symm
    _ = ((target.numerator : Fraction.Rational) /
          (target.denominator : Fraction.Rational)) *
          (target.denominator : Fraction.Rational) :=
      (Fraction.Field.div_mul_cancel_of_ne _ _
        target.denominator_cast_ne_zero).symm

end PositiveSquareClassRepresentative
end Purelib.NumberTheory.SquareClass.Rational.Basic.TheoremSixtyTwo
