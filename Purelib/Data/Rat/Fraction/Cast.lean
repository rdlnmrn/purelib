module
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Field

import Mathlib.Algebra.Order.Ring.Defs

open Purelib.Algebra

open Purelib.Data.Rat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
@[expose] public section

/-!
# Casts and order for canonical fractions

Natural and integer casts are related directly to denominator-one canonical
records.  Weak order is sign-safe cross multiplication; strict order is its
constructive asymmetric part and is proved equivalent to strict integer
cross multiplication.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib.Data.Int
open Purelib.Algebra.Ring

/-- The canonical denominator-one record for an integer. -/
def Cast.fromInt (value : Int) : Rational :=
  ⟨value, 1, by decide,
    ⟨⟨0, 1, by
      change 0 * value.natAbs + 1 * (1 : Int) = 1
      rw [Arithmetic.zero_mul, Int.one_mul, Arithmetic.zero_add]⟩⟩⟩

/-- Integer denominator-one records preserve addition.

Their plain sum has the original integer sum as numerator and denominator
one, so canonical uniqueness identifies it with the displayed cast record. -/
theorem Cast.add_fromInt (left right : Int) :
    Fraction.Cast.fromInt left + Fraction.Cast.fromInt right = Fraction.Cast.fromInt (left + right) := by
  apply eq_of_equivalent
  have displayed := add_plain (Fraction.Cast.fromInt left) (Fraction.Cast.fromInt right)
  have plainAddition :
      Equivalent
        (plainAddRaw (Fraction.Cast.fromInt left).toRaw (Fraction.Cast.fromInt right).toRaw)
        (Fraction.Cast.fromInt (left + right)).toRaw := by
    dsimp only [Equivalent, plainAddRaw, Rational.toRaw, Fraction.Cast.fromInt]
    rw [Nat.one_mul, Int.natCast_one, Arithmetic.mul_one, Arithmetic.mul_one,
      Arithmetic.mul_one, Arithmetic.mul_one]
  exact equivalent_trans displayed plainAddition

/-- Natural casts are exactly denominator-one canonical records. -/
theorem Cast.natCast_eq_fromInt (value : Nat) :
    (value : Rational) = Fraction.Cast.fromInt (value : Int) := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ, inductionHypothesis]
      change Fraction.Cast.fromInt (value : Int) + Fraction.Cast.fromInt 1 =
        Fraction.Cast.fromInt ((value + 1 : Nat) : Int)
      rw [Fraction.Cast.add_fromInt]
      rfl

/-- Integer casts are exactly denominator-one canonical records. -/
theorem Cast.intCast_eq_fromInt (value : Int) :
    (value : Rational) = Fraction.Cast.fromInt value := by
  cases value with
  | ofNat value =>
      change (((value : Nat) : Int) : Rational) = Fraction.Cast.fromInt (value : Int)
      rw [Int.cast_natCast, Fraction.Cast.natCast_eq_fromInt]
  | negSucc value =>
      rw [IntCast.cast_negSucc, Fraction.Cast.natCast_eq_fromInt]
      apply Rational.ext
      · rfl
      · rfl

/-- Equality of two canonical rational natural casts implies equality of their natural inputs. -/
theorem Cast.Order.natCast_injective_direct {left right : Nat}
    (equal : (left : Rational) = (right : Rational)) : left = right := by
  rw [Fraction.Cast.natCast_eq_fromInt left, Fraction.Cast.natCast_eq_fromInt right] at equal
  have numeratorEqual := congrArg Rational.num equal
  exact Int.ofNat.inj numeratorEqual

/-- Equality of two canonical rational integer casts implies equality of their integer inputs. -/
theorem Cast.Order.intCast_injective_direct {left right : Int}
    (equal : (left : Rational) = (right : Rational)) : left = right := by
  rw [Fraction.Cast.intCast_eq_fromInt left, Fraction.Cast.intCast_eq_fromInt right] at equal
  exact congrArg Rational.num equal
end Purelib.Data.Rat.Fraction

end

end

section
@[expose] public section

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

namespace Purelib.Data.Rat.Fraction.Cast

open Purelib.Data.Int

/-- Integer addition is preserved by the canonical denominator-one embedding.  This direct route avoids the generic cast
theorem's quotient extensionality dependency. -/
theorem intCast_add_direct (left right : Int) :
    ((left + right : Int) : Fraction.Rational) =
      (left : Fraction.Rational) + (right : Fraction.Rational) := by
  rw [intCast_eq_fromInt,
    intCast_eq_fromInt,
    intCast_eq_fromInt]
  exact (add_fromInt left right).symm

/-- Integer multiplication is preserved by the canonical denominator-one embedding, proved directly from the displayed
cross-products.  This avoids the generic cast theorem whose upstream proof route uses quotient extensionality. -/
theorem intCast_mul_direct (left right : Int) :
    ((left * right : Int) : Fraction.Rational) =
      (left : Fraction.Rational) * (right : Fraction.Rational) := by
  rw [intCast_eq_fromInt,
    intCast_eq_fromInt,
    intCast_eq_fromInt]
  apply Fraction.eq_of_equivalent
  have plainResult : Fraction.Equivalent
      (fromInt (left * right)).toRaw
      (Fraction.plainMulRaw
        (fromInt left).toRaw
        (fromInt right).toRaw) := by
    dsimp only [Fraction.Equivalent,
      Fraction.plainMulRaw,
      Fraction.Rational.toRaw,
      fromInt]
  exact Fraction.equivalent_trans plainResult
    (Fraction.mul_plain
      (fromInt left)
      (fromInt right)).symm

/-- Equality of two canonical rational natural casts implies equality of their natural inputs. -/
theorem Compatibility.natCast_injective_direct {left right : Nat}
    (equal : (left : Fraction.Rational) = (right : Fraction.Rational)) : left = right :=
  Fraction.Cast.Order.natCast_injective_direct equal

/-- Equality of two canonical rational integer casts implies equality of their integer inputs. -/
theorem Compatibility.intCast_injective_direct {left right : Int}
    (equal : (left : Fraction.Rational) = (right : Fraction.Rational)) : left = right :=
  Fraction.Cast.Order.intCast_injective_direct equal

/-- Multiplying a rational by its retained positive denominator recovers its retained integer numerator cast.

The canonical record has a positive natural denominator. Multiplication by its
exact rational cast cancels that denominator and retains the original integer
numerator. -/
theorem representative_mul_den (value : Fraction.Rational) :
    value * ((Fraction.Basic.representative value).den : Fraction.Rational) =
      ((Fraction.Basic.representative value).num : Fraction.Rational) := by
  change value * (value.den : Fraction.Rational) = (value.num : Fraction.Rational)
  rw [natCast_eq_fromInt,
    intCast_eq_fromInt]
  apply Fraction.eq_of_equivalent
  have productDisplay := Fraction.mul_plain value
    (fromInt (value.den : Int))
  have plainResult : Fraction.Equivalent
      (Fraction.plainMulRaw value.toRaw
        (fromInt (value.den : Int)).toRaw)
      (fromInt value.num).toRaw := by
    dsimp only [Fraction.Equivalent,
      Fraction.plainMulRaw,
      Fraction.Rational.toRaw,
      fromInt]
    rw [Int.natCast_one, Nat.mul_one, Arithmetic.mul_one]
  exact Fraction.equivalent_trans productDisplay plainResult
end Purelib.Data.Rat.Fraction.Cast

end

end

section
@[expose] public section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

namespace Purelib.Data.Rat.Fraction.Cast

/- The canonical finite representative is its displayed numerator divided
by its displayed positive denominator. -/

/-! ## The finite rational-root bounds -/

/-- Casting a positive natural to the canonical rational carrier gives a nonzero value. -/
private theorem Order.natCast_ne_zero_of_pos {value : Nat} (positive : 0 < value)
  :
    (value : Fraction.Rational) ≠ 0 := by
  intro equal
  have valueZero : value = 0 :=
    Fraction.Cast.Compatibility.natCast_injective_direct
      (equal.trans (Nat.cast_zero).symm)
  exact (Nat.ne_of_gt positive) valueZero

/-- A canonical rational equals its retained numerator cast divided by its retained positive denominator cast. -/
theorem representative_eq_num_div_den (value : Fraction.Rational) :
    value = ((Fraction.Basic.representative value).num : Fraction.Rational) /
      ((Fraction.Basic.representative value).den : Fraction.Rational) := by
  let reduced := Fraction.Basic.representative value
  have denominatorNonzero : (reduced.den : Fraction.Rational) ≠ 0 :=
    Fraction.Cast.Order.natCast_ne_zero_of_pos reduced.den_pos
  apply Fraction.Field.mul_right_cancel_of_ne denominatorNonzero
  rw [representative_mul_den]
  exact (Field.ExplicitField.div_mul_cancel
    (reduced.num : Fraction.Rational) denominatorNonzero).symm
end Purelib.Data.Rat.Fraction.Cast

end

section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Cast

/-- Build the canonical denominator-one record for a natural number. -/
def ofNat (source : Nat) : Fraction.Basic.ReducedFraction :=
  fromInt (source : Int)

/-- The retained reduced record of a natural cast is its denominator-one constructor. -/
theorem ofRational_natCast (source : Nat) :
    Fraction.Basic.ofRational (source : Fraction.Rational) = ofNat source := by
  exact natCast_eq_fromInt source
end Purelib.Data.Rat.Fraction.Cast

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7 worked examples

This module records the exact rational calculation of Example 7.2 and the
fully executable finite-field calculation of Example 7.3.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSeven

namespace ChapterSevenExamples

/-- Casting a nonzero natural to canonical rationals preserves nonzeroness. -/
private theorem rational_natCast_nonzero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Fraction.Rational) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (Fraction.Cast.Compatibility.natCast_injective_direct castZero)

end ChapterSevenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterSeven

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 17 worked examples

This module records the complete finite-field arithmetic printed in Examples
17.1, 17.2, and 17.4, together with the exact constructive-rational data of
Example 17.3.  All finite-field coordinates are literal elements of the
executable eleven-element field; no enumeration of all field elements or
roots is used.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSeventeen

namespace ChapterSeventeenExamples

namespace ExampleSeventeenThree

/-- Casting a nonzero natural to canonical rationals preserves nonzeroness. -/
private theorem rational_natCast_nonzero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Fraction.Rational) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (Fraction.Cast.Compatibility.natCast_injective_direct castZero)
end ExampleSeventeenThree

end ChapterSeventeenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterSeventeen

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 6 worked examples

The numerical examples use the project's executable constructive rational
field.  Every equality below reduces to finite integer arithmetic; no decimal
or completed-real interpretation is involved.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSix

namespace ChapterSixExamples

end ChapterSixExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterSix

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10 rational examples

The two examples below retain the source's literal rational coordinates.  All
side matches and spread matches are explicit finite permutation witnesses.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTen

namespace ChapterTenExamples

/-- Casting a nonzero natural to canonical rationals preserves nonzeroness. -/
private theorem rational_natCast_nonzero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Fraction.Rational) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (Fraction.Cast.Compatibility.natCast_injective_direct castZero)

end ChapterTenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterTen

end

public section

namespace Purelib.Data.Rat.Fraction.Cast

/-- Natural addition is preserved by the canonical denominator-one embedding. -/
theorem natCast_add_direct (left right : Nat) :
    ((left + right : Nat) : Rational) = (left : Rational) + (right : Rational) := by
  rw [natCast_eq_fromInt (left + right), natCast_eq_fromInt left,
    natCast_eq_fromInt right]
  exact (add_fromInt (left : Int) (right : Int)).symm

/-- Natural multiplication is preserved by the canonical denominator-one embedding. -/
theorem natCast_mul_direct (left right : Nat) :
    ((left * right : Nat) : Rational) = (left : Rational) * (right : Rational) :=
  intCast_mul_direct (left : Int) (right : Int)

end Purelib.Data.Rat.Fraction.Cast

end
