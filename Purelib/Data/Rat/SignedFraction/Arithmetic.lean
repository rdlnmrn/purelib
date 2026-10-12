module
import Purelib.Data.Int.ToNat
-- Exposed signed records retain the direct denominator sign certificates.
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.SignedFraction.Basic
public import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.Data.Int.Arithmetic

import Mathlib.Order.Basic
import Mathlib.Order.Lattice

open Purelib.Data

open Purelib.Data.Rat

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

namespace Purelib.Data.Rat.SignedFraction.Arithmetic

open Purelib.Data.Int

/-- The positive-denominator signed display of zero. -/
def zeroFraction : SignedFraction := ⟨0, 1, by
  decide⟩
/-- The positive-denominator signed display of one. -/
def oneFraction : SignedFraction := ⟨1, 1, by
  decide⟩

/-- Add two signed displays with their positive product denominator. -/
def addFraction (left right : SignedFraction) :
  SignedFraction :=
  ⟨left.num * right.den + right.num * left.den,
    left.den * right.den, Order.mul_pos left.den_pos right.den_pos⟩

/-- Negate a signed display's numerator while retaining its positive denominator. -/
def negFraction (fraction : SignedFraction) :
  SignedFraction :=
  ⟨-fraction.num, fraction.den, fraction.den_pos⟩

/-- Multiply two signed displays with their positive product denominator. -/
def mulFraction (left right : SignedFraction) :
  SignedFraction :=
  ⟨left.num * right.num, left.den * right.den,
    Order.mul_pos left.den_pos right.den_pos⟩

/-- A nonzero displayed integer has a positive square. -/
private theorem int_mul_self_pos {value : Int} (nonzero : value ≠ 0) :
    0 < value * value := Order.mul_self_pos nonzero

/-- Normalize a signed display and read back its total canonical reciprocal.

Zero is sent to zero. For a nonzero value the canonical inverse exchanges numerator magnitude and denominator, retaining
the numerator sign and the positive-denominator certificate. -/
def invFraction (fraction : SignedFraction) :
  SignedFraction :=
  let reciprocal := (SignedFraction.Normalization.ofFraction fraction)⁻¹
  ⟨reciprocal.num, (reciprocal.den : Int),
    Order.natCast_pos reciprocal.den_pos⟩

/-- Normalizing the retained reciprocal display gives the canonical reciprocal.

The signed denominator is positive and inversion treats zero explicitly. The
retained reciprocal display normalizes to the total canonical inverse in either
branch. -/
theorem ofFraction_invFraction (fraction :
  SignedFraction) :
    SignedFraction.Normalization.ofFraction (invFraction fraction) =
      (SignedFraction.Normalization.ofFraction fraction)⁻¹ := by
  let reciprocal := (SignedFraction.Normalization.ofFraction fraction)⁻¹
  change Fraction.normalize
    ⟨reciprocal.num, Int.toNat (reciprocal.den : Int),
      Int.ToNat.toNat_pos_direct (Order.natCast_pos reciprocal.den_pos)⟩ = reciprocal
  have displayEqual :
      (⟨reciprocal.num, Int.toNat (reciprocal.den : Int),
        Int.ToNat.toNat_pos_direct (Order.natCast_pos reciprocal.den_pos)⟩ :
        Fraction.RawFraction) = reciprocal.toRaw := by
    cases reciprocal with
    | mk num den den_pos reduced =>
        rfl
  rw [displayEqual, Fraction.normalize_idempotent]

/-- The natural rational cast is normalization of the denominator-one signed display. -/
theorem natCast_eq_fraction (value : Nat) :
    (value : Fraction.Rational) =
      SignedFraction.Normalization.ofFraction ⟨Int.ofNat value, 1, by decide⟩ := by
  rw [Fraction.Cast.natCast_eq_fromInt]
  change Fraction.Cast.fromInt (Int.ofNat value) =
    Fraction.normalize
      ⟨Int.ofNat value, Int.toNat 1, Int.ToNat.toNat_pos_direct (by decide)⟩
  have displayEqual :
      (⟨Int.ofNat value, Int.toNat 1,
        Int.ToNat.toNat_pos_direct (by decide)⟩ : Fraction.RawFraction) =
        (Fraction.Cast.fromInt (Int.ofNat value)).toRaw := by
    rfl
  rw [displayEqual, Fraction.normalize_idempotent]

/-- The integer rational cast is normalization of the denominator-one signed display. -/
theorem intCast_eq_fraction (value : Int) :
    (value : Fraction.Rational) = SignedFraction.Normalization.ofFraction ⟨value, 1, by decide⟩ := by
  rw [Fraction.Cast.intCast_eq_fromInt]
  change Fraction.Cast.fromInt value =
    Fraction.normalize ⟨value, Int.toNat 1,
      Int.ToNat.toNat_pos_direct (by decide)⟩
  have displayEqual :
      (⟨value, Int.toNat 1,
        Int.ToNat.toNat_pos_direct (by decide)⟩ : Fraction.RawFraction) =
        (Fraction.Cast.fromInt value).toRaw := by
    rfl
  rw [displayEqual, Fraction.normalize_idempotent]

/-- Normalizing the ordinary signed sum agrees with adding the two canonical normalizations.

The two original positive signed denominators define the sum display. Its cross-
product relation identifies its canonical normalization with canonical addition. -/
theorem ofFraction_addFraction (left right :
  SignedFraction) :
    SignedFraction.Normalization.ofFraction left + SignedFraction.Normalization.ofFraction right =
      SignedFraction.Normalization.ofFraction (addFraction left right) := by
  apply Fraction.eq_of_equivalent
  have sumDisplay := Fraction.add_plain
    (SignedFraction.Normalization.ofFraction left) (SignedFraction.Normalization.ofFraction right)
  have leftNormalized : Fraction.Equivalent
      (SignedFraction.Normalization.ofFraction left).toRaw left.toRaw :=
    Fraction.normalize_equivalent left.toRaw
  have rightNormalized : Fraction.Equivalent
      (SignedFraction.Normalization.ofFraction right).toRaw right.toRaw :=
    Fraction.normalize_equivalent right.toRaw
  have replacedInputs := Fraction.plainAddRaw_respects
    leftNormalized rightNormalized
  have displayedSum : Fraction.Equivalent
      (Fraction.plainAddRaw left.toRaw right.toRaw)
      (addFraction left right).toRaw := by
    have leftDenominator : (left.den.toNat : Int) = left.den :=
      ToNat.toNat_of_pos left.den_pos
    have rightDenominator : (right.den.toNat : Int) = right.den :=
      ToNat.toNat_of_pos right.den_pos
    have sumDenominator : ((left.den * right.den).toNat : Int) =
        left.den * right.den :=
      ToNat.toNat_of_pos (Order.mul_pos left.den_pos right.den_pos)
    dsimp only [Fraction.Equivalent,
      Fraction.plainAddRaw, SignedFraction.toRaw, addFraction]
    rw [Int.natCast_mul, leftDenominator, rightDenominator, sumDenominator]
  have resultNormalized : Fraction.Equivalent
      (SignedFraction.Normalization.ofFraction (addFraction left right)).toRaw
      (addFraction left right).toRaw :=
    Fraction.normalize_equivalent (addFraction left right).toRaw
  exact Fraction.equivalent_trans sumDisplay
    (Fraction.equivalent_trans replacedInputs
      (Fraction.equivalent_trans displayedSum
        resultNormalized.symm))

/-- Normalizing the ordinary signed product agrees with multiplying the two canonical normalizations.

The two original positive signed denominators define the product display. Its
cross-product relation identifies its canonical normalization with canonical
multiplication. -/
theorem ofFraction_mulFraction (left right :
  SignedFraction) :
    SignedFraction.Normalization.ofFraction left * SignedFraction.Normalization.ofFraction right =
      SignedFraction.Normalization.ofFraction (mulFraction left right) := by
  apply Fraction.eq_of_equivalent
  have productDisplay := Fraction.mul_plain
    (SignedFraction.Normalization.ofFraction left) (SignedFraction.Normalization.ofFraction right)
  have leftNormalized : Fraction.Equivalent
      (SignedFraction.Normalization.ofFraction left).toRaw left.toRaw :=
    Fraction.normalize_equivalent left.toRaw
  have rightNormalized : Fraction.Equivalent
      (SignedFraction.Normalization.ofFraction right).toRaw right.toRaw :=
    Fraction.normalize_equivalent right.toRaw
  have replacedInputs := Fraction.plainMulRaw_respects
    leftNormalized rightNormalized
  have displayedProduct : Fraction.Equivalent
      (Fraction.plainMulRaw left.toRaw right.toRaw)
      (mulFraction left right).toRaw := by
    have leftDenominator : (left.den.toNat : Int) = left.den :=
      ToNat.toNat_of_pos left.den_pos
    have rightDenominator : (right.den.toNat : Int) = right.den :=
      ToNat.toNat_of_pos right.den_pos
    have productDenominator : ((left.den * right.den).toNat : Int) =
        left.den * right.den :=
      ToNat.toNat_of_pos (Order.mul_pos left.den_pos right.den_pos)
    dsimp only [Fraction.Equivalent,
      Fraction.plainMulRaw, SignedFraction.toRaw, mulFraction]
    rw [Int.natCast_mul, leftDenominator, rightDenominator, productDenominator]
  have resultNormalized : Fraction.Equivalent
      (SignedFraction.Normalization.ofFraction (mulFraction left right)).toRaw
      (mulFraction left right).toRaw :=
    Fraction.normalize_equivalent (mulFraction left right).toRaw
  exact Fraction.equivalent_trans productDisplay
    (Fraction.equivalent_trans replacedInputs
      (Fraction.equivalent_trans displayedProduct
        resultNormalized.symm))

/-- Multiplying a normalized signed display by its original denominator recovers its numerator cast.

The original integer denominator is positive. Its rational cast cancels the
denominator of the normalized display and leaves the cast of the retained
numerator. -/
theorem ofFraction_mul_den (fraction :
  SignedFraction) :
    SignedFraction.Normalization.ofFraction fraction * (fraction.den : Fraction.Rational) =
      (fraction.num : Fraction.Rational) := by
  rw [Fraction.Cast.intCast_eq_fromInt,
    Fraction.Cast.intCast_eq_fromInt]
  apply Fraction.eq_of_equivalent
  have productDisplay := Fraction.mul_plain
    (SignedFraction.Normalization.ofFraction fraction) (Fraction.Cast.fromInt fraction.den)
  have normalizedInput : Fraction.Equivalent
      (SignedFraction.Normalization.ofFraction fraction).toRaw fraction.toRaw :=
    Fraction.normalize_equivalent fraction.toRaw
  have replacedInput := Fraction.plainMulRaw_respects
    normalizedInput
    (Fraction.equivalent_refl
      (Fraction.Cast.fromInt fraction.den).toRaw)
  have denominatorCast : (fraction.den.toNat : Int) = fraction.den :=
    ToNat.toNat_of_pos fraction.den_pos
  have plainResult : Fraction.Equivalent
      (Fraction.plainMulRaw fraction.toRaw
        (Fraction.Cast.fromInt fraction.den).toRaw)
      (Fraction.Cast.fromInt fraction.num).toRaw := by
    dsimp only [Fraction.Equivalent,
      Fraction.plainMulRaw, SignedFraction.toRaw,
      Fraction.Rational.toRaw,
      Fraction.Cast.fromInt]
    rw [Int.natCast_one, Nat.mul_one, Arithmetic.mul_one, denominatorCast]
  exact Fraction.equivalent_trans productDisplay
    (Fraction.equivalent_trans replacedInput plainResult)

/-- A normalized signed display equals its numerator cast divided by its positive denominator cast.

The positive original denominator gives a nonzero rational cast. The normalized
value is the quotient of the original numerator and denominator casts. -/
theorem ofFraction_eq_div (fraction :
  SignedFraction) :
    SignedFraction.Normalization.ofFraction fraction =
      (fraction.num : Fraction.Rational) / (fraction.den : Fraction.Rational) := by
  have denominatorPositive : (0 : Fraction.Rational) < fraction.den :=
    by
      apply (Fraction.Order.Basic.zero_lt_iff_num_pos _).mpr
      rw [Fraction.Cast.intCast_eq_fromInt]
      exact fraction.den_pos
  apply Fraction.Field.mul_right_cancel_of_ne denominatorPositive.ne'
  calc
    SignedFraction.Normalization.ofFraction fraction * (fraction.den : Fraction.Rational) =
        (fraction.num : Fraction.Rational) := ofFraction_mul_den fraction
    _ = ((fraction.num : Fraction.Rational) / (fraction.den : Fraction.Rational)) *
          (fraction.den : Fraction.Rational) :=
      (Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne').symm
end Purelib.Data.Rat.SignedFraction.Arithmetic

end

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

namespace Purelib.Data.Rat.SignedFraction.Arithmetic

open Purelib.Data.Int

/-! ## Reduction-aware raw operation records -/

/-- Retain a positive raw natural denominator in its signed integer display. -/
private def rawToFraction
    (fraction : Fraction.RawFraction) : SignedFraction :=
  ⟨fraction.num, (fraction.den : Int),
    Order.natCast_pos fraction.den_pos⟩

/-- Read the reduction-aware canonical sum display with its denominator cast to a positive integer. -/
def addRaw (left right : Fraction.Basic.ReducedFraction) :
  SignedFraction :=
  let raw := Fraction.addRaw left right
  ⟨raw.num, (raw.den : Int), Order.natCast_pos raw.den_pos⟩

/-- The reduction-aware signed sum display is equivalent to the ordinary product-denominator sum. -/
theorem addRaw_equivalent (left right :
  Fraction.Basic.ReducedFraction) :
    SignedFraction.Basic.Equivalent (addRaw left right)
      (addFraction (SignedFraction.Normalization.toFraction left)
        (SignedFraction.Normalization.toFraction right)) := by
  simpa only [SignedFraction.Basic.Equivalent, addRaw,
    rawToFraction, addFraction,
    SignedFraction.Normalization.toFraction, Fraction.Equivalent,
    Fraction.addRaw, Fraction.referenceAddRaw,
    Fraction.Rational.toRaw, Int.natCast_mul] using
      Fraction.addRaw_equivalent left right

/-- Compute the original rational product by cross-cancelling its displayed factors.

Each numerator is cancelled against the other denominator using the retained
Euclidean quotient data. The resulting positive-denominator display has the
original product value. -/
def mulRaw (left right : Fraction.Basic.ReducedFraction) :
  SignedFraction := by
  let raw := Fraction.mulRaw left right
  exact ⟨raw.num, (raw.den : Int), Order.natCast_pos raw.den_pos⟩

/-- The cross-cancelled signed product display is equivalent to the ordinary product display. -/
theorem mulRaw_equivalent (left right :
  Fraction.Basic.ReducedFraction) :
    SignedFraction.Basic.Equivalent (mulRaw left right)
      (mulFraction (SignedFraction.Normalization.toFraction left)
        (SignedFraction.Normalization.toFraction right)) := by
  simpa only [SignedFraction.Basic.Equivalent, mulRaw,
    rawToFraction, mulFraction,
    SignedFraction.Normalization.toFraction, Fraction.Equivalent,
    Fraction.mulRaw, Fraction.referenceMulRaw,
    Fraction.Rational.toRaw, Int.natCast_mul] using
      Fraction.mulRaw_equivalent left right

/-- Read the total reciprocal of a reduced fraction as a positive signed display. -/
def invRaw (source : Fraction.Basic.ReducedFraction) :
  SignedFraction :=
  SignedFraction.Normalization.toFraction (source⁻¹)

/-- The canonical reciprocal display is equivalent to the signed reciprocal display. -/
theorem invRaw_equivalent (source : Fraction.Basic.ReducedFraction) :
    SignedFraction.Basic.Equivalent (invRaw source) (invFraction
      (SignedFraction.Normalization.toFraction source)) := by
  apply (SignedFraction.Normalization.ofFraction_eq_iff _ _).mp
  calc
    SignedFraction.Normalization.ofFraction (invRaw source) = source⁻¹ :=
      SignedFraction.Normalization.representative_spec _
    _ = (SignedFraction.Normalization.ofFraction (SignedFraction.Normalization.toFraction source))⁻¹ := by
      exact congrArg (fun value : Fraction.Rational => value⁻¹)
        (SignedFraction.Normalization.representative_spec source).symm
    _ = SignedFraction.Normalization.ofFraction (invFraction
      (SignedFraction.Normalization.toFraction source)) :=
      (ofFraction_invFraction (SignedFraction.Normalization.toFraction source)).symm
end Purelib.Data.Rat.SignedFraction.Arithmetic

end
