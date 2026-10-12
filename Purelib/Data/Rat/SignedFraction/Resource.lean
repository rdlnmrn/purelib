module
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Resource.Components
public import Purelib.Data.Rat.SignedFraction.Arithmetic
import Purelib.Data.Rat.SignedFraction.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.SignedFraction.Normalization
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Data.Rat

/-!
# Component bounds of signed arithmetic displays

The signed arithmetic displays retain the same original reduced fraction
components and cancellation quotients. Their numerator magnitudes and natural
denominator readbacks inherit the exact bounds of those original operations.
-/

namespace Purelib.Data.Rat.SignedFraction.Resource

/-- Normalization does not increase the absolute integer numerator.

The same signed input converts to its positive natural-denominator raw display.
The retained gcd divides its numerator magnitude, so normalization reads the
original natural quotient without increasing that magnitude. -/
public theorem normalize_numerator_le (fraction : SignedFraction) :
    (SignedFraction.Normalization.normalize fraction).num.natAbs ≤ fraction.num.natAbs := by
  exact Fraction.Resource.Components.normalize_numerator_le fraction.toRaw

/-- Normalization does not increase the natural value of the original positive signed denominator.

The same positive signed denominator converts to its original natural value.
Dividing by the retained normalization gcd cannot increase that original
denominator readback. -/
public theorem normalize_denominator_le (fraction : SignedFraction) :
    (SignedFraction.Normalization.normalize fraction).den ≤ fraction.den.toNat := by
  exact Fraction.Resource.Components.normalize_denominator_le fraction.toRaw

/-- The reduced-denominator sum display has denominator at most the product of the input denominators.

The original addition divides its left denominator by the shared denominator
gcd before multiplication. That retained quotient is no larger than the
original left denominator, so the signed display inherits the product bound. -/
public theorem addRaw_denominator_le (left right : Fraction.Basic.ReducedFraction) :
    (SignedFraction.Arithmetic.addRaw left right).den.toNat ≤ left.den * right.den := by
  change Fraction.Arithmetic.additionLeftQuotient left right * right.den ≤ left.den * right.den
  exact Nat.mul_le_mul_right right.den (Fraction.Resource.Components.NormalizedFraction.additionLeftQuotient_le left
    right)

/-- The sum display's numerator magnitude is bounded by the sum of the two cross-product magnitudes.

The original sum keeps both reduced denominator quotients outside its signed
cross-products. Their direct numerator magnitude bound is the same bound
proved for the retained canonical raw addition display. -/
public theorem addRaw_numerator_le (left right : Fraction.Basic.ReducedFraction) :
    (SignedFraction.Arithmetic.addRaw left right).num.natAbs ≤
      left.num.natAbs * right.den + right.num.natAbs * left.den :=
  Fraction.Resource.Components.addRaw_numerator_le left right

/-- Cross-cancellation bounds the product display's denominator by the product of the original denominators.

Both original denominator quotients are bounded by their own retained natural
denominators. The signed display reads the identical cross-cancelled product
as a natural denominator before applying the existing component bound. -/
public theorem mulRaw_denominator_le (left right : Fraction.Basic.ReducedFraction) :
    (SignedFraction.Arithmetic.mulRaw left right).den.toNat ≤ left.den * right.den :=
  Fraction.Resource.Components.mulRaw_denominator_le left right

/-- Cross-cancellation bounds the product numerator magnitude by the product of the original magnitudes.

Each retained positive cancellation gcd divides its original numerator
magnitude. Their exact quotient magnitudes and the same original product
inherit the canonical raw multiplication component bound. -/
public theorem mulRaw_numerator_le (left right : Fraction.Basic.ReducedFraction) :
    (SignedFraction.Arithmetic.mulRaw left right).num.natAbs ≤
      left.num.natAbs * right.num.natAbs :=
  Fraction.Resource.Components.mulRaw_numerator_le left right

/-- The reciprocal display denominator is bounded by the larger input component magnitude.

The signed reciprocal reads the denominator of the original canonical inverse.
Its retained component magnitude is bounded by that of the input, which is
the larger original numerator magnitude or natural denominator. -/
public theorem invRaw_denominator_le (source : Fraction.Basic.ReducedFraction) :
    (SignedFraction.Arithmetic.invRaw source).den.toNat ≤ max source.num.natAbs source.den := by
  simpa only [SignedFraction.Arithmetic.invRaw, SignedFraction.Normalization.toFraction, Int.toNat_natCast,
    Fraction.Resource.Components.Size.componentMagnitude] using
    ((Fraction.Resource.Components.Size.denominator_le_componentMagnitude source⁻¹).trans
      (Fraction.Resource.Components.Size.componentMagnitude_inv_le source))

/-- The reciprocal display numerator magnitude is bounded by the larger input component magnitude.

The same canonical inverse supplies the signed reciprocal numerator. Its
original numerator magnitude is bounded by the retained input component
magnitude, the larger original numerator magnitude or denominator. -/
public theorem invRaw_numerator_le (source : Fraction.Basic.ReducedFraction) :
    (SignedFraction.Arithmetic.invRaw source).num.natAbs ≤ max source.num.natAbs source.den := by
  simpa only [SignedFraction.Arithmetic.invRaw, SignedFraction.Normalization.toFraction,
    Fraction.Resource.Components.Size.componentMagnitude] using
    ((Fraction.Resource.Components.Size.numerator_le_componentMagnitude source⁻¹).trans
      (Fraction.Resource.Components.Size.componentMagnitude_inv_le source))
end Purelib.Data.Rat.SignedFraction.Resource
