module
import Purelib.Data.Int.ToNat
-- Exposed displays retain the original denominator with its direct sign proof.
public import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.SignedFraction.Basic

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

namespace Purelib.Data.Rat.SignedFraction.Normalization

open Purelib.Data.Int

/-- Normalize a signed-denominator display to its unique canonical rational record.

Convert the positive integer denominator to its equal natural value and run the original gcd normalization. The result
retains a positive denominator and proposition-valued coprimality. -/
def ofFraction (fraction : SignedFraction) :
  Fraction.Rational :=
  Fraction.normalize fraction.toRaw

/-- Equivalent signed displays normalize to the same canonical rational.

The two positive denominators retain their exact natural readbacks, so the
original signed cross-product certificate supplies raw-fraction equivalence. -/
theorem ofFraction_eq_of_equivalent
    {left right : SignedFraction}
    (equivalent : SignedFraction.Basic.Equivalent left right) :
    ofFraction left = ofFraction right := by
  apply Fraction.normalize_respects
  exact (SignedFraction.Basic.fraction_toRaw_equivalent_iff left right).mpr equivalent

/-- Two signed displays normalize equally exactly when their cross products agree.

Canonical uniqueness identifies equality of their reduced raw displays with
the original signed relation, retaining both input numerators and denominators. -/
theorem ofFraction_eq_iff (left right :
  SignedFraction) :
    ofFraction left = ofFraction right ↔
      SignedFraction.Basic.Equivalent left right := by
  exact (Fraction.equivalent_iff_normalize_eq left.toRaw right.toRaw).symm.trans
    (SignedFraction.Basic.fraction_toRaw_equivalent_iff left right)
section ReducedFraction

/-- Read a canonical fraction as a positive signed-denominator display. -/
def toFraction (fraction : Fraction.Basic.ReducedFraction) :
  SignedFraction :=
  ⟨fraction.num, (fraction.den : Int),
    Order.natCast_pos fraction.den_pos⟩

/-- Normalize a signed display to the canonical reduced-fraction carrier. -/
def normalize (fraction : SignedFraction) :
  Fraction.Basic.ReducedFraction :=
  ofFraction fraction

/-- The displayed coordinates of normalization are cross-product equivalent to the input. -/
theorem normalize_equivalent (fraction :
  SignedFraction) :
    SignedFraction.Basic.Equivalent (toFraction (normalize
      fraction)) fraction := by
  have canonicalEquivalent := Fraction.normalize_equivalent fraction.toRaw
  change
    (Fraction.normalize fraction.toRaw).num * fraction.den =
      fraction.num * (Fraction.normalize fraction.toRaw).den
  have denominatorCast : (fraction.den.toNat : Int) = fraction.den :=
    ToNat.toNat_of_pos fraction.den_pos
  simpa only [Fraction.Equivalent, Fraction.Rational.toRaw,
    SignedFraction.toRaw, denominatorCast] using canonicalEquivalent

/-- Cross-product equivalent signed displays have identical reduced normalizations. -/
theorem normalize_respects {left right :
  SignedFraction}
    (equivalent : SignedFraction.Basic.Equivalent left right) :
    normalize left = normalize right :=
  ofFraction_eq_of_equivalent equivalent

end ReducedFraction

/-- Normalizing the signed display of a rational representative recovers the original rational. -/
theorem representative_spec (value : Fraction.Rational) :
    ofFraction (toFraction (Fraction.Basic.representative
      value)) = value := by
  change Fraction.normalize
    ⟨value.num, Int.toNat (value.den : Int),
      Int.ToNat.toNat_pos_direct (Order.natCast_pos value.den_pos)⟩ = value
  have displayEqual :
      (⟨value.num, Int.toNat (value.den : Int),
        Int.ToNat.toNat_pos_direct (Order.natCast_pos value.den_pos)⟩ :
        Fraction.RawFraction) = value.toRaw := by
    cases value with
    | mk num den den_pos reduced =>
        rfl
  rw [displayEqual, Fraction.normalize_idempotent]

/-- Normalizing the signed display of a reduced record recovers that exact record. -/
theorem representative_of_reduced (reduced :
  Fraction.Basic.ReducedFraction) :
    Fraction.Basic.representative (ofFraction (toFraction
      reduced)) = reduced :=
  representative_spec reduced
end Purelib.Data.Rat.SignedFraction.Normalization

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

namespace Purelib.Data.Rat.SignedFraction.Normalization

/-- Taking the representative of a reduced record's value returns the same record. -/
theorem representative_value (source :
  Fraction.Basic.ReducedFraction) :
    Fraction.Basic.representative (Fraction.Basic.value source) = source := rfl

/-- The value of signed-display normalization is its canonical rational normalization. -/
theorem normalize_value (fraction :
  SignedFraction) :
    Fraction.Basic.value (normalize fraction) = ofFraction
      fraction := rfl
end Purelib.Data.Rat.SignedFraction.Normalization

end
