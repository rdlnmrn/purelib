module

import Purelib.Tactic.QuotientFreeOmega

namespace Purelib.Data.Int.ToNat

/-- Converting a positive integer to a natural and back retains its value.

The natural constructor has this equation by reduction. Positivity excludes
the negative successor constructor, which natural conversion would truncate. -/
public theorem toNat_of_pos {value : Int} (positive : 0 < value) :
    (value.toNat : Int) = value := by
  cases value with
  | ofNat value => rfl
  | negSucc value => cases positive

end Purelib.Data.Int.ToNat

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

namespace Purelib.Data.Int.ToNat

/-- Converting a strictly positive integer to Nat preserves positivity. -/
theorem toNat_pos_direct {value : Int} (positive : 0 < value) :
    0 < value.toNat := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => cases positive
      | succ value => exact Nat.zero_lt_succ value
  | negSucc value => cases positive
end Purelib.Data.Int.ToNat

end
