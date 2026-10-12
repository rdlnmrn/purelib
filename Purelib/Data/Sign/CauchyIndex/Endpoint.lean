module

public import Purelib.Data.Sign.Basic

/-!
# One-sided formal Cauchy contributions

The original denominator-zero test and terminal product reading determine
the contribution. Finite constructor cases certify its scaling laws.
-/

namespace Purelib.Data.Sign

-- This declaration group retains the nominal Purelib.Data.Sign.Basic.Sign public API.

/-- Compute the doubled one-sided Cauchy contribution from four endpoint signs.

The contribution is zero when the initial denominator sign is nonzero. When it is
zero, read the product of the later numerator and denominator signs as an integer;
the initial numerator is unused. -/
@[expose] public def leftEndpointIndex2
    (_P₀ Q₀ P₁ Q₁ : Sign) : Int :=
  if Q₀ = zero then Sign.value (Sign.mul P₁ Q₁) else 0

/-- A nonzero sign scaling all four entries on the left preserves the endpoint
contribution.

The same finite factor multiplies both coordinates at both endpoints, so the
zero-denominator test and the later product reading are unchanged. -/
public theorem leftEndpointIndex2_scale_left
    (A C₀ D₀ C₁ D₁ : Sign) (ANonzero : A ≠ zero) :
    Sign.leftEndpointIndex2 (Sign.mul A C₀) (Sign.mul A D₀)
        (Sign.mul A C₁) (Sign.mul A D₁) =
      Sign.leftEndpointIndex2 C₀ D₀ C₁ D₁ := by
  cases A
  · cases D₀ <;> cases C₁ <;> cases D₁ <;> rfl
  · exact (ANonzero rfl).elim
  · cases D₀ <;> cases C₁ <;> cases D₁ <;> rfl

/-- A nonzero sign scaling all four entries on the right preserves the endpoint
contribution.

The same finite factor multiplies both coordinates at both endpoints, so the
zero-denominator test and the later product reading are unchanged. -/
public theorem leftEndpointIndex2_scale_right
    (C A₀ B₀ A₁ B₁ : Sign) (CNonzero : C ≠ zero) :
    Sign.leftEndpointIndex2 (Sign.mul A₀ C) (Sign.mul B₀ C)
        (Sign.mul A₁ C) (Sign.mul B₁ C) =
      Sign.leftEndpointIndex2 A₀ B₀ A₁ B₁ := by
  cases C
  · cases B₀ <;> cases A₁ <;> cases B₁ <;> rfl
  · exact (CNonzero rfl).elim
  · cases B₀ <;> cases A₁ <;> cases B₁ <;> rfl

/-- Zero denominator signs at both endpoints give zero one-sided contribution. -/
public theorem leftEndpointIndex2_zero_to_zero
    (P₀ P₁ : Sign) :
    Sign.leftEndpointIndex2 P₀ zero P₁ zero = 0 := by
  cases P₁ <;> rfl

end Purelib.Data.Sign
