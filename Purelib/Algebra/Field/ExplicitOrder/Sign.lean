module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.ExplicitOrder.Basic
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

open Purelib.Algebra.Field.ExplicitOrder.Basic

section
public section

/-!
# Rational rotations, section 12.2: ray proportions and spin

Ray equivalence is kept quotient-free: equality carries a displayed positive
scale.  The ordered-field interface includes the finite sign decision and
incompatibility laws actually used to split each projective class into its
two rays.  Products, inverses, the two-to-one rotation map, and the central
ray `(-1:0)` are all represented by executable coordinates.
-/

namespace Purelib.Algebra.Field.ExplicitOrder.Sign

/-- An ordered explicit field with a decidable nonzero sign split.

Positive values are nonzero, a value and its negative cannot both be positive, and every nonzero value has one of the
two positive signs. -/
class RayOrderedExplicitField (K : Type*) extends OrderedExplicitField K
  where
  /-- Positive scalars are nonzero. -/ positive_ne_zero_direct : ∀ {value : K}, 0 < value → value ≠ 0
  /-- A scalar and its negative cannot both be positive. -/ positive_neg_exclusive_direct : ∀ {value : K}, 0 < value → ¬
    0 < -value
  /-- Every nonzero scalar is positive or has positive negative. -/ sign_split_direct : ∀ value : K, value ≠ 0 → (0 <
    value) ∨ (0 < -value)

namespace RayOrderedExplicitField

variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField F]

section
open Purelib.Algebra.Field.ExplicitOrder.Sign
/-- The positive unit is nonzero in a ray-ordered explicit field. -/
theorem one_ne_zero : (1 : F) ≠ 0 :=
  RayOrderedExplicitField.positive_ne_zero_direct OrderedExplicitField.zero_lt_one_direct

/-- Negative one is nonzero in a ray-ordered explicit field. -/
theorem neg_one_ne_zero : (-1 : F) ≠ 0 := by
  intro negOneZero
  apply RayOrderedExplicitField.one_ne_zero (F := F)
  calc
    (1 : F) = -(-1) := by ring1
    _ = -0 := by rw [negOneZero]
    _ = 0 := by ring1

end

/-- Two is positive as the sum of two positive units. -/
theorem two_pos : 0 < (2 : F) := by
  rw [show (2 : F) = 1 + 1 by ring1]
  exact OrderedExplicitField.add_pos_direct
    OrderedExplicitField.zero_lt_one_direct
    OrderedExplicitField.zero_lt_one_direct

open Purelib.Algebra.Field.ExplicitOrder.Sign in
/-- Two is nonzero in a ray-ordered explicit field. -/
theorem two_ne_zero : (2 : F) ≠ 0 :=
  RayOrderedExplicitField.positive_ne_zero_direct RayOrderedExplicitField.two_pos

end RayOrderedExplicitField

variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField F]

namespace RayOrderedExplicitField

/-- Use the decidable equality retained by the ray-ordered explicit field. -/
local instance instDecidableEq : DecidableEq F := OrderedExplicitField.eq_decidable

/-- Cancel a supplied nonzero right factor from an equality of products. -/
public theorem eq_of_mul_right_eq
    {left right factor :
  F}
    (factorNonzero : factor ≠ 0) (equal : left * factor = right * factor) :
    left = right := by
  have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * (factor * factor⁻¹) := by rw [cancel, mul_one]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [equal]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [cancel, mul_one]

end RayOrderedExplicitField
end Purelib.Algebra.Field.ExplicitOrder.Sign

end

end

section
variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField F]
/-- Use the decidable equality retained by the ray-ordered explicit field. -/
local instance : DecidableEq F := OrderedExplicitField.eq_decidable
namespace Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField
/-- Adding any square to a positive scalar preserves positivity.

The retained equality decision separates zero from a strictly positive nonzero square. -/
public theorem add_square_pos {base value : F}
  (basePositive : 0 < base) :
    0 < base + value ^ 2 := by
  by_cases valueZero : value = 0
  · rw [valueZero]
    simpa only [pow_two, zero_mul, add_zero] using basePositive
  · have squarePositive : 0 < value ^ 2 := by
      simpa only [pow_two] using
        OrderedExplicitField.mul_self_pos_direct valueZero
    exact OrderedExplicitField.add_pos_direct basePositive squarePositive
end Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField
end
