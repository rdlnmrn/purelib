module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

section
/-!
# Uniform bounds for finite rational list sums

Every retained mapped occurrence is bounded by the same rational ceiling.
Structural recursion preserves the original list and its multiplicity.
-/

public section

namespace Purelib.Data.List.Rat

open Purelib.Algebra

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.Fraction.Order

/-- Bound a finite rational sum by its number of entries times a common upper bound.

Each retained input occurrence must satisfy the displayed weak bound. The estimate
includes repeated entries and uses direct finite rational addition inequalities. -/
theorem sum_map_le_length_mul_of_bounded {β : Type}
    (items : List β) (value : β → Rational) (ceiling : Rational)
    (bounded : ∀ item, item ∈ items → value item ≤ ceiling) :
    (items.map value).sum ≤ (items.length : Rational) * ceiling := by
  induction items with
  | nil =>
      simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero,
        zero_mul]
      exact le_rfl
  | cons item remaining inductionHypothesis =>
      have tailBounded : ∀ candidate, candidate ∈ remaining →
          value candidate ≤ ceiling := by
        intro candidate member
        exact bounded candidate (List.mem_cons_of_mem item member)
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        NatCast.add, Nat.cast_one]
      calc
        value item + (remaining.map value).sum ≤
            ceiling + (remaining.length : Rational) * ceiling :=
          Arithmetic.add_le_add_direct
            (bounded item List.mem_cons_self)
            (inductionHypothesis tailBounded)
        _ = ((remaining.length : Rational) + 1) * ceiling := by ring1
end Purelib.Data.List.Rat

end
