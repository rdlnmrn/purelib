module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
public import Purelib.Integration.Cell.Basic
public import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Interval.Basic

/-!
# Certified finite integration

Integration is a pair of finite rational sums.  Each displayed cell carries a
nonnegative weight and rational lower and upper values.  No function space,
partition limit, supremum, or completed integral is introduced.
-/

@[expose] public section

namespace Purelib.Integration

open Purelib in
open Purelib.Integration in
/-- A frontier whose lower and upper values agree at every occurrence has zero weighted oscillation. -/
private theorem integralOscillation_eq_zero_of_exact {α : Type} :
    ∀ {cells : List (Integration.IntegrationCell α)},
      (∀ cell, cell ∈ cells → cell.lower = cell.upper) →
      Integration.integralOscillation cells = 0
  | [], _ => rfl
  | cell :: remaining, exactRanges => by
      have head := exactRanges cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          candidate.lower = candidate.upper :=
        fun candidate member =>
          exactRanges candidate (List.mem_cons_of_mem cell member)
      dsimp only [Integration.integralOscillation, IntegrationCell.oscillation]
      rw [head, sub_self, mul_zero, zero_add,
        integralOscillation_eq_zero_of_exact tail]

open Purelib in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration in
/-- Exact cells built from the retained weighted payload-value list have zero enclosure width. -/
theorem integralBound_exact_width
    {α : Type} (entries : List (Measure.Weighted (α × Fraction.Rational))) :
    (Integration.integralBound (entries.map fun entry =>
      IntegrationCell.exact entry.item.1 entry.weight entry.item.2
        entry.nonnegative)).width = 0 := by
  rw [Integration.integralBound_width]
  apply integralOscillation_eq_zero_of_exact
  intro cell member
  rcases Map.mem_map.mp member with ⟨entry, sourceMember, equal⟩
  rw [← equal]
  rfl

end Purelib.Integration

end
