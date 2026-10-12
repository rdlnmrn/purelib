module
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Filter
public import Purelib.Data.Nat.Decide

/-!
# Bounded positive divisor indices

The original range is filtered by successor divisibility. Its finite order and
indices remain unchanged, with direct membership and length certificates.
-/
namespace Purelib.Data.Nat.Divisors.Indices

open Purelib.Data.List Purelib.Data.List.Range

/-! ## Executable bounded enumeration -/

/-- Enumerate predecessor indices of positive divisors in a bounded natural range.

Filter the indices below value by the test that index + 1 divides value. For positive
value this enumerates its positive divisors; at zero the finite source range is
empty. -/
@[expose] public def positiveDivisorIndices (value : Nat) : List Nat :=
  (List.range value).filter (fun index => index + 1 ∣ value)

/-- A bounded index whose successor divides the value occurs in its divisor enumeration.

The retained range occurrence and exact divisibility decision certify acceptance
by the original filter, without changing its Boolean branch. -/
public theorem mem_positiveDivisorIndices {index value : Nat}
    (bounded : index < value) (divides : index + 1 ∣ value) :
    index ∈ positiveDivisorIndices value := by
  apply Filter.mem_filter.mpr
  exact ⟨Basic.mem_range.mpr bounded, decide_eq_true divides⟩

/-- The positive divisor index list has length at most its finite scan bound.

Filtering retains at most the original range occurrences. That same range has
the displayed bound as its exact length. -/
public theorem positiveDivisorIndices_length_le (value : Nat) :
    (positiveDivisorIndices value).length ≤ value := by
  calc
    (positiveDivisorIndices value).length ≤ (List.range value).length :=
      Filter.length_filter_le _ _
    _ = value := Basic.length_range value
end Purelib.Data.Nat.Divisors.Indices
