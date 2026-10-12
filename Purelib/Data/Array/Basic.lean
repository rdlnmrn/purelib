module

-- Iteration retains the original array carrier, membership and indexed readbacks.
public import Init.Data.Array.Basic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Bounded iteration through retained arrays

The original array and its complete size determine a countdown traversal. Each
step reads the same increasing coordinate with its retained bound and stops at
the same yielded, returned or failed monadic result.
-/

namespace Purelib.Data.Array

universe u v w

/-- Iterate through the original array with each entry's occurrence certificate.

The countdown retains the original array, accumulator and callback. Each
successful yield advances one coordinate; an early return or monadic failure
leaves all remaining callbacks unevaluated.
-/
@[inline, expose] public def forIn' {Alpha : Type u} {Beta : Type v}
    {m : Type v → Type w} [Monad m] (values : Array Alpha) (initial : Beta)
    (visit : (value : Alpha) → value ∈ values → Beta → m (ForInStep Beta)) : m Beta :=
  let rec loop (remaining : Nat) (bounded : remaining ≤ values.size)
      (accumulator : Beta) : m Beta := do
    match remaining, bounded with
    | 0, _ => pure accumulator
    | previous + 1, bounded =>
      have previousBelow : previous < values.size :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self previous) bounded
      have lastBelow : values.size - 1 < values.size := by omega0
      have indexBelow : values.size - 1 - previous < values.size :=
        Nat.lt_of_le_of_lt (Nat.sub_le (values.size - 1) previous) lastBelow
      have member : values[values.size - 1 - previous]'indexBelow ∈ values :=
        _root_.Array.Mem.mk (_root_.List.getElem_mem indexBelow)
      match (← visit (values[values.size - 1 - previous]'indexBelow) member accumulator) with
      | .done result => pure result
      | .yield result => loop previous (Nat.le_of_lt previousBelow) result
  loop values.size (Nat.le_refl _) initial

end Purelib.Data.Array
