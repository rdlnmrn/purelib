module

-- The exposed membership-preserving loop retains these original proof owners.
public import Purelib.Data.List.Membership
public import Purelib.Data.List.Append
public import Init.Data.List.Control

/-!
# Iteration through an original finite list

Iteration retains the supplied list, accumulator, callback and original
membership proposition. Its prefix certificate changes only when an original
head is consumed; yielded and early-returned accumulators remain unchanged.
-/

namespace Purelib.Data.List

universe u v w

/-- Iterate through a retained list with its original occurrence certificates.

Each callback receives the same displayed head and its membership in the
original list. A yielded accumulator continues through the retained tail;
an early return ends the traversal without evaluating any remaining callback. -/
@[inline, expose] public def forIn' {Alpha : Type u} {Beta : Type v}
    {m : Type v → Type w} [Monad m] (values : @& List Alpha) (initial : Beta)
    (visit : (value : Alpha) → value ∈ values → Beta → m (ForInStep Beta)) : m Beta :=
  let rec @[specialize] loop : (remaining : @& List Alpha) → (accumulator : Beta) →
      Exists (fun before => before ++ remaining = values) → m Beta
    | [], accumulator, _ => pure accumulator
    | head :: tail, accumulator, retained => do
        have member : head ∈ values := by
          clear visit
          obtain ⟨before, equal⟩ := retained
          cases equal
          exact Membership.mem_append.mpr (Or.inr (List.Mem.head tail))
        match (← visit head member accumulator) with
        | .done result => pure result
        | .yield result =>
            have next : Exists (fun before => before ++ tail = values) := by
              obtain ⟨before, equal⟩ := retained
              refine ⟨before ++ [head], ?_⟩
              exact (Append.append_assoc before [head] tail).trans equal
            loop tail result next
  loop values initial ⟨[], rfl⟩

/-- Select the retained occurrence-preserving finite-list iterator.

The original membership relation, monad and callback contract remain unchanged.
Opening the list scope replaces only the selected iterator's proof certificates. -/
public scoped instance (priority := 1001) [Monad m] :
    ForIn' m (List Alpha) Alpha inferInstance where
  forIn' := forIn'

end Purelib.Data.List
