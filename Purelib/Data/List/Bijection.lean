module

import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
-- Retain the existing field API re-export for list-bijection clients.
public import Purelib.Algebra.Field.ExplicitField
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Bijections between displayed finite lists

The retained maps preserve membership and are inverse on listed elements.
Duplicate-free input lists therefore have the same length.
-/

open Purelib.Data.List

public section

namespace Purelib.Data.List.Bijection

set_option genInjectivity false in
/-- Retain mutually inverse maps between the members of two displayed lists.

The maps act on the underlying carriers, while membership and inverse laws are
required only for listed elements. No duplicate-freeness is assumed in the record
itself. -/
structure ListBijection {Alpha Beta : Type*}
    (source : List Alpha) (target : List Beta) where
  /-- The retained map from the source carrier to the target carrier. -/ forward : Alpha → Beta
  /-- The retained map from the target carrier to the source carrier. -/ backward : Beta → Alpha
  /-- The forward map sends each displayed source member into the target list. -/ forward_mem : ∀ value ∈ source,
    forward value ∈ target
  /-- The backward map sends each displayed target member into the source list. -/ backward_mem : ∀ value ∈ target,
    backward value ∈ source
  /-- Backward after forward recovers each displayed source member. -/ backward_forward : ∀ value ∈ source, backward
    (forward value) = value
  /-- Forward after backward recovers each displayed target member. -/ forward_backward : ∀ value ∈ target, forward
    (backward value) = value

constructive_injectivity ListBijection

namespace ListBijection

/-- A map injective on the displayed list preserves its duplicate-freeness.

Only pairs of members require an injectivity witness. Structural recursion separates
the mapped head from the mapped tail. -/
private theorem nodup_map_of_injective_on
    {Alpha Beta : Type*} {values : List Alpha} (function : Alpha → Beta)
    (injectiveOn : ∀ left ∈ values, ∀ right ∈ values,
      function left = function right → left = right)
    (valuesNodup : values.Nodup) : (values.map function).Nodup := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      rw [List.map_cons]
      apply List.pairwise_cons.mpr
      constructor
      · intro mapped mappedMember equal
        rcases Map.mem_map.mp mappedMember with
          ⟨source, sourceMember, sourceEqual⟩
        apply (List.pairwise_cons.mp valuesNodup).1 source sourceMember
        apply injectiveOn head List.mem_cons_self source
          (List.mem_cons_of_mem head sourceMember)
        exact equal.trans sourceEqual.symm
      · apply inductionHypothesis
        · intro left leftMember right rightMember equal
          exact injectiveOn left (List.mem_cons_of_mem head leftMember)
            right (List.mem_cons_of_mem head rightMember) equal
        · exact (List.pairwise_cons.mp valuesNodup).2

/-- A retained bijection between two duplicate-free lists identifies their lengths.

Both lists must have no repeated entries. Each retained map gives a duplicate-free
subcollection of the other list, and the two finite length bounds imply equality. -/
theorem length_eq {Alpha Beta : Type*} {source : List Alpha}
    {target : List Beta} (bijection : ListBijection source target)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup) :
    source.length = target.length := by
  have forwardNodup : (source.map bijection.forward).Nodup :=
    ListBijection.nodup_map_of_injective_on bijection.forward (by
      intro left leftMember right rightMember equal
      calc
        left = bijection.backward (bijection.forward left) :=
          (bijection.backward_forward left leftMember).symm
        _ = bijection.backward (bijection.forward right) :=
          congrArg bijection.backward equal
        _ = right := bijection.backward_forward right rightMember)
      sourceNodup
  have forwardContained : ∀ value ∈ source.map bijection.forward,
      value ∈ target := by
    intro value member
    rcases Map.mem_map.mp member with
      ⟨sourceValue, sourceMember, equal⟩
    exact equal ▸ bijection.forward_mem sourceValue sourceMember
  have sourceLeTarget : source.length ≤ target.length := by
    rw [← Map.length_map bijection.forward source]
    exact Nodup.nodup_length_le_of_mem forwardNodup targetNodup
      forwardContained
  have backwardNodup : (target.map bijection.backward).Nodup :=
    ListBijection.nodup_map_of_injective_on bijection.backward (by
      intro left leftMember right rightMember equal
      calc
        left = bijection.forward (bijection.backward left) :=
          (bijection.forward_backward left leftMember).symm
        _ = bijection.forward (bijection.backward right) :=
          congrArg bijection.forward equal
        _ = right := bijection.forward_backward right rightMember)
      targetNodup
  have backwardContained : ∀ value ∈ target.map bijection.backward,
      value ∈ source := by
    intro value member
    rcases Map.mem_map.mp member with
      ⟨targetValue, targetMember, equal⟩
    exact equal ▸ bijection.backward_mem targetValue targetMember
  have targetLeSource : target.length ≤ source.length := by
    rw [← Map.length_map bijection.backward target]
    exact Nodup.nodup_length_le_of_mem backwardNodup sourceNodup
      backwardContained
  exact Nat.le_antisymm sourceLeTarget targetLeSource

end ListBijection
end Purelib.Data.List.Bijection
