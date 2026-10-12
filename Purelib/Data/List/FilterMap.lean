module

namespace Purelib.Data.List.FilterMap

/-- A filtered map discards a head whose retained result is none.

The supplied option equality selects the discarded-head branch. The original
tail is filtered by the same mapping function. -/
public theorem filterMap_cons_none {Alpha : Type u} {Beta : Type v}
    {function : Alpha → Option Beta} {head : Alpha} {tail : List Alpha}
    (selected : function head = none) :
    (head :: tail).filterMap function = tail.filterMap function := by
  change (match function head with
    | none => tail.filterMap function
    | some value => value :: tail.filterMap function) = _
  rw [selected]

/-- A filtered map retains a successful head result before the filtered tail.

The supplied option equality identifies the retained head value. It precedes
the original tail's filtered map without changing occurrence order. -/
public theorem filterMap_cons_some {Alpha : Type u} {Beta : Type v}
    {function : Alpha → Option Beta} {head : Alpha} {tail : List Alpha}
    {value : Beta} (selected : function head = some value) :
    (head :: tail).filterMap function = value :: tail.filterMap function := by
  change (match function head with
    | none => tail.filterMap function
    | some value => value :: tail.filterMap function) = _
  rw [selected]

end Purelib.Data.List.FilterMap

/-!
# Structural finite-list lemmas

The upstream statements replaced here concern only structural recursion over
displayed finite lists.  Their current proof routes use generic simplifier or
extensionality infrastructure that reaches `Quot.sound`.  These versions keep
the same mathematical content while exposing the finite recursion directly.
-/

public section

namespace Purelib.Data.List

universe u v w

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

/-- Membership in a filtered map is equivalent to a source member mapped to that exact
some value.

The explicit witness retains source membership and the Option equality. None branches
contribute no entries, while successful branches preserve order and multiplicity. -/
theorem FilterMap.mem_filterMap {function : Alpha → Option Beta} {target : Beta} :
    ∀ {values : List Alpha},
      target ∈ values.filterMap function ↔
        ∃ source, source ∈ values ∧ function source = some target
  | [] => by
      constructor
      · intro impossible
        nomatch impossible
      · rintro ⟨_, impossible, _⟩
        nomatch impossible
  | value :: values => by
      cases selected : function value with
      | none =>
          rw [FilterMap.filterMap_cons_none selected]
          constructor
          · intro member
            rcases (mem_filterMap (values := values)).mp member with
              ⟨source, sourceMember, equal⟩
            exact ⟨source, List.mem_cons_of_mem value sourceMember, equal⟩
          · rintro ⟨source, sourceMember, equal⟩
            cases sourceMember with
            | head =>
                rw [selected] at equal
                nomatch equal
            | tail _ tail =>
                exact (mem_filterMap (values := values)).mpr ⟨source, tail, equal⟩
      | some selectedValue =>
          rw [FilterMap.filterMap_cons_some selected]
          constructor
          · intro member
            cases member with
            | head => exact ⟨value, List.Mem.head values, selected⟩
            | tail _ tail =>
                rcases (mem_filterMap (values := values)).mp tail with
                  ⟨source, sourceMember, equal⟩
                exact ⟨source, List.Mem.tail value sourceMember, equal⟩
          · rintro ⟨source, sourceMember, equal⟩
            cases sourceMember with
            | head =>
                have valuesEqual : selectedValue = target := Option.some.inj (selected.symm.trans equal)
                rw [valuesEqual]
                exact List.Mem.head _
            | tail _ tail =>
                exact List.Mem.tail _ ((mem_filterMap (values := values)).mpr
                  ⟨source, tail, equal⟩)
end Purelib.Data.List

end

namespace Purelib.Data.List.FilterMap

/-- Filtering optional outputs cannot increase the length of a finite list.

Each successful head contributes one retained output; a discarded head contributes none. The original tail is processed
by the same function. -/
public theorem length_filterMap_le {Input Output : Type} (function : Input → Option Output) :
    ∀ values : List Input, (values.filterMap function).length ≤ values.length
  | [] => Nat.le_refl 0
  | value :: remaining => by
      cases selected : function value with
      | none =>
          rw [filterMap_cons_none selected]
          exact Nat.le_trans (length_filterMap_le function remaining) (Nat.le_succ _)
      | some result =>
          rw [filterMap_cons_some selected]
          exact Nat.succ_le_succ (length_filterMap_le function remaining)

end Purelib.Data.List.FilterMap
