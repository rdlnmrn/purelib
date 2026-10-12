module

/-!
# Universal predicates over finite lists

The list-wide Boolean and propositional tests retain the original predicate and list spine.
Structural certificates relate its result to acceptance at each displayed
member, with no equality between predicate functions.
-/

namespace Purelib.Data.List

universe u

/-- Every displayed entry satisfies the predicate.

The empty list accepts trivially, a singleton retains only its entry's condition,
and a longer list retains the leading condition and the original tail predicate. -/
@[expose] public def Forall {Alpha : Type u} (predicate : Alpha → Prop) :
    List Alpha → Prop
  | [] => True
  | head :: tail =>
      List.casesOn (motive := fun _ => Prop) tail
        (predicate head)
        (fun _ _ => predicate head ∧ Forall predicate tail)

end Purelib.Data.List

namespace Purelib.Data.List.All

open Purelib

universe u

variable {Alpha : Type u}

/-- A Boolean list-wide test succeeds exactly when every displayed member passes.

Structural recursion relates the conjunction computed by List.all to the predicate's
truth at each list member, without identifying predicate functions. -/
public theorem all_eq_true {predicate : Alpha → Bool} :
    ∀ {values : List Alpha},
      values.all predicate = true ↔
        ∀ value ∈ values, predicate value = true
  | [] => by
      constructor
      · intro _ value impossible
        nomatch impossible
      · intro _
        rfl
  | head :: tail => by
      change (predicate head && tail.all predicate) = true ↔ _
      constructor
      · intro accepted
        have passed : predicate head = true ∧ tail.all predicate = true := by
          generalize predicate head = headResult at accepted ⊢
          generalize tail.all predicate = tailResult at accepted ⊢
          cases headResult <;> cases tailResult <;> cases accepted
          exact ⟨Eq.refl true, Eq.refl true⟩
        have tailAccepted :=
          (all_eq_true (values := tail)).mp passed.2
        intro value member
        cases member with
        | head => exact passed.1
        | tail _ tailMember => exact tailAccepted value tailMember
      · intro accepted
        have headAccepted := accepted head (List.Mem.head tail)
        have tailAccepted :=
          (all_eq_true (values := tail)).mpr
            (fun value member => accepted value (List.Mem.tail head member))
        rewrite [headAccepted, tailAccepted]
        exact Eq.refl true

end Purelib.Data.List.All

namespace Purelib.Data.List.All

open Purelib

universe u v

/-- Universal acceptance of a cons separates its head and tail conditions. -/
public theorem forall_cons {Alpha : Type u} {predicate : Alpha → Prop}
    {head : Alpha} {tail : List Alpha} :
    Data.List.Forall predicate (head :: tail) ↔
      predicate head ∧ Data.List.Forall predicate tail := by
  cases tail with
  | nil => exact ⟨fun passed => ⟨passed, True.intro⟩, fun passed => passed.1⟩
  | cons next rest => exact Iff.rfl

/-- Universal acceptance holds exactly at every displayed list member.

Structural recursion preserves the predicate and original list spine; membership
certificates identify entries without comparing predicate functions. -/
public theorem forall_iff_mem {Alpha : Type u} {predicate : Alpha → Prop} :
    ∀ {values : List Alpha}, Data.List.Forall predicate values ↔
      ∀ value ∈ values, predicate value
  | [] => by
      constructor
      · intro _ value impossible
        nomatch impossible
      · intro _
        exact True.intro
  | head :: tail => by
      constructor
      · intro accepted value member
        have parts := forall_cons.mp accepted
        cases member with
        | head => exact parts.1
        | tail _ tailMember => exact forall_iff_mem.mp parts.2 value tailMember
      · intro accepted
        exact forall_cons.mpr ⟨accepted head (List.Mem.head tail),
          forall_iff_mem.mpr (fun value member => accepted value (List.Mem.tail head member))⟩

/-- Universal acceptance of mapped entries retains the original source predicate.

Each list constructor transports its own scalar condition. The tail remains the
same retained source list, with no equality between functions. -/
public theorem forall_map_iff {Alpha : Type u} {Beta : Type v}
    {predicate : Beta → Prop} {map : Alpha → Beta} :
    ∀ {values : List Alpha}, Data.List.Forall predicate (values.map map) ↔
      Data.List.Forall (fun value => predicate (map value)) values
  | [] => Iff.rfl
  | head :: tail => by
      constructor
      · intro accepted
        have parts := forall_cons.mp accepted
        exact forall_cons.mpr ⟨parts.1, forall_map_iff.mp parts.2⟩
      · intro accepted
        have parts := forall_cons.mp accepted
        exact forall_cons.mpr ⟨parts.1, forall_map_iff.mpr parts.2⟩

end Purelib.Data.List.All
