module
import Purelib.Data.List.Membership

/-!
# Structural maps over retained finite lists

A supplied function visits each original entry in order. Structural certificates
retain length, concatenation, membership and composed values on those same
finite spines, including repeated occurrences and the empty list.
-/

namespace Purelib.Data.List.Map

universe u v w

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

/-- Mapping a finite list retains its length.

Each displayed source entry contributes exactly one mapped entry. Structural
recursion on the retained tail proves the length equation by scalar successor
congruence. -/
public theorem length_map (function : Alpha → Beta) :
    ∀ values : List Alpha, (values.map function).length = values.length
  | [] => rfl
  | _ :: values => congrArg Nat.succ (Purelib.Data.List.Map.length_map function values)

/-- Mapping a retained concatenation concatenates the two mapped lists.

Structural recursion follows the original left spine and preserves every mapped
head. The unchanged right spine supplies the remaining mapped suffix, retaining
both lists' order and repeated occurrences. -/
public theorem map_append (function : Alpha → Beta) :
    ∀ left right : List Alpha,
      (left ++ right).map function = left.map function ++ right.map function
  | [], _ => rfl
  | head :: tail, right =>
      congrArg (List.cons (function head))
        (Purelib.Data.List.Map.map_append function tail right)

/-- Functions equal at every displayed list member have equal mapped lists.

Only entries actually appearing in the retained list need pointwise equality.
Structural recursion preserves their order and multiplicity. -/
public theorem map_congr_left {function other : Alpha → Beta} :
    ∀ {values : List Alpha},
      (∀ value ∈ values, function value = other value) →
        values.map function = values.map other
  | [], _ => rfl
  | value :: values, equal => by
      rw [List.map_cons, List.map_cons,
        equal value List.mem_cons_self,
        Purelib.Data.List.Map.map_congr_left (fun item member =>
          equal item (List.mem_cons_of_mem value member))]

/-- Membership in a finite map is witnessed by a displayed source member.

The witness retains its membership in the original list and the equality of
its mapped value with the target. Both directions follow the list constructors. -/
public theorem mem_map {function : Alpha → Beta} {target : Beta} :
    ∀ {values : List Alpha},
      target ∈ values.map function ↔
        ∃ source, source ∈ values ∧ function source = target
  | [] => by
      constructor
      · intro impossible
        nomatch impossible
      · rintro ⟨_, impossible, _⟩
        nomatch impossible
  | value :: values => by
      constructor
      · intro member
        cases member with
        | head => exact ⟨value, List.Mem.head values, rfl⟩
        | tail _ tail =>
          rcases (Purelib.Data.List.Map.mem_map (values := values)).mp tail with
            ⟨source, sourceMember, equal⟩
          exact ⟨source, List.Mem.tail value sourceMember, equal⟩
      · rintro ⟨source, sourceMember, equal⟩
        cases sourceMember with
        | head =>
          rw [← equal]
          exact List.Mem.head _
        | tail _ tail =>
          exact List.Mem.tail _ ((Purelib.Data.List.Map.mem_map (values := values)).mpr
            ⟨source, tail, equal⟩)

/-- Mapping a retained source member gives a member of the mapped list. -/
public theorem mem_map_of_mem {f : Alpha → Beta} {source : Alpha}
    {values : List Alpha} (member : source ∈ values) :
    f source ∈ values.map f :=
  Map.mem_map.mpr ⟨source, member, rfl⟩

/-- Mapping a finite list twice agrees with composing the two supplied functions.

Each original source entry is mapped in the same order through the two supplied
functions. Structural recursion retains the composed head and unchanged tail. -/
public theorem map_map (second : Beta → Gamma) (first : Alpha → Beta) :
    ∀ values : List Alpha,
      (values.map first).map second = values.map (second ∘ first)
  | [] => rfl
  | value :: values =>
      congrArg (List.cons (second (first value))) (map_map second first values)

/-- Mapping identity over a finite list leaves the list unchanged. -/
public theorem map_id {α : Type u} (values : List α) : values.map id = values := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

/-- Reading a mapped finite list returns the mapped value at the same bounded coordinate.

The supplied bounds certify the original and mapped coordinates separately.
Structural recursion follows the same coordinate and spine in both readbacks,
preserving the supplied function and original entry. -/
public theorem getElem_map (function : Alpha → Beta) (values : List Alpha)
    (index : Nat) (bound : index < values.length)
    (mappedBound : index < (values.map function).length) :
    (values.map function)[index]'mappedBound =
      function (values[index]'bound) := by
  induction values generalizing index with
  | nil => cases bound
  | cons head tail retained =>
      cases index with
      | zero => rfl
      | succ index =>
          exact retained index (Nat.lt_of_succ_lt_succ bound)
            (Nat.lt_of_succ_lt_succ mappedBound)

/-- Equal mapped lists retain equal values at every source occurrence.

Both maps read the same displayed source spine. Constructor equality identifies
its head values and tail maps, and membership selects the retained occurrence. -/
public theorem maps_pointwise {Item : Type u} {Value : Type v} (first second : Item → Value) :
    (items : List Item) → items.map first = items.map second → ∀ item ∈ items, first item = second item
  | [], _, _, member => by nomatch member
  | head :: tail, equal, item, member => by
      have parts := List.cons.inj equal
      cases member with
      | head => exact parts.1
      | tail _ member => exact maps_pointwise first second tail parts.2 item member

/-- Equal images identify two original list members when the mapped list has no duplicates.

Both inputs must occur in the original finite list. Structural induction uses
the distinct mapped head and retained tail to identify their original entries. -/
public theorem equal_of_map_unique {α β : Type} (map : α → β) {items : List α}
    (unique : (items.map map).Nodup) {first last : α} (firstMember : first ∈ items) (lastMember : last ∈ items)
    (equal : map first = map last) : first = last := by
  induction items with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      have parts := List.pairwise_cons.mp unique
      rcases Membership.mem_cons.mp firstMember with same | firstMember
      · subst first
        rcases Membership.mem_cons.mp lastMember with same | lastMember
        · exact same.symm
        · exact (parts.1 _ (Map.mem_map_of_mem lastMember) equal).elim
      · rcases Membership.mem_cons.mp lastMember with same | lastMember
        · subst last
          exact (parts.1 _ (Map.mem_map_of_mem firstMember) equal.symm).elim
        · exact ih parts.2 firstMember lastMember

/-- Mapping the retained prefix equals taking the same prefix of the mapped entries.

Both operations keep the original order and requested prefix count. Structural
recursion retains each mapped head and the exact original tail. -/
public theorem map_take (function : Alpha → Beta) (values : List Alpha) (count : Nat) :
    (values.take count).map function = (values.map function).take count := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih =>
      cases values with
      | nil => rfl
      | cons head tail => exact congrArg (List.cons (function head)) (ih tail)

/-- An injective entry map reflects equality of the two original retained lists.

Each pair of displayed heads is identified by the supplied injectivity witness.
Structural recursion then retains equality of the exact original tails. -/
public theorem map_inj_right {f : Alpha → Beta} (injective : Function.Injective f)
    {left right : List Alpha} : left.map f = right.map f ↔ left = right := by
  constructor
  · intro equal
    induction left generalizing right with
    | nil => cases right with
      | nil => rfl
      | cons head tail => cases equal
    | cons head tail ih => cases right with
      | nil => cases equal
      | cons other rest =>
          have parts := List.cons.inj equal
          have heads := injective parts.1
          have tails := ih parts.2
          cases heads
          cases tails
          rfl
  · intro equal
    cases equal
    rfl

end Purelib.Data.List.Map

namespace Purelib.Data.List.Map

/-- Mapping a retained list before Boolean search composes the test with its map.

The search visits each original mapped head and the same recursive tail. No
entry, ordering or Boolean acceptance decision is changed. -/
public theorem any_map {Item Label : Type} (map : Item → Label) (test : Label → Bool) (items : List Item) :
    (items.map map).any test = items.any (fun item => test (map item)) := by
  induction items with
  | nil => rfl
  | cons head tail ih => change (test (map head) || _) = (test (map head) || _); rw [ih]

end Purelib.Data.List.Map

namespace Purelib.Data.List.Map

/-- Mapping commutes with dropping an initial number of retained entries.

Both lists discard the same original heads and map the same remaining tail;
the original map and drop operations are unchanged. -/
public theorem map_drop {Alpha Beta : Type} (function : Alpha → Beta)
    (values : List Alpha) (count : Nat) :
    (values.drop count).map function = (values.map function).drop count := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih =>
      cases values with
      | nil => rfl
      | cons head tail => exact ih tail

end Purelib.Data.List.Map
