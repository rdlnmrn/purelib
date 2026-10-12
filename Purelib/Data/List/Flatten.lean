module
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.FilterMap

import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership

/-! Ordered flattening, flat-map composition and membership in finite list spines. -/

namespace Purelib.Data.List.Flatten

open Purelib.Data.List

universe u v w

/-- A rectangular finite table has the product of its two dimensions as its flattened length.

Each retained row enumerates all inner indices in their original order. Structural
recursion on the outer dimension adds exactly that inner dimension at each step. -/
public theorem length_flatten_ofFn {outer inner : Nat}
    (entries : Fin outer → Fin inner → Alpha) :
    ((List.ofFn fun row : Fin outer =>
      List.ofFn fun column : Fin inner => entries row column).flatten).length =
        outer * inner := by
  induction outer with
  | zero =>
      change 0 = 0 * inner
      exact (Nat.zero_mul inner).symm
  | succ outer inductionHypothesis =>
      rw [OfFn.Basic.ofFn_succ, List.flatten_cons,
        Append.length_append, OfFn.Basic.length_ofFn]
      rw [inductionHypothesis]
      rw [Nat.succ_mul]
      exact Nat.add_comm _ _

/-- Flattening two retained outer-list spines concatenates their original flattened words.

Every original inner list keeps its complete ordered entries. Structural recursion
on the left outer spine preserves those fibers and the unchanged right suffix. -/
public theorem flatten_append {Alpha : Type u} (left right : List (List Alpha)) :
    (left ++ right).flatten = left.flatten ++ right.flatten := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      exact (congrArg (List.append head) ih).trans
        (Append.append_assoc head tail.flatten right.flatten).symm

/-- A flat-map concatenates the head fiber with the unchanged tail flat-map.

The original list-valued function supplies both the head fiber and every tail
fiber. Their displayed concatenation retains order and repeated occurrences. -/
public theorem flatMap_cons {Alpha : Type u} {Beta : Type v}
    (function : Alpha → List Beta) (head : Alpha) (tail : List Alpha) :
    (head :: tail).flatMap function = function head ++ tail.flatMap function := rfl

/-- Flat-mapping a concatenation concatenates the two corresponding flat-maps.

The same retained list-valued function supplies both output spines. Structural
recursion preserves each original fiber, its order and repeated occurrences. -/
public theorem flatMap_append
    {Alpha : Type u} {Beta : Type v}
    (function : Alpha → List Beta) : ∀ left right : List Alpha,
    (left ++ right).flatMap function =
      left.flatMap function ++ right.flatMap function
  | [], _ => rfl
  | head :: tail, right => by
      change function head ++ (tail ++ right).flatMap function =
        (function head ++ tail.flatMap function) ++ right.flatMap function
      rw [Purelib.Data.List.Flatten.flatMap_append function tail right,
        Append.append_assoc]

/-- Mapping entries before flat-mapping reads the same fibers in the same order.

The original entry map supplies each retained fiber argument. Structural list
recursion compares the same head fiber and concatenates the unchanged tail.
-/
public theorem flatMap_map {Alpha : Type u} {Beta : Type v} {Gamma : Type w}
    (fiber : Beta → List Gamma) (entry : Alpha → Beta) :
    ∀ values : List Alpha,
      (values.map entry).flatMap fiber =
        values.flatMap (fun value => fiber (entry value))
  | [] => rfl
  | head :: tail => by
      change fiber (entry head) ++ (tail.map entry).flatMap fiber =
        fiber (entry head) ++ tail.flatMap (fun value => fiber (entry value))
      exact congrArg (List.append (fiber (entry head)))
        (flatMap_map fiber entry tail)

/-- Enumerating a fixed inner list for every outer entry gives the product of their
lengths.

Each retained outer occurrence contributes exactly one mapped inner list. Adding
those lengths preserves repetitions in both displayed spines. -/
public theorem length_flatMap_map
    {Outer Inner Result : Type}
    (outer : List Outer) (inner : List Inner) (f : Outer → Inner → Result) :
    (outer.flatMap fun left => inner.map (f left)).length =
      outer.length * inner.length := by
  induction outer with
  | nil => exact (Nat.zero_mul inner.length).symm
  | cons left remaining inductionHypothesis =>
      rw [Flatten.flatMap_cons, Append.length_append, Map.length_map,
        inductionHypothesis, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- Successive finite flat-maps equal one flat-map of the composite list-valued function.

The equality preserves the displayed output order and multiplicities and follows
structurally from flat-map distribution over append. -/
public theorem flatMap_assoc_direct
    {Alpha : Type u} {Beta : Type v} {Gamma : Type w}
    (first : Alpha → List Beta) (second : Beta → List Gamma) :
    ∀ values : List Alpha,
      (values.flatMap first).flatMap second =
        values.flatMap (fun value => (first value).flatMap second)
  | [] => rfl
  | head :: tail => by
      change (first head ++ tail.flatMap first).flatMap second =
        (first head).flatMap second ++
          tail.flatMap (fun value => (first value).flatMap second)
      rw [Flatten.flatMap_append second, flatMap_assoc_direct first second tail]

/-- Pointwise equal finite output lists give equal flat-maps on the displayed inputs.

Only members of the retained source list require an equality witness. The proof
compares resulting lists without equating the list-valued functions. -/
public theorem flatMap_congr_direct
    {Alpha : Type u} {Beta : Type v}
    (first second : Alpha → List Beta) : ∀ values : List Alpha,
    (∀ value, value ∈ values → first value = second value) →
      values.flatMap first = values.flatMap second
  | [], _ => rfl
  | head :: tail, equal => by
      change first head ++ tail.flatMap first =
        second head ++ tail.flatMap second
      rw [equal head List.mem_cons_self,
        flatMap_congr_direct first second tail (fun value member =>
          equal value (List.mem_cons_of_mem head member))]

/-- Membership in a finite flat-map is equivalent to a displayed source and inner
membership.

The witness retains both occurrence in the outer list and occurrence of the target in
that source's output list. -/
public theorem mem_flatMap {Alpha : Type u} {Beta : Type v} {function : Alpha → List Beta} {target : Beta} :
    ∀ {values : List Alpha},
      target ∈ values.flatMap function ↔
        ∃ source, source ∈ values ∧ target ∈ function source
  | [] => by
      constructor
      · intro impossible
        nomatch impossible
      · rintro ⟨_, impossible, _⟩
        nomatch impossible
  | value :: values => by
      change target ∈ function value ++ values.flatMap function ↔ _
      constructor
      · intro member
        rcases Membership.mem_append.mp member with head | tail
        · exact ⟨value, List.mem_cons_self, head⟩
        · rcases (mem_flatMap (values := values)).mp tail with
            ⟨source, sourceMember, targetMember⟩
          exact ⟨source, List.mem_cons_of_mem value sourceMember,
            targetMember⟩
      · rintro ⟨source, sourceMember, targetMember⟩
        cases sourceMember with
        | head => exact Membership.mem_append.mpr (Or.inl targetMember)
        | tail _ tail => exact Membership.mem_append.mpr (Or.inr
            ((mem_flatMap (values := values)).mpr
              ⟨source, tail, targetMember⟩))

end Purelib.Data.List.Flatten

namespace Purelib.Data.List

/-- An entry of a displayed member list belongs to the flattened outer list. -/
public theorem mem_flatten_of_mem {α : Type u} {value : α} {word : List α}
    {words : List (List α)} (outer : word ∈ words) (inner : value ∈ word) :
    value ∈ words.flatten := by
  induction words with
  | nil => cases outer
  | cons head rest ih =>
      cases outer with
      | head => exact Membership.mem_append.mpr (.inl inner)
      | tail _ member => exact Membership.mem_append.mpr (.inr (ih member))

end Purelib.Data.List

namespace Purelib.Data.List.Flatten

open Purelib.Data.List

/-- An original member list is no longer than the complete flattened list.

Membership selects its original head or tail block. The ordered concatenation
adds the remaining block lengths without changing the selected list. -/
public theorem length_le_flatten_of_mem {Item : Type u} {block : List Item} {blocks : List (List Item)}
    (member : block ∈ blocks) : block.length ≤ blocks.flatten.length := by
  induction blocks with
  | nil => cases member
  | cons first rest ih =>
    change block.length ≤ (first ++ rest.flatten).length
    rw [Append.length_append]
    rcases Membership.mem_cons.mp member with rfl | member
    · exact Nat.le_add_right block.length rest.flatten.length
    · exact Nat.le_trans (ih member) (Nat.le_add_left rest.flatten.length first.length)

end Purelib.Data.List.Flatten

namespace Purelib.Data.List.Flatten

open Purelib.Data.List

/-- A nested map over two fixed finite lists has length equal to the product of their
lengths.

Each retained outer occurrence contributes the entire mapped inner spine.
The output preserves both lists' multiplicities when adding the fiber lengths. -/
public theorem flatMap_map_length {Alpha Beta Gamma : Type*}
    (outer : List Alpha) (inner : List Beta)
    (function : Alpha → Beta → Gamma) :
    (outer.flatMap fun left => inner.map fun right => function left right).length =
      outer.length * inner.length := by
  induction outer with
  | nil =>
      change 0 = 0 * inner.length
      exact (Nat.zero_mul inner.length).symm
  | cons head tail inductionHypothesis =>
      rw [Flatten.flatMap_cons, Append.length_append, Map.length_map,
        inductionHypothesis, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- A flat-map with constant displayed fiber length has product length.

Every member of the retained outer list must produce exactly count entries. Repeated
outer members still contribute their full retained fibers. -/
public theorem flatMap_length_of_constant {Alpha Beta : Type*}
    (values : List Alpha) (fiber : Alpha → List Beta) (count : Nat)
    (fiberLength : ∀ value ∈ values, (fiber value).length = count) :
    (values.flatMap fiber).length = values.length * count := by
  induction values with
  | nil =>
      change 0 = 0 * count
      exact (Nat.zero_mul count).symm
  | cons head tail inductionHypothesis =>
      rw [Flatten.flatMap_cons, Append.length_append,
        fiberLength head List.mem_cons_self,
        inductionHypothesis (fun value member =>
          fiberLength value (List.mem_cons_of_mem head member)),
        List.length_cons, Nat.succ_mul, Nat.add_comm]

end Purelib.Data.List.Flatten

namespace Purelib.Data.List.Flatten

open Purelib.Data.List

/-- Mapping a flattened finite list maps each retained block before flattening.

Structural recursion preserves the original block order and every repeated
entry. The same entry map acts on the head block and unchanged tail blocks. -/
public theorem map_flatten {Item : Type u} {Result : Type v}
    (entry : Item → Result) (blocks : List (List Item)) :
    blocks.flatten.map entry = (blocks.map (List.map entry)).flatten := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
      change (head ++ tail.flatten).map entry = head.map entry ++ _
      rewrite [Map.map_append, ih]
      rfl

end Purelib.Data.List.Flatten

namespace Purelib.Data.List.Flatten

/-- Filtering the pairs of two finite lists produces at most their length product.

Each outer occurrence retains an optional-output filter of the same inner list. The bound accounts for every repeated
pair without changing either list. -/
public theorem length_flatMap_filterMap_le {Outer Inner Output : Type} (right : List Inner)
    (function : Outer → Inner → Option Output) :
    ∀ left : List Outer,
      (left.flatMap fun first => right.filterMap (function first)).length ≤ left.length * right.length
  | [] => by
      change 0 ≤ 0 * right.length
      rewrite [Nat.zero_mul]
      exact Nat.le_refl 0
  | first :: remaining => by
      rw [flatMap_cons, Append.length_append, List.length_cons, Nat.succ_mul]
      have headBound := FilterMap.length_filterMap_le (function first) right
      have tailBound := length_flatMap_filterMap_le right function remaining
      have bound := Nat.add_le_add headBound tailBound
      rw [Nat.add_comm right.length] at bound
      exact bound

/-- Flattening a retained three-level list equals flattening its original flattened blocks.

The outer spine keeps the same ordered blocks. The two associations concatenate exactly the same original entries. -/
public theorem flatten_flatten {Item : Type u} (blocks : List (List (List Item))) :
    blocks.flatten.flatten = (blocks.map List.flatten).flatten := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
      change (head ++ tail.flatten).flatten = head.flatten ++ (tail.map List.flatten).flatten
      rewrite [flatten_append, ih]
      exact Eq.refl _

end Purelib.Data.List.Flatten

namespace Purelib.Data.List.Flatten

open Purelib.Data.List

/-- An entry of flattened original blocks belongs to an original member block.

The displayed witness retains membership in the outer list and in the selected
block. Structural recursion preserves every original occurrence and its order. -/
public theorem block_of_member {α : Type} {entry : α} (blocks : List (List α))
    (member : entry ∈ blocks.flatten) : ∃ block ∈ blocks, entry ∈ block := by
  induction blocks with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      rcases Membership.mem_append.mp member with inHead | inTail
      · exact ⟨head, List.mem_cons_self, inHead⟩
      · obtain ⟨block, present, inside⟩ := ih inTail
        exact ⟨block, List.mem_cons_of_mem _ present, inside⟩

end Purelib.Data.List.Flatten

namespace Purelib.Data.List.Flatten

/-- Flat-mapping ordered entries equals flattening their original mapped blocks.

Both operations concatenate each displayed fiber before the same retained tail.
Structural recursion preserves the full block order and repeated occurrences. -/
public theorem flatMap_eq {Alpha Beta : Type} (entries : List Alpha) (value : Alpha → List Beta) :
    entries.flatMap value = (entries.map value).flatten := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.append (value head)) ih

end Purelib.Data.List.Flatten
