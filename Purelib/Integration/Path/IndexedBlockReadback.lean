module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Data.List.OfFn.Basic

import Purelib.Integration.Path.JoinedTrace

open Purelib

public section

/-! Transfer an exact ordered key spine to its cached payloads. Every payload
comparison uses its actual finite index; no enumeration or choice is inferred. -/
namespace Purelib.Integration.Path.IndexedBlockReadback

/-- Equal original key lists and coherent matching-key payloads give equal payload lists. -/
private theorem payloads_eq {Key Value : Type} (first last : List (Key × Value))
    (keys : first.map Prod.fst = last.map Prod.fst)
    (coherent : ∀ a ∈ first, ∀ b ∈ last, a.1 = b.1 → a.2 = b.2) :
    first.map Prod.snd = last.map Prod.snd := by
  induction first generalizing last with
  | nil =>
      cases last with
      | nil => rfl
      | cons head tail => cases keys
  | cons head tail ih =>
      cases last with
      | nil => cases keys
      | cons next rest =>
          have equal := List.cons.inj keys
          exact congrArg₂ List.cons (coherent head List.mem_cons_self next List.mem_cons_self equal.1)
            (ih rest equal.2 (fun a ha b hb => coherent a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)))

open Purelib.Data.List in
/-- Mapping flattened indexed blocks equals flattening the mapped original blocks. -/
private theorem map_blocks {α β : Type} {count : Nat} (blocks : Fin count → List α) (value : α → β) :
    ((List.ofFn blocks).flatten).map value =
      (List.ofFn (fun index => (blocks index).map value)).flatten := by
  rw [Data.List.Flatten.map_flatten, OfFn.Basic.map_ofFn]
  rfl

open Purelib.Data.List in
open Purelib.Integration.Path in
/-- Transport an exact indexed key decomposition to the corresponding coherent payload decomposition.

The supplied whole and piece owners remain distinct; matching original keys identify their payloads at retained indices.
-/
theorem ofFn_flatten {Key Value : Type} {count total : Nat} {sizes : Fin count → Nat}
    (keys : Fin total → Key) (values : Fin total → Value)
    (pieceKeys : (piece : Fin count) → Fin (sizes piece) → Key)
    (pieceValues : (piece : Fin count) → Fin (sizes piece) → Value)
    (spine : List.ofFn keys = (List.ofFn (fun piece => List.ofFn (pieceKeys piece))).flatten)
    (coherent : ∀ piece localIndex wholeIndex, pieceKeys piece localIndex = keys wholeIndex →
      pieceValues piece localIndex = values wholeIndex) :
    List.ofFn values = (List.ofFn (fun piece => List.ofFn (pieceValues piece))).flatten := by
  let whole := List.ofFn (fun index => (keys index, values index))
  let blocks := fun piece => List.ofFn (fun index => (pieceKeys piece index, pieceValues piece index))
  have wholeKeys : whole.map Prod.fst = List.ofFn keys := OfFn.Basic.map_ofFn
  have wholeValues : whole.map Prod.snd = List.ofFn values := OfFn.Basic.map_ofFn
  have blockKeys : ((List.ofFn blocks).flatten).map Prod.fst =
      (List.ofFn (fun piece => List.ofFn (pieceKeys piece))).flatten := by
    rw [IndexedBlockReadback.map_blocks]
    exact congrArg List.flatten (OfFn.Basic.ofFn_congr (fun piece => OfFn.Basic.map_ofFn))
  have blockValues : ((List.ofFn blocks).flatten).map Prod.snd =
      (List.ofFn (fun piece => List.ofFn (pieceValues piece))).flatten := by
    rw [IndexedBlockReadback.map_blocks]
    exact congrArg List.flatten (OfFn.Basic.ofFn_congr (fun piece => OfFn.Basic.map_ofFn))
  have equal := IndexedBlockReadback.payloads_eq whole (List.ofFn blocks).flatten
    (wholeKeys.trans (spine.trans blockKeys.symm)) (by
      intro a ha b hb same
      obtain ⟨wholeIndex, wholeEq⟩ := Data.List.OfFn.Basic.mem_ofFn.mp ha
      obtain ⟨block, blockMember, inBlock⟩ := Data.List.Flatten.block_of_member _ hb
      obtain ⟨piece, blockEq⟩ := Data.List.OfFn.Basic.mem_ofFn.mp blockMember
      rw [← blockEq] at inBlock
      obtain ⟨localIndex, localEq⟩ := Data.List.OfFn.Basic.mem_ofFn.mp inBlock
      cases wholeEq
      cases localEq
      exact (coherent piece localIndex wholeIndex same.symm).symm)
  exact wholeValues.symm.trans (equal.trans blockValues)

open Purelib.Data.List in
/-- Reading a list through its retained count-to-length equality reconstructs the original list. -/
theorem ofFn_get_cast {α : Type} (entries : List α) {count : Nat} (equal : count = entries.length) :
    List.ofFn (fun index : Fin count => entries[(Fin.cast equal index).val]'(Fin.cast equal index).isLt) = entries := by
  cases equal
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      rw [OfFn.Basic.ofFn_succ]
      exact congrArg (List.cons head) ih

end Purelib.Integration.Path.IndexedBlockReadback
