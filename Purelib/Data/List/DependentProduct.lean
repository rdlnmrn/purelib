module

import Purelib.Data.List.OfFn.Basic

/-!
# Retained products at bounded list occurrences

The original list supplies the occurrence indices, and each occurrence retains
its own entry type. The product uses `PUnit` and ordinary pairs, preserving the
entry family's universe and direct projection reduction. Materialization stores
each supplied entry once; lookup follows those stored pairs.
-/

public section

namespace Purelib.Data.List

universe u v w x

/-- A stored product with one dependent entry at each bounded original list occurrence.

The list and its original bounds determine the family. An empty list retains
`PUnit`; a nonempty list retains its zero-index entry and the successor-index
tail. Unlike an inductive spine, this representation stays in the entry
family's universe and reduces directly to ordinary product projections. -/
@[expose] def DependentProduct {α : Type u} :
    (items : List α) → (Fin items.length → Type v) → Type v
  | [], _ => PUnit
  | _ :: remaining, family => family 0 × DependentProduct remaining (fun index => family index.succ)

namespace DependentProduct

/-- Embed an original left occurrence in the literal appended list.

Structural recursion retains its original position. The empty prefix has no
left occurrence; a successor follows the same original prefix tail. -/
@[expose] def leftIndex {α : Type u} :
    (first second : List α) → Fin first.length → Fin (first ++ second).length
  | [], _, index => Fin.elim0 index
  | head :: remaining, second, index =>
      Fin.cases (⟨0, Nat.zero_lt_succ _⟩ : Fin ((head :: remaining) ++ second).length)
        (fun tail => (leftIndex remaining second tail).succ) index

/-- Embed an original right occurrence after the actual retained left prefix.

The empty left list returns the same bounded index. Each retained prefix
entry shifts that index once, preserving the original right occurrence. -/
@[expose] def rightIndex {α : Type u} :
    (first second : List α) → Fin second.length → Fin (first ++ second).length
  | [], _, index => index
  | _ :: remaining, second, index => (rightIndex remaining second index).succ

/-- Left occurrence embedding preserves its original natural coordinate. -/
theorem leftIndex_val {α : Type u} : (first second : List α) → (index : Fin first.length) →
    (leftIndex first second index).val = index.val
  | [], _, index => Fin.elim0 index
  | _ :: remaining, second, index => by
      refine Fin.cases (Eq.refl _) ?_ index
      intro tail
      exact congrArg Nat.succ (leftIndex_val remaining second tail)

/-- Right occurrence embedding uses exactly the original left-list length as its offset. -/
theorem rightIndex_val {α : Type u} : (first second : List α) → (index : Fin second.length) →
    (rightIndex first second index).val = first.length + index.val
  | [], _, index => (Nat.zero_add index.val).symm
  | _ :: remaining, second, index =>
      (congrArg Nat.succ (rightIndex_val remaining second index)).trans
        (Nat.succ_add remaining.length index.val).symm

/-- Distinct original left occurrences remain distinct after append. -/
theorem leftIndex_injective {α : Type u} (first second : List α) {left right : Fin first.length}
    (same : leftIndex first second left = leftIndex first second right) : left = right := by
  apply Fin.ext
  have values := congrArg Fin.val same
  rewrite [leftIndex_val, leftIndex_val] at values
  exact values

/-- Distinct original right occurrences remain distinct after append. -/
theorem rightIndex_injective {α : Type u} (first second : List α) {left right : Fin second.length}
    (same : rightIndex first second left = rightIndex first second right) : left = right := by
  apply Fin.ext
  have values := congrArg Fin.val same
  rewrite [rightIndex_val, rightIndex_val] at values
  exact Nat.add_left_cancel values

/-- Left and right original occurrences retain disjoint appended positions. -/
theorem leftIndex_ne_rightIndex {α : Type u} (first second : List α)
    (left : Fin first.length) (right : Fin second.length) :
    leftIndex first second left ≠ rightIndex first second right := by
  intro same
  have values := congrArg Fin.val same
  rewrite [leftIndex_val, rightIndex_val] at values
  have before := left.isLt
  rewrite [values] at before
  exact Nat.not_lt_of_ge (Nat.le_add_right first.length right.val) before

/-- Append two original bounded coordinate functions without changing either supplied suffix.

The empty prefix returns the same right function. A nonempty prefix retains
its actual first value and recurses on its original successor coordinates.
-/
@[expose] def appendFn {α : Type u} {β : Sort w} :
    (first second : List α) → (Fin first.length → β) → (Fin second.length → β) →
      Fin (first ++ second).length → β
  | [], _, _, right => right
  | _ :: remaining, second, left, right =>
      Fin.cases (left 0) (appendFn remaining second (fun index => left index.succ) right)

/-- Appended coordinates return the same whole original left value at its shared bounded embedding. -/
theorem appendFn_left {α : Type u} {β : Sort w} : (first second : List α) →
    (left : Fin first.length → β) → (right : Fin second.length → β) → (index : Fin first.length) →
      appendFn first second left right (leftIndex first second index) = left index
  | [], _, _, _, index => Fin.elim0 index
  | _ :: remaining, second, left, right, index => by
      refine Fin.cases (Eq.refl _) ?_ index
      intro tail
      exact appendFn_left remaining second (fun index => left index.succ) right tail

/-- Appended coordinates return the same whole original right value at its shared bounded embedding. -/
theorem appendFn_right {α : Type u} {β : Sort w} : (first second : List α) →
    (left : Fin first.length → β) → (right : Fin second.length → β) → (index : Fin second.length) →
      appendFn first second left right (rightIndex first second index) = right index
  | [], _, _, _, _ => rfl
  | _ :: remaining, second, left, right, index =>
      appendFn_right remaining second (fun index => left index.succ) right index

/-- Append actual stored products indexed by supplied original bounded coordinate values.

The family may depend on an actual interpreted channel rather than only the
underlying list item. Each actual left entry is retained literally; the empty
left tail returns the same supplied right product. No table or entry is rebuilt.
-/
@[expose] def append {α : Type u} {β : Sort w} (family : β → Type v) :
    (first second : List α) → (leftValues : Fin first.length → β) → (rightValues : Fin second.length → β) →
    DependentProduct first (fun index => family (leftValues index)) →
    DependentProduct second (fun index => family (rightValues index)) →
    DependentProduct (first ++ second) (fun index => family (appendFn first second leftValues rightValues index))
  | [], _, _, _, _, right => right
  | _ :: remaining, second, leftValues, rightValues, left, right =>
      (left.1, append family remaining second (fun index => leftValues index.succ) rightValues left.2 right)

/-- An empty left product returns the identical supplied right cache under its original coordinate function. -/
theorem append_nil {α : Type u} {β : Sort w} (family : β → Type v) (second : List α)
    (leftValues : Fin ([] : List α).length → β) (rightValues : Fin second.length → β)
    (left : DependentProduct [] (fun index => family (leftValues index)))
    (right : DependentProduct second (fun index => family (rightValues index))) :
    append family [] second leftValues rightValues left right = right := rfl

/-- Nonempty append retains the same actual first entry and recursively attached original tail. -/
theorem append_cons {α : Type u} {β : Sort w} (family : β → Type v) (head : α) (remaining second : List α)
    (leftValues : Fin (head :: remaining).length → β) (rightValues : Fin second.length → β)
    (left : DependentProduct (head :: remaining) (fun index => family (leftValues index)))
    (right : DependentProduct second (fun index => family (rightValues index))) :
    append family (head :: remaining) second leftValues rightValues left right =
      (left.1, append family remaining second (fun index => leftValues index.succ) rightValues left.2 right) := rfl

/-- Pointwise equal finite entry types determine the same whole original dependent-product type. -/
theorem family_eq {α : Type u} : (items : List α) → {first second : Fin items.length → Type v} →
    (∀ index, first index = second index) → DependentProduct items first = DependentProduct items second
  | [], _, _, _ => rfl
  | _ :: remaining, first, second, same =>
      (congrArg (fun head => head × DependentProduct remaining (fun index => first index.succ)) (same 0)).trans
        (congrArg (Prod (second 0)) (family_eq remaining (fun index => same index.succ)))

/-- Transport the literal complete original product through its finite pointwise entry-type identities. -/
@[expose] def transport {α : Type u} (items : List α) {first second : Fin items.length → Type v}
    (same : ∀ index, first index = second index) (entries : DependentProduct items first) :
    DependentProduct items second := cast (family_eq items same) entries

/-- Casting a product transports its same actual head and tail through the supplied scalar type identities. -/
private theorem cast_pair {α β γ δ : Type v} (first : α = γ) (second : β = δ) (entries : α × β) :
    cast ((congrArg (fun head => head × β) first).trans (congrArg (Prod γ) second)) entries =
      (cast first entries.1, cast second entries.2) := by
  cases first
  cases second
  rfl

/-- Finite-family transport retains the same empty original product. -/
theorem transport_nil {α : Type u} {first second : Fin ([] : List α).length → Type v}
    (same : ∀ index, first index = second index) (entries : DependentProduct [] first) :
    transport [] same entries = entries := rfl

/-- Finite-family transport casts the same actual head and original tail without producing replacement entries. -/
theorem transport_cons {α : Type u} (head : α) (remaining : List α)
    {first second : Fin (head :: remaining).length → Type v}
    (same : ∀ index, first index = second index) (entries : DependentProduct (head :: remaining) first) :
    transport (head :: remaining) same entries =
      (cast (same 0) entries.1, transport remaining (fun index => same index.succ) entries.2) :=
  cast_pair (same 0) (family_eq remaining (fun index => same index.succ)) entries

/-- Read the exact stored entry at its original bounded list occurrence.

The lookup follows the retained product tail and finite index without invoking
the original entry producer or changing the index-dependent entry type. -/
@[expose] def get {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} → DependentProduct items family →
      (index : Fin items.length) → family index
  | [], _, _, index => Fin.elim0 index
  | _ :: remaining, _, entries, index => Fin.cases entries.1 (fun tail => get remaining entries.2 tail) index

/-- Appended left lookup returns the same complete original dependent entry at its actual coordinate. -/
theorem get_append_left {α : Type u} {β : Sort w} (family : β → Type v) :
    (first second : List α) → (leftValues : Fin first.length → β) → (rightValues : Fin second.length → β) →
    (left : DependentProduct first (fun index => family (leftValues index))) →
    (right : DependentProduct second (fun index => family (rightValues index))) → (index : Fin first.length) →
    HEq (get (first ++ second) (append family first second leftValues rightValues left right)
      (leftIndex first second index)) (get first left index)
  | [], _, _, _, _, _, index => Fin.elim0 index
  | _ :: remaining, second, leftValues, rightValues, left, right, index => by
      refine Fin.cases (HEq.refl _) ?_ index
      intro tail
      exact get_append_left family remaining second (fun index => leftValues index.succ) rightValues left.2 right tail

/-- Appended right lookup returns the same complete original entry from the literal supplied suffix. -/
theorem get_append_right {α : Type u} {β : Sort w} (family : β → Type v) :
    (first second : List α) → (leftValues : Fin first.length → β) → (rightValues : Fin second.length → β) →
    (left : DependentProduct first (fun index => family (leftValues index))) →
    (right : DependentProduct second (fun index => family (rightValues index))) → (index : Fin second.length) →
    HEq (get (first ++ second) (append family first second leftValues rightValues left right)
      (rightIndex first second index)) (get second right index)
  | [], _, _, _, _, _, _ => HEq.refl _
  | _ :: remaining, second, leftValues, rightValues, left, right, index =>
      get_append_right family remaining second (fun index => leftValues index.succ) rightValues left.2 right index

/-- A transported finite product lookup retains its same complete actual original entry. -/
theorem get_transport {α : Type u} : (items : List α) → {first second : Fin items.length → Type v} →
    (same : ∀ index, first index = second index) → (entries : DependentProduct items first) →
    (index : Fin items.length) → HEq (get items (transport items same entries) index) (get items entries index)
  | [], _, _, _, _, index => Fin.elim0 index
  | head :: remaining, _, _, same, entries, index => by
      rewrite [transport_cons]
      refine Fin.cases ?_ ?_ index
      · exact cast_heq (same 0) entries.1
      · intro tail
        exact get_transport remaining (fun index => same index.succ) entries.2 tail

/-- Replace one original bounded entry, retaining every other stored entry and the selected literal tail.

At the selected occurrence the new entry is paired with the unchanged original
tail. Earlier occurrences retain their actual cached entries; recursion follows
the same successor-index family without raising its universe.
-/
@[expose] def replace {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} → DependentProduct items family →
      (index : Fin items.length) → family index → DependentProduct items family
  | [], _, _, index, _ => Fin.elim0 index
  | _ :: remaining, _, entries, index, entry =>
      Fin.cases (fun value => (value, entries.2))
        (fun tail value => (entries.1, replace remaining entries.2 tail value)) index entry

/-- Lookup at the replaced original bounded occurrence returns the same supplied dependent entry. -/
theorem get_same {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
    (entries : DependentProduct items family) → (index : Fin items.length) → (entry : family index) →
      get items (replace items entries index entry) index = entry
  | [], _, _, index, _ => Fin.elim0 index
  | _ :: remaining, _, entries, index, entry => by
      revert entry
      refine Fin.cases (fun _ => rfl) ?_ index
      intro tail entry
      exact get_same remaining entries.2 tail entry

/-- Lookup at every other original bounded occurrence returns its unchanged actual cached entry. -/
theorem get_other {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
    (entries : DependentProduct items family) → (index : Fin items.length) → (entry : family index) →
    (other : Fin items.length) → other ≠ index →
      get items (replace items entries index entry) other = get items entries other
  | [], _, _, index, _, _, _ => Fin.elim0 index
  | _ :: remaining, _, entries, index, entry, other, different => by
      revert entry other
      refine Fin.cases ?_ ?_ index
      · intro entry other different
        revert different
        refine Fin.cases ?_ ?_ other
        · intro different
          exact False.elim (different rfl)
        · intro _ _
          rfl
      · intro tail entry other different
        revert different
        refine Fin.cases ?_ ?_ other
        · intro _
          rfl
        · intro later different
          exact get_other remaining entries.2 tail entry later
            (fun same => different (congrArg Fin.succ same))

/-- Materialize each original bounded occurrence's supplied entry exactly once.

The head stores the original zero-index entry. Recursion stores the remaining
entries under their original successor indices, with no function retained in
place of the supplied data. -/
@[expose] def ofFn {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
      ((index : Fin items.length) → family index) → DependentProduct items family
  | [], _, _ => PUnit.unit
  | _ :: remaining, _, entries => (entries 0, ofFn remaining (fun index => entries index.succ))

/-- Materialize checked retained dependent entries in their original order inside a monadic procedure.

Each returned entry carries equality to its original constructor. The stored
product consumes those actual returned values and retains complete agreement
with ordinary materialization, without evaluating the original constructors.
-/
@[expose] def ofFnM {α : Type u} {m : Type v → Type w} [Monad m] :
    (items : List α) → {family : Fin items.length → Type v} →
      (entries : (index : Fin items.length) → family index) →
      ((index : Fin items.length) → m {entry : family index // entry = entries index}) →
      m {stored : DependentProduct items family // stored = ofFn items entries}
  | [], _, _, _ => pure ⟨PUnit.unit, rfl⟩
  | _ :: remaining, _, entries, load => do
    let first ← load 0
    let rest ← ofFnM remaining (fun index => entries index.succ) (fun index => load index.succ)
    return ⟨(first.val, rest.val),
      (congrArg (fun entry => (entry, rest.val)) first.property).trans
        (congrArg (fun tail => (entries 0, tail)) rest.property)⟩

/-- Lookup after materialization returns the same original supplied dependent entry. -/
theorem get_ofFn {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
    (entries : (index : Fin items.length) → family index) → (index : Fin items.length) →
      get items (ofFn items entries) index = entries index
  | [], _, _, index => Fin.elim0 index
  | _ :: remaining, _, entries, index => by
      refine Fin.cases (Eq.refl _) ?_ index
      intro tail
      exact get_ofFn remaining (fun index => entries index.succ) tail

/-- Retain an actual supplied list under another original list's equal-count occurrence indices.

The entry universe is unchanged. Structural recursion forwards the actual
value head and literal value tail; the original index list drives the
same finite product shape. No bounded lookup or entry factory is executed.
-/
@[expose] def ofList {α : Type u} {β : Type v} :
    (items : List α) → (values : List β) → values.length = items.length →
      DependentProduct items (fun _ => β)
  | [], [], _ => PUnit.unit
  | [], _ :: _, same => by cases same
  | _ :: _, [], same => by cases same
  | _ :: remaining, value :: values, same =>
      (value, ofList remaining values (Nat.succ.inj same))

/-- The whole retained-list product equals original materialization on those same supplied values.

This exact equality includes every original entry and literal product tail.
The lookup function occurs only in the specification; the executable
retained-list constructor traverses the actual two lists directly.
-/
theorem ofList_eq_ofFn {α : Type u} {β : Type v} :
    (items : List α) → (values : List β) → (same : values.length = items.length) →
      ofList items values same =
        ofFn items (fun index => values[index.val]'(same.symm ▸ index.isLt))
  | [], [], _ => rfl
  | [], _ :: _, same => by cases same
  | _ :: _, [], same => by cases same
  | _ :: remaining, value :: values, same => by
      exact congrArg (fun tail : DependentProduct remaining (fun _ => β) => (value, tail))
        (ofList_eq_ofFn remaining values (Nat.succ.inj same))

/-- Bounded lookup reads the same whole original value at its unchanged ordinal.

The original materialization readback and whole retained-list equality
identify the supplied cache value; no component equality or replacement
entry is used to recover it.
-/
theorem get_ofList {α : Type u} {β : Type v} (items : List α) (values : List β)
    (same : values.length = items.length) (index : Fin items.length) :
    get items (ofList items values same) index = values[index.val]'(same.symm ▸ index.isLt) := by
  rewrite [ofList_eq_ofFn items values same]
  exact get_ofFn items (fun index => values[index.val]'(same.symm ▸ index.isLt)) index

/-- Map each actual retained entry to data indexed by that same whole entry.

The result keeps the original bounded occurrences and their exact stored
parents. Structural recursion passes the supplied product tail unchanged;
no lookup or producer is rerun while building another entry.
-/
@[expose] def map {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
    (entries : DependentProduct items family) →
    (result : (index : Fin items.length) → family index → Type w) →
    ((index : Fin items.length) → (entry : family index) → result index entry) →
      DependentProduct items (fun index => result index (get items entries index))
  | [], _, _, _, _ => PUnit.unit
  | _ :: remaining, _, entries, result, mapped =>
      (mapped 0 entries.1, map remaining entries.2
        (fun index entry => result index.succ entry) (fun index entry => mapped index.succ entry))

/-- Reading a dependent map returns the actual mapped whole entry at its unchanged bounded occurrence. -/
theorem get_map {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
    (entries : DependentProduct items family) →
    (result : (index : Fin items.length) → family index → Type w) →
    (mapped : (index : Fin items.length) → (entry : family index) → result index entry) →
    (index : Fin items.length) →
      get items (map items entries result mapped) index = mapped index (get items entries index)
  | [], _, _, _, _, index => Fin.elim0 index
  | _ :: remaining, _, entries, result, mapped, index => by
      refine Fin.cases (Eq.refl _) ?_ index
      intro tail
      exact get_map remaining entries.2 (fun index entry => result index.succ entry)
        (fun index entry => mapped index.succ entry) tail

/-- Combine two actual original dependent banks at their same bounded occurrences in one structural traversal.

The mapper receives both complete original entries and their whole lookup
identities. Those identities can transport existing nominal indices in
proofs; executable construction consumes the supplied heads and literal
tails directly. The result family has its own independent universe.
-/
@[expose] def zipWith {α : Type u} :
    (items : List α) → {leftFamily : Fin items.length → Type v} →
    {rightFamily : Fin items.length → Type w} →
    (left : DependentProduct items leftFamily) → (right : DependentProduct items rightFamily) →
    (result : Fin items.length → Type x) →
    ((index : Fin items.length) → (first : leftFamily index) → (last : rightFamily index) →
      first = get items left index → last = get items right index → result index) →
      DependentProduct items result
  | [], _, _, _, _, _, _ => PUnit.unit
  | _ :: remaining, _, _, left, right, result, mapped =>
      (mapped ⟨0, Nat.zero_lt_succ _⟩ left.1 right.1 rfl rfl,
        zipWith remaining left.2 right.2 (fun index => result index.succ)
          (fun index first last sameFirst sameLast => mapped index.succ first last sameFirst sameLast))

/-- Reading the paired structural map returns the mapper at the same two whole original entries and bounded index. -/
theorem get_zipWith {α : Type u} :
    (items : List α) → {leftFamily : Fin items.length → Type v} →
    {rightFamily : Fin items.length → Type w} →
    (left : DependentProduct items leftFamily) → (right : DependentProduct items rightFamily) →
    (result : Fin items.length → Type x) →
    (mapped : (index : Fin items.length) → (first : leftFamily index) → (last : rightFamily index) →
      first = get items left index → last = get items right index → result index) →
    (index : Fin items.length) →
      get items (zipWith items left right result mapped) index =
        mapped index (get items left index) (get items right index) rfl rfl
  | [], _, _, _, _, _, _, index => Fin.elim0 index
  | _ :: remaining, _, _, left, right, result, mapped, index => by
      refine Fin.cases (Eq.refl _) ?_ index
      intro tail
      exact get_zipWith remaining left.2 right.2 (fun index => result index.succ)
        (fun index first last sameFirst sameLast => mapped index.succ first last sameFirst sameLast) tail

/-- Map the actual stored dependent entries into a list in their original occurrence order.

Structural recursion consumes each supplied head and literal tail once.
The mapper receives the unchanged bounded source index and its whole
stored dependent entry; it never invokes the original entry producer.
-/
@[expose] def mapToList {α : Type u} {β : Type w} :
    (items : List α) → {family : Fin items.length → Type v} → DependentProduct items family →
      ((index : Fin items.length) → family index → β) → List β
  | [], _, _, _ => []
  | _ :: remaining, _, entries, mapped =>
      mapped 0 entries.1 :: mapToList remaining entries.2 (fun index value => mapped index.succ value)

/-- A scalar list map consumes the same stored dependent entries in their original order.

The second operation is applied to each retained mapped value. Neither
side invokes an entry producer or changes the original bounded indices.
-/
theorem map_mapToList {α : Type u} {β : Type w} {γ : Type x} :
    (items : List α) → {family : Fin items.length → Type v} →
    (entries : DependentProduct items family) →
    (first : (index : Fin items.length) → family index → β) → (second : β → γ) →
      (mapToList items entries first).map second =
        mapToList items entries (fun index entry => second (first index entry))
  | [], _, _, _, _ => rfl
  | _ :: remaining, _, entries, first, second =>
      congrArg (List.cons (second (first 0 entries.1)))
        (map_mapToList remaining entries.2 (fun index entry => first index.succ entry) second)

/-- An item-only mapping of the actual stored product reads the same original list in its unchanged order.

The entry family, stored head and literal tail remain the supplied ones.
When the mapper consumes only the bounded original item, structural
recursion gives the ordinary map without invoking an entry producer.
-/
theorem mapToList_items {α : Type u} {β : Type w} :
    (items : List α) → {family : Fin items.length → Type v} →
    (entries : DependentProduct items family) → (mapped : α → β) →
      mapToList items entries (fun index _entry => mapped (items[index.val]'index.isLt)) = items.map mapped
  | [], _, _, _ => rfl
  | _ :: remaining, _, entries, mapped =>
      congrArg (List.cons (mapped _)) (mapToList_items remaining entries.2 mapped)

/-- Mapping the stored dependent entries preserves exactly the original occurrence count. -/
theorem length_mapToList {α : Type u} {β : Type w} :
    (items : List α) → {family : Fin items.length → Type v} →
    (entries : DependentProduct items family) →
    (mapped : (index : Fin items.length) → family index → β) →
      (mapToList items entries mapped).length = items.length
  | [], _, _, _ => rfl
  | _ :: remaining, _, entries, mapped =>
      congrArg Nat.succ (length_mapToList remaining entries.2 (fun index value => mapped index.succ value))

/-- Reading a mapped occurrence consumes its exact original bounded index and whole stored entry. -/
theorem get_mapToList {α : Type u} {β : Type w} :
    (items : List α) → {family : Fin items.length → Type v} →
    (entries : DependentProduct items family) →
    (mapped : (index : Fin items.length) → family index → β) →
    (index : Fin items.length) →
      (mapToList items entries mapped)[index.val]'((length_mapToList items entries mapped).symm ▸ index.isLt) =
        mapped index (get items entries index)
  | [], _, _, _, index => Fin.elim0 index
  | _ :: remaining, _, entries, mapped, index => by
      refine Fin.cases (Eq.refl _) ?_ index
      intro tail
      exact get_mapToList remaining entries.2 (fun index value => mapped index.succ value) tail

/-- Split the actual stored product at its literal original list concatenation.

The two returned products retain the original bounded left and right
coordinate families. Each prefix entry is copied as the same complete
value; the terminal right product is the unchanged supplied cache.
-/
@[expose] def split {α : Type u} :
    (first second : List α) → {family : Fin (first ++ second).length → Type v} →
    DependentProduct (first ++ second) family →
      DependentProduct first (fun index => family (leftIndex first second index)) ×
        DependentProduct second (fun index => family (rightIndex first second index))
  | [], _, _, entries => ⟨PUnit.unit, entries⟩
  | _ :: remaining, second, _, entries =>
      let rest := split remaining second entries.2
      ⟨⟨entries.1, rest.1⟩, rest.2⟩

/-- Splitting an empty prefix returns the literal original whole right cache. -/
theorem split_nil {α : Type u} (second : List α) {family : Fin second.length → Type v}
    (entries : DependentProduct second family) : split [] second entries = ⟨PUnit.unit, entries⟩ := rfl

/-- The split left product reads the same complete original entry at its retained left embedding. -/
theorem get_split_left {α : Type u} :
    (first second : List α) → {family : Fin (first ++ second).length → Type v} →
    (entries : DependentProduct (first ++ second) family) → (index : Fin first.length) →
      get first (split first second entries).1 index = get (first ++ second) entries (leftIndex first second index)
  | [], _, _, _, index => Fin.elim0 index
  | _ :: remaining, second, _, entries, index => by
      refine Fin.cases (Eq.refl _) ?_ index
      intro tail
      exact get_split_left remaining second entries.2 tail

/-- The split right product reads the same whole original entry from the literal retained suffix. -/
theorem get_split_right {α : Type u} :
    (first second : List α) → {family : Fin (first ++ second).length → Type v} →
    (entries : DependentProduct (first ++ second) family) → (index : Fin second.length) →
      get second (split first second entries).2 index = get (first ++ second) entries (rightIndex first second index)
  | [], _, _, _, _ => rfl
  | _ :: remaining, second, _, entries, index => get_split_right remaining second entries.2 index

/-- Mapping the original bank is the concatenation of its same actual split entries in original order.

Each mapper receives the unchanged original bounded position and complete
entry. Structural recursion follows only the supplied prefix and literal
right tail; neither bank nor mapped entry is produced again.
-/
theorem mapToList_split {α : Type u} {β : Type w} :
    (first second : List α) → {family : Fin (first ++ second).length → Type v} →
    (entries : DependentProduct (first ++ second) family) →
    (mapped : (index : Fin (first ++ second).length) → family index → β) →
      mapToList (first ++ second) entries mapped =
        mapToList first (split first second entries).1
          (fun index entry => mapped (leftIndex first second index) entry) ++
        mapToList second (split first second entries).2
          (fun index entry => mapped (rightIndex first second index) entry)
  | [], _, _, _, _ => rfl
  | _ :: remaining, second, _, entries, mapped =>
      congrArg (List.cons (mapped ⟨0, Nat.zero_lt_succ _⟩ entries.1))
        (mapToList_split remaining second entries.2 (fun index entry => mapped index.succ entry))

/-- Pointwise equality of stored lookups identifies the whole original finite product.

Structural recursion compares each actual head and remaining product.
No function extensionality or replacement producer is used.
-/
theorem eq_of_get {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
    (first second : DependentProduct items family) →
    (∀ index, get items first index = get items second index) → first = second
  | [], _, first, second, _ => by cases first; cases second; rfl
  | _ :: remaining, _, first, second, same =>
      (congrArg (fun head => (head, first.2)) (same ⟨0, Nat.zero_lt_succ _⟩)).trans
        (congrArg (Prod.mk second.1)
          (eq_of_get remaining first.2 second.2 (fun index => same index.succ)))

/-- Mapping a family transport consumes the same actual entries through their supplied exact type equalities. -/
theorem mapToList_transport {α : Type u} {β : Type w} :
    (items : List α) → {first second : Fin items.length → Type v} →
    (same : ∀ index, first index = second index) → (entries : DependentProduct items first) →
    (mapped : (index : Fin items.length) → second index → β) →
      mapToList items (transport items same entries) mapped =
        mapToList items entries (fun index entry => mapped index (cast (same index) entry))
  | [], _, _, _, _, _ => rfl
  | head :: remaining, _, _, same, entries, mapped => by
      rewrite [transport_cons]
      exact congrArg (List.cons (mapped 0 (cast (same 0) entries.1)))
        (mapToList_transport remaining (fun index => same index.succ) entries.2
          (fun index entry => mapped index.succ entry))

/-- A pointwise property of the mapped retained entries holds at every occurrence in their ordered output list.

The predicate is supplied on each actual bounded mapper application.
Structural membership follows the same retained head and tail; the
original dependent family and its universe remain unchanged.
-/
theorem mapToList_all {α : Type u} {β : Type w} :
    (items : List α) → {family : Fin items.length → Type v} → (entries : DependentProduct items family) →
    (mapped : (index : Fin items.length) → family index → β) → {predicate : β → Prop} →
    (∀ index entry, predicate (mapped index entry)) → ∀ value ∈ mapToList items entries mapped, predicate value
  | [], _, _, _, _, _, _, impossible => nomatch impossible
  | _ :: remaining, _, entries, mapped, _, property, value, member => by
      cases member with
      | head => exact property ⟨0, Nat.zero_lt_succ _⟩ entries.1
      | tail _ selected =>
          exact mapToList_all remaining entries.2 (fun index entry => mapped index.succ entry)
            (fun index entry => property index.succ entry) value selected

/-- Pointwise agreement of the mapped actual entries identifies their complete ordered output lists. -/
theorem mapToList_congr {α : Type u} {β : Type w} :
    (items : List α) → {family : Fin items.length → Type v} → (entries : DependentProduct items family) →
    (first second : (index : Fin items.length) → family index → β) →
    (∀ index entry, first index entry = second index entry) →
      mapToList items entries first = mapToList items entries second
  | [], _, _, _, _, _ => rfl
  | _ :: remaining, _, entries, first, second, same =>
      (congrArg (fun head => head :: mapToList remaining entries.2
        (fun index entry => first index.succ entry)) (same ⟨0, Nat.zero_lt_succ _⟩ entries.1)).trans
        (congrArg (List.cons (second ⟨0, Nat.zero_lt_succ _⟩ entries.1))
          (mapToList_congr remaining entries.2 (fun index entry => first index.succ entry)
            (fun index entry => second index.succ entry) (fun index entry => same index.succ entry)))

/-- Agreement of mapped whole-entry lookups identifies ordered maps of two original dependent products.

The two original families and products remain distinct. Structural recursion
consumes their actual heads and unchanged tails at the same bounded list
occurrences; it introduces no function equality or reconstructed product.
-/
theorem mapToList_eq_of_get {α : Type u} {β : Type w} :
    (items : List α) → {firstFamily : Fin items.length → Type v} →
    {secondFamily : Fin items.length → Type x} →
    (first : DependentProduct items firstFamily) → (second : DependentProduct items secondFamily) →
    (firstMap : (index : Fin items.length) → firstFamily index → β) →
    (secondMap : (index : Fin items.length) → secondFamily index → β) →
    (∀ index, firstMap index (get items first index) = secondMap index (get items second index)) →
      mapToList items first firstMap = mapToList items second secondMap
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: remaining, _, _, first, second, firstMap, secondMap, same =>
      (congrArg (fun head => head :: mapToList remaining first.2
        (fun index entry => firstMap index.succ entry)) (same ⟨0, Nat.zero_lt_succ _⟩)).trans
        (congrArg (List.cons (secondMap ⟨0, Nat.zero_lt_succ _⟩ second.1))
          (mapToList_eq_of_get remaining first.2 second.2
            (fun index entry => firstMap index.succ entry)
            (fun index entry => secondMap index.succ entry) (fun index => same index.succ)))

/-- Transport the entire original dependent product to the same retained list under a supplied list equality.

The original entry family still reads the same natural values and original
bounds. An optional exact family equality can also retain item-dependent
indices. Equality elimination returns the whole supplied bank literally,
without visiting, replacing or constructing any of its retained entries.
-/
@[expose] def castItems {α : Type u} {items actual : List α}
    (equal : actual = items) {family : Fin items.length → Type v}
    (entries : DependentProduct items family)
    (resultFamily : Fin actual.length → Type v :=
      fun index => family ⟨index.val, by rewrite [← equal]; exact index.isLt⟩)
    (sameFamily : (fun index => family ⟨index.val, by rewrite [← equal]; exact index.isLt⟩) = resultFamily := by rfl) :
    DependentProduct actual resultFamily := by
  cases equal
  cases sameFamily
  exact entries

/-- Reflexive list transport returns the complete original dependent product. -/
theorem castItems_self {α : Type u} {items : List α} {family : Fin items.length → Type v}
    (entries : DependentProduct items family) : castItems rfl entries = entries := (rfl)

/-- Reading a transported product consumes the same complete original entry at its unchanged bounded natural index. -/
theorem get_castItems {α : Type u} {items actual : List α}
    (equal : actual = items) {family : Fin items.length → Type v}
    (entries : DependentProduct items family) (index : Fin actual.length) :
    get actual (castItems equal entries) index =
      get items entries ⟨index.val, by rewrite [← equal]; exact index.isLt⟩ := by
  cases equal
  rfl

/-- Pointwise equality of retained entries identifies the same materialized dependent product spine. -/
theorem ofFn_congr {α : Type u} (items : List α) {family : Fin items.length → Type v}
    (first second : (index : Fin items.length) → family index)
    (equal : ∀ index, first index = second index) : ofFn items first = ofFn items second :=
  eq_of_get items (ofFn items first) (ofFn items second) (fun index =>
    (get_ofFn items first index).trans ((equal index).trans (get_ofFn items second index).symm))

/-- Sum natural weights of the actual stored entries in original list order.

The fold follows the retained product spine. Each weight consumes its same
stored entry and original bounded occurrence without rebuilding that entry. -/
@[expose] def sum {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
      ((index : Fin items.length) → family index → Nat) → DependentProduct items family → Nat
  | [], _, _, _ => 0
  | _ :: remaining, _, weight, entries =>
      weight 0 entries.1 + sum remaining (fun index => weight index.succ) entries.2

/-- Pointwise equal weights on the same stored entries give equal natural sums. -/
theorem sum_congr {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
      (entries : DependentProduct items family) →
      (first last : (index : Fin items.length) → family index → Nat) →
      (∀ index, first index (get items entries index) = last index (get items entries index)) →
      sum items first entries = sum items last entries
  | [], _, _, _, _, _ => rfl
  | _ :: remaining, _, entries, first, last, same => by
      change first 0 entries.1 + sum remaining (fun index => first index.succ) entries.2 =
        last 0 entries.1 + sum remaining (fun index => last index.succ) entries.2
      have tail := sum_congr remaining entries.2 (fun index => first index.succ) (fun index => last index.succ)
        (fun index => same index.succ)
      exact (congrArg (fun value => value + sum remaining (fun index => first index.succ) entries.2) (same 0)).trans
        (congrArg (fun value => last 0 entries.1 + value) tail)

/-- Adding two weights before folding gives the sum of their separate retained-entry folds. -/
theorem sum_add {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
      (entries : DependentProduct items family) →
      (first last : (index : Fin items.length) → family index → Nat) →
      sum items (fun index entry => first index entry + last index entry) entries =
        sum items first entries + sum items last entries
  | [], _, _, _, _ => rfl
  | _ :: remaining, _, entries, first, last => by
      change (first 0 entries.1 + last 0 entries.1) +
          sum remaining (fun index entry => first index.succ entry + last index.succ entry) entries.2 =
        (first 0 entries.1 + sum remaining (fun index => first index.succ) entries.2) +
          (last 0 entries.1 + sum remaining (fun index => last index.succ) entries.2)
      rw [sum_add remaining entries.2 (fun index => first index.succ) (fun index => last index.succ)]
      rw [Nat.add_assoc, ← Nat.add_assoc (last 0 entries.1),
        Nat.add_comm (last 0 entries.1), Nat.add_assoc, ← Nat.add_assoc]

/-- Unit weight counts exactly the original list's retained bounded occurrences. -/
theorem sum_one {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
      (entries : DependentProduct items family) → sum items (fun _ _ => 1) entries = items.length
  | [], _, _ => rfl
  | _ :: remaining, _, entries => by
      change 1 + sum remaining (fun _ _ => 1) entries.2 = remaining.length + 1
      rw [sum_one remaining entries.2]
      exact Nat.add_comm _ _

/-- A weight depending only on the original item gives its structural list fold.

The retained entries are read only through the same original product. Their
values do not affect an item-only weight, so the fold agrees without rebuilding
the entries or comparing their dependent types. -/
theorem sum_items {α : Type u} :
    (items : List α) → {family : Fin items.length → Type v} →
      (entries : DependentProduct items family) → (weight : α → Nat) →
      sum items (fun index _ => weight (items.get index)) entries =
        items.foldr (fun item total => weight item + total) 0
  | [], _, _, _ => rfl
  | head :: remaining, _, entries, weight => by
      change weight head + sum remaining (fun index _ => weight (remaining.get index)) entries.2 =
        weight head + remaining.foldr (fun item total => weight item + total) 0
      exact congrArg (fun total => weight head + total) (sum_items remaining entries.2 weight)

/-- Folding displayed values of the same retained entries agrees with the original stored-entry sum.

The finite list materialization preserves the original occurrence order.
Each displayed value is read from its same stored entry; this equation does
not invoke the original entry producer.
-/
theorem sum_ofFn {α : Type u} {β : Type v} :
    (items : List α) → {family : Fin items.length → Type w} →
    (entries : DependentProduct items family) →
    (value : (index : Fin items.length) → family index → β) → (weight : β → Nat) →
    (List.ofFn (fun index => value index (get items entries index))).foldr
        (fun entry total => weight entry + total) 0 =
      sum items (fun index entry => weight (value index entry)) entries
  | [], _, _, _, _ => rfl
  | _ :: remaining, _, entries, value, weight => by
      rw [OfFn.Basic.ofFn_succ]
      change weight (value 0 entries.1) +
          (List.ofFn (fun index => value index.succ (get remaining entries.2 index))).foldr
            (fun entry total => weight entry + total) 0 =
        weight (value 0 entries.1) + sum remaining (fun index entry => weight (value index.succ entry)) entries.2
      exact congrArg (fun total => weight (value 0 entries.1) + total)
        (sum_ofFn remaining entries.2 (fun index => value index.succ) weight)

end DependentProduct

end Purelib.Data.List

end
