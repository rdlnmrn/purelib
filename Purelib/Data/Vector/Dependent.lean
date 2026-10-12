module
meta import Purelib.Elab.ConstructiveInjectivity

-- Exposed vector types and builders retain this direct successor evidence.
public import Purelib.Data.Nat.Order

/-!
# Materialized finite dependent vectors

Each entry keeps its own type and is computed once by `ofFn`. Lookup follows
the stored spine and finite index directly; neither choice nor function
extensionality is used to recover a dependent entry.
-/

namespace Purelib.Data.Vector

open scoped Purelib.Data.Nat

public section

universe u v

set_option genInjectivity false in
/-- A finite stored spine whose entries retain their index-dependent types.

Each constructor keeps the original family and dimension. The head has the
family's zero-index type and the tail keeps the successor-index family. -/
inductive DependentVector : {size : Nat} → (Fin size → Type u) → Type (u + 1) where
  /-- The empty dependent vector over the original empty family. -/ | nil {family : Fin 0 → Type u} : DependentVector
    family
  /-- Retain the original zero-index entry and the tail with its successor-shifted family. -/ | cons {size : Nat}
    {family : Fin (size + 1) → Type u}
      (head : family 0) (tail : DependentVector (fun index => family index.succ)) : DependentVector family

constructive_injectivity DependentVector

namespace DependentVector

/-- Read a dependent entry by following its retained finite index.

Lookup traverses the stored spine directly and returns the original family's
type at that index, without reconstructing an entry. -/
@[expose] def get : {size : Nat} → {family : Fin size → Type u} → DependentVector family → (index : Fin size) → family
  index
  | _, _, .nil, index => Fin.elim0 index
  | _, _, .cons head _, ⟨0, _⟩ => head
  | _, _, .cons _ tail, ⟨index + 1, bound⟩ => tail.get ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Store each entry of a finite dependent lookup exactly once.

The original family and dimension are retained in the resulting spine. Each
recursive tail materializes the successor-index entries of that family. -/
@[expose] def ofFn : {size : Nat} → {family : Fin size → Type u} → ((index : Fin size) → family index) → DependentVector
  family
  | 0, _, _ => .nil
  | _ + 1, _, entries => .cons (entries 0) (ofFn fun index => entries index.succ)

/-- Reading a materialized dependent vector recovers its original entry. -/
theorem ofFn_get {size : Nat} {family : Fin size → Type u} (entries : (index : Fin size) → family index) (index : Fin
  size) :
    (ofFn entries).get index = entries index := by
  induction size with
  | zero => exact Fin.elim0 index
  | succ size ih =>
      rcases index with ⟨index, bound⟩
      cases index with
      | zero => rfl
      | succ index =>
          exact ih (fun index => entries index.succ)
            ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Fold the maximum natural weight over retained dependent entries.

The weight reads both the original index and its already stored entry. The empty
vector contributes zero; the computation never rebuilds an entry. -/
@[expose] def maximum : {size : Nat} → {family : Fin size → Type u} →
    ((index : Fin size) → family index → Nat) → DependentVector family → Nat
  | _, _, _, .nil => 0
  | _, _, weight, .cons head tail => max (weight 0 head) (tail.maximum fun index => weight index.succ)

/-- Every retained entry's scalar requirement is bounded by the stored maximum.

The bound follows the same spine and finite index as lookup, retaining the
weight's dependent entry type at every step. -/
theorem get_le_maximum : ∀ {size : Nat} {family : Fin size → Type u}
    (weight : (index : Fin size) → family index → Nat) (entries : DependentVector family) (index : Fin size),
    weight index (entries.get index) ≤ entries.maximum weight
  | _, _, _, .nil, index => Fin.elim0 index
  | _, _, _, .cons _ _, ⟨0, _⟩ => Nat.Order.le_max_left _ _
  | _, _, weight, .cons _ tail, ⟨index + 1, bound⟩ =>
      Nat.le_trans (get_le_maximum (fun index => weight index.succ) tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩)
        (Nat.Order.le_max_right _ _)

/-- A common scalar ceiling bounds the maximum of retained dependent entries.

Each original entry is bounded at its retained finite index. The proof follows
only that vector's stored spine and combines the head and tail bounds. -/
theorem maximum_le {size : Nat} {family : Fin size → Type u}
    (entries : DependentVector family)
    (weight : (position : Fin size) → family position → Nat) (ceiling : Nat)
    (bounded : ∀ position, weight position (entries.get position) ≤ ceiling) :
    entries.maximum weight ≤ ceiling := by
  induction entries with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    exact Nat.Order.max_le (bounded 0)
      (ih (fun position => weight position.succ) (fun position => bounded position.succ))

/-- Equal pointwise weights give the same maximum of retained dependent entries.

The vectors keep their original dimension and potentially different entry
families. Each vector's maximum bounds the other's equal pointwise weights,
and scalar antisymmetry identifies the two retained maxima. -/
theorem maximum_eq {size : Nat} {firstFamily : Fin size → Type u} {lastFamily : Fin size → Type v}
    (first : DependentVector firstFamily) (last : DependentVector lastFamily)
    (firstWeight : (position : Fin size) → firstFamily position → Nat)
    (lastWeight : (position : Fin size) → lastFamily position → Nat)
    (same : ∀ position, firstWeight position (first.get position) = lastWeight position (last.get position)) :
    first.maximum firstWeight = last.maximum lastWeight := by
  exact Nat.le_antisymm
    (maximum_le first firstWeight (last.maximum lastWeight)
      (fun position => (same position).symm ▸ get_le_maximum lastWeight last position))
    (maximum_le last lastWeight (first.maximum firstWeight)
      (fun position => same position ▸ get_le_maximum firstWeight first position))

/-- The maximum natural weight of a materialized three-index dependent bank.

The outer vector retains each row, each row retains its cells, and each cell
retains its original third-index entries. Three existing maximum folds use
exactly those stored spines and the supplied scalar weight.
-/
@[expose] def maximum3 {n m k : Nat} {family : Fin n → Fin m → Fin k → Type u}
    (weight : ∀ a b c, family a b c → Nat)
    (entries : DependentVector (fun a => DependentVector (fun b => DependentVector (family a b)))) : Nat :=
  entries.maximum (fun a rows => rows.maximum (fun b cells => cells.maximum (weight a b)))

/-- Each retained three-index entry has weight bounded by the bank maximum.

The original three indices select the same stored entry at every level.
Successive existing entry bounds compare its weight with the cell, row and
outer maxima without enumerating or recomputing any entry.
-/
theorem entry_le_maximum3 {n m k : Nat} {family : Fin n → Fin m → Fin k → Type u}
    (weight : ∀ a b c, family a b c → Nat)
    (entries : DependentVector (fun a => DependentVector (fun b => DependentVector (family a b))))
    (a : Fin n) (b : Fin m) (c : Fin k) :
    weight a b c (((entries.get a).get b).get c) ≤ maximum3 weight entries :=
  Nat.le_trans (get_le_maximum (weight a b) ((entries.get a).get b) c)
    (Nat.le_trans
      (get_le_maximum
        (fun b (cells : DependentVector (family a b)) => cells.maximum (weight a b)) (entries.get a) b)
      (get_le_maximum
        (fun a (rows : DependentVector (fun b => DependentVector (family a b))) =>
          rows.maximum (fun b cells => cells.maximum (weight a b))) entries a))

end DependentVector
end

end Purelib.Data.Vector
