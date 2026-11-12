module

public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.List.DependentProduct.Flatten
import Purelib.Tactic.Ring

/-! # Scalar sums of retained item-dependent products

Every scalar reading consumes its original stored entry. Concatenating or
flattening products preserves the exact ordered scalar sum, including empty
blocks and repeated item occurrences.
-/

public section

namespace Purelib.Algebra.FiniteSum.Fin

open Purelib.Data.List

universe u v w

variable {Item : Type u} {family : Item → Type v} {K : Type w} [CommRing K]

/-- Sum scalar readings of the same stored item-dependent product at its original finite positions. -/
@[expose] def sumProduct (items : List Item)
    (entries : DependentProduct items (fun index => family (items[index.val]'index.isLt)))
    (read : (item : Item) → family item → K) : K :=
  sumFin (fun index => read (items[index.val]'index.isLt) (DependentProduct.get items entries index))

/-- The actual retained head reading separates from the unchanged scalar tail. -/
private theorem sumProduct_cons (head : Item) (tail : List Item)
    (entries : DependentProduct (head :: tail) (fun index => family ((head :: tail)[index.val]'index.isLt)))
    (read : (item : Item) → family item → K) :
    sumProduct (head :: tail) entries read = read head entries.1 + sumProduct tail entries.2 read :=
  sumFin_succ (fun index => read ((head :: tail)[index.val]'index.isLt)
    (DependentProduct.get (head :: tail) entries index))

/-- Scalar readings of an actually materialized product equal the same original finite scalar table. -/
theorem sumProduct_ofFn (items : List Item)
    (entries : (index : Fin items.length) → family (items[index.val]'index.isLt))
    (read : (item : Item) → family item → K) :
    sumProduct items (DependentProduct.ofFn items entries) read =
      sumFin (fun index => read (items[index.val]'index.isLt) (entries index)) :=
  sumFin_congr (fun index => congrArg (read (items[index.val]'index.isLt))
    (DependentProduct.get_ofFn items entries index))

/-- Exact item-list transport preserves the whole scalar sum of the same retained product. -/
theorem sumProduct_castItems {first last : List Item} (equal : first = last)
    (entries : DependentProduct first (fun index => family (first[index.val]'index.isLt)))
    (read : (item : Item) → family item → K) :
    sumProduct last (DependentProduct.castItems equal.symm entries
      (resultFamily := fun index => family (last[index.val]'index.isLt))
      (sameFamily := by cases equal; rfl)) read = sumProduct first entries read := by
  cases equal
  rfl

/-- Appending actual stored product spines adds their exact scalar readings without rebuilding entries. -/
theorem sumProduct_appendItems : (first last : List Item) →
    (before : DependentProduct first (fun index => family (first[index.val]'index.isLt))) →
    (after : DependentProduct last (fun index => family (last[index.val]'index.isLt))) →
    (read : (item : Item) → family item → K) →
    sumProduct (first ++ last) (DependentProduct.appendItems first last before after) read =
      sumProduct first before read + sumProduct last after read
  | [], last, _, after, read => by
      change sumProduct last after read = 0 + sumProduct last after read
      ring1
  | head :: tail, last, before, after, read => by
      change sumProduct (head :: (tail ++ last))
        (before.1, DependentProduct.appendItems tail last before.2 after) read = _
      rewrite [sumProduct_cons, sumProduct_cons, sumProduct_appendItems tail last before.2 after read]
      ring1

/-- Flattening actual stored blocks preserves the original nested sum and every empty or repeated occurrence. -/
theorem sumProduct_flattenItems : (blocks : List (List Item)) →
    (entries : DependentProduct blocks (fun outer =>
      DependentProduct (blocks[outer.val]'outer.isLt)
        (fun inner => family ((blocks[outer.val]'outer.isLt)[inner.val]'inner.isLt)))) →
    (read : (item : Item) → family item → K) →
    sumProduct blocks.flatten (DependentProduct.flattenItems blocks entries) read =
      sumFin (fun outer => sumProduct (blocks[outer.val]'outer.isLt)
        (DependentProduct.get blocks entries outer) read)
  | [], _, _ => rfl
  | head :: tail, entries, read => by
      change sumProduct (head ++ tail.flatten)
        (DependentProduct.appendItems head tail.flatten entries.1 (DependentProduct.flattenItems tail entries.2))
        read = _
      rewrite [sumProduct_appendItems head tail.flatten entries.1 (DependentProduct.flattenItems tail entries.2) read,
        sumProduct_flattenItems tail entries.2 read, sumFin_succ]
      rfl

end Purelib.Algebra.FiniteSum.Fin

end
