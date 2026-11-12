module

import Purelib.Data.List.Occurrences

/-!
# Ordered repeated-tag cache regression

Nonadjacent repeated tags retain their original positions, exact occurrence
orders and immediately preceding occurrence coordinates.
-/

namespace TestPurelib.Data.List.Occurrences

open Purelib.Data.List

/-- A word with interleaved repeated original tags. -/
private def word : List Nat := [0, 1, 0, 0, 1, 2, 0]

/-- The complete once-prepared cache for the same original word. -/
private def retained := Occurrences.prepare word

/-- The actual cached occurrence orders have the independent expected finite table. -/
private theorem orders : ∀ index : Fin 7,
    retained.orders index = ([0, 0, 1, 2, 1, 0, 3] : List Nat)[index.val]'index.isLt := by decide +kernel

/-- The actual cached predecessors retain the independent original position table. -/
private theorem predecessors : ∀ index : Fin 7,
    (retained.predecessors index).map Fin.val =
      ([none, none, some 0, some 2, some 1, none, some 3] : List (Option Nat))[index.val]'index.isLt := by
  decide +kernel

/-- Prepending consumes the retained original tail through the same public branch. -/
private theorem shared_prepend : ∀ index : Fin 7,
    (Occurrences.prepend 0 (Occurrences.prepare [1, 0, 0, 1, 2, 0])).orders index = retained.orders index := by
  decide +kernel

/-- Extract the same original three-tag prefix from the already prepared complete cache. -/
private def first : Occurrences ([0, 1, 0] : List Nat) :=
  retained.take [0, 1, 0] [0, 1, 2, 0]

/-- Prefix extraction retains exactly the expected original occurrence orders. -/
private theorem prefix_orders : ∀ index : Fin 3,
    first.orders index = ([0, 0, 1] : List Nat)[index.val]'index.isLt := by decide +kernel

/-- Prefix extraction retains the original bounded predecessor coordinates without another scan. -/
private theorem prefix_predecessors : ∀ index : Fin 3,
    (first.predecessors index).map Fin.val =
      ([none, none, some 0] : List (Option Nat))[index.val]'index.isLt := by decide +kernel

end TestPurelib.Data.List.Occurrences
