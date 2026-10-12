module
import Purelib.Data.Fin.Remove
import Purelib.Data.Fin
import Purelib.Data.Nat.Addition

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Nat

/-!
# Cardinality bounds from explicit finite injections

Removing the displayed image of the first position reduces both finite
index types. Structural recursion bounds their original natural sizes.
-/

namespace Purelib.Data.Fin.Cardinality

/-- An injection between bounded natural index types bounds their sizes.

Given an explicit injective map from Fin n to Fin m, prove n ≤ m by recursively removing the image of zero and
restricting to the successor indices. No enumeration chosen from finiteness is required. -/
public theorem fin_card_le_of_injective_direct : ∀ {n m : Nat},
    (f : Fin n → Fin m) → Function.Injective f → n ≤ m
  | 0, _, _, _ => Nat.zero_le _
  | n + 1, 0, f, _ => Fin.elim0 (f ⟨0, Nat.zero_lt_succ n⟩)
  | n + 1, m + 1, f, injective => by
      let removed := f ⟨0, Nat.zero_lt_succ n⟩
      let reduced : Fin n → Fin m := fun i =>
        Remove.removeFinIndex removed (f i.succ) (by
          intro equal
          exact Purelib.Data.Fin.succ_ne_zero i (injective equal))
      have reducedInjective : Function.Injective reduced := by
        intro i j equal
        have images : f i.succ = f j.succ := by
          apply Remove.removeFinIndex_injective <;> assumption
        have successors : i.succ = j.succ := injective images
        have values := congrArg (fun z : Fin (n + 1) => z.val) successors
        change i.val + 1 = j.val + 1 at values
        exact Fin.ext (Addition.add_right_cancel values)
      exact Nat.succ_le_succ
        (Purelib.Data.Fin.Cardinality.fin_card_le_of_injective_direct reduced reducedInjective)

end Purelib.Data.Fin.Cardinality
