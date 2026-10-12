module
import Purelib.Data.List.OfFn.Basic
import Mathlib.Tactic.TypeStar

/-!
# Distinct entries of an injective finite function table

The original List.ofFn table retains every original bounded index in order.
Injectivity distinguishes its head from each successor entry and identifies
indices recursively in that same successor tail.
-/

open Purelib.Data.List

namespace Purelib.Data.List.OfFn.Nodup

/-- An injective finite indexed family materializes to a duplicate-free list.

Each original table occurrence carries its actual bounded Fin index.
Injectivity rules out a repeated head and identifies successor indices
without proposition equality or changing the retained enumeration. -/
public theorem nodup_ofFn_of_injective {Alpha : Type*} {size : Nat}
    {function : Fin size → Alpha} (injective : Function.Injective function) :
    (List.ofFn function).Nodup := by
  induction size with
  | zero =>
      rw [List.ofFn_zero]
      exact List.Pairwise.nil
  | succ size inductionHypothesis =>
      rw [OfFn.Basic.ofFn_succ]
      apply List.Pairwise.cons
      · intro value member equal
        rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, valueEqual⟩
        have impossible : (0 : Fin (size + 1)) = index.succ :=
          injective (equal.trans valueEqual.symm)
        exact Nat.noConfusion (congrArg Fin.val impossible)
      · apply inductionHypothesis
        intro left right equal
        have equalSuccessors : left.succ = right.succ := injective equal
        apply Fin.ext
        exact Nat.succ.inj (congrArg Fin.val equalSuccessors)

end Purelib.Data.List.OfFn.Nodup
