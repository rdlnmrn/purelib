module

public import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Data.List.GetD

/-! # Shared vertices of the original ordered subdivision edge word

The initial endpoint followed by the original target list gives one shared
vertex at each position. Consecutive edges use its unchanged castSucc and
succ indices. The readbacks retain complete Endpoint values, including
their original bounds, without selecting a vertex by its coordinate.
-/

public section

namespace Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

open Purelib

/-- Consecutive edges have exactly one occurrence for each supplied target endpoint. -/
theorem parameterEdgesFrom_length : (current : Endpoint) → (targets : List Endpoint) →
    (parameterEdgesFrom current targets).length = targets.length
  | _, [] => rfl
  | _, endpoint :: remaining => congrArg Nat.succ (parameterEdgesFrom_length endpoint remaining)

/-- Retain the SAME target occurrence as its exact consecutive-edge occurrence. -/
@[expose] def edgeIndex (current : Endpoint) (targets : List Endpoint) (index : Fin targets.length) :
    Fin (parameterEdgesFrom current targets).length :=
  Fin.cast (parameterEdgesFrom_length current targets).symm index

/-- Each consecutive edge starts at the SAME stored vertex preceding its actual target occurrence. -/
theorem parameterEdgesFrom_source : (current : Endpoint) → (targets : List Endpoint) →
    (index : Fin targets.length) →
    (current :: targets)[index.castSucc.val]'index.castSucc.isLt =
      ((parameterEdgesFrom current targets)[(edgeIndex current targets index).val]'
        (edgeIndex current targets index).isLt).left
  | _, [], index => Fin.elim0 index
  | _, _ :: _, ⟨0, _⟩ => rfl
  | _, endpoint :: remaining, ⟨index + 1, bounded⟩ =>
      parameterEdgesFrom_source endpoint remaining ⟨index, Nat.lt_of_succ_lt_succ bounded⟩
termination_by structural _ targets _ => targets

/-- Each consecutive edge ends at the SAME stored vertex at its actual target occurrence. -/
theorem parameterEdgesFrom_target : (current : Endpoint) → (targets : List Endpoint) →
    (index : Fin targets.length) →
    (current :: targets)[index.succ.val]'index.succ.isLt =
      ((parameterEdgesFrom current targets)[(edgeIndex current targets index).val]'
        (edgeIndex current targets index).isLt).right
  | _, [], index => Fin.elim0 index
  | _, _ :: _, ⟨0, _⟩ => rfl
  | _, endpoint :: remaining, ⟨index + 1, bounded⟩ =>
      parameterEdgesFrom_target endpoint remaining ⟨index, Nat.lt_of_succ_lt_succ bounded⟩
termination_by structural _ targets _ => targets

/-- The SAME dyadic target occurrence indexes its original dyadic parameter edge. -/
@[expose] def dyadicIndex (depth : Nat) (left right : Endpoint)
    (index : Fin (dyadicTargets depth left right).length) : Fin (dyadicEdges depth left right).length :=
  Fin.cast (congrArg List.length (parameterEdgesFrom_dyadicTargets depth left right))
    (edgeIndex left (dyadicTargets depth left right) index)

/-- The original dyadic edge starts at its SAME shared bounded vertex. -/
theorem dyadic_source (depth : Nat) (left right : Endpoint)
    (index : Fin (dyadicTargets depth left right).length) :
    (left :: dyadicTargets depth left right)[index.castSucc.val]'index.castSucc.isLt =
      ((dyadicEdges depth left right)[(dyadicIndex depth left right index).val]'
        (dyadicIndex depth left right index).isLt).left :=
  (parameterEdgesFrom_source left (dyadicTargets depth left right) index).trans
    (congrArg ParameterEdge.left (Data.List.at_cast
      (parameterEdgesFrom_dyadicTargets depth left right)
      (edgeIndex left (dyadicTargets depth left right) index))).symm

/-- The original dyadic edge ends at its SAME shared bounded vertex. -/
theorem dyadic_target (depth : Nat) (left right : Endpoint)
    (index : Fin (dyadicTargets depth left right).length) :
    (left :: dyadicTargets depth left right)[index.succ.val]'index.succ.isLt =
      ((dyadicEdges depth left right)[(dyadicIndex depth left right index).val]'
        (dyadicIndex depth left right index).isLt).right :=
  (parameterEdgesFrom_target left (dyadicTargets depth left right) index).trans
    (congrArg ParameterEdge.right (Data.List.at_cast
      (parameterEdgesFrom_dyadicTargets depth left right)
      (edgeIndex left (dyadicTargets depth left right) index))).symm

/-- Transport an actual retained target occurrence through its complete original dyadic list factory. -/
@[expose] def dyadicIndexOf (depth : Nat) (left right : Endpoint)
    (targets : List Endpoint) (factory : targets = dyadicTargets depth left right) (index : Fin targets.length) :
    Fin (dyadicEdges depth left right).length :=
  dyadicIndex depth left right (Fin.cast (congrArg List.length factory) index)

/-- The SAME cached source vertex is the actual indexed dyadic edge's complete left Endpoint. -/
theorem dyadic_source_of_eq (depth : Nat) (left right : Endpoint)
    (targets : List Endpoint) (factory : targets = dyadicTargets depth left right) (index : Fin targets.length) :
    (left :: targets)[index.castSucc.val]'index.castSucc.isLt =
      ((dyadicEdges depth left right)[(dyadicIndexOf depth left right targets factory index).val]'
        (dyadicIndexOf depth left right targets factory index).isLt).left := by
  let original := Fin.cast (congrArg List.length factory) index
  have same : (left :: targets)[index.castSucc.val]'index.castSucc.isLt =
      (left :: dyadicTargets depth left right)[original.castSucc.val]'original.castSucc.isLt :=
    getElem_congr (congrArg (List.cons left) factory) rfl index.castSucc.isLt
  exact same.trans (dyadic_source depth left right original)

/-- The SAME cached finishing vertex is the actual indexed dyadic edge's complete right Endpoint. -/
theorem dyadic_target_of_eq (depth : Nat) (left right : Endpoint)
    (targets : List Endpoint) (factory : targets = dyadicTargets depth left right) (index : Fin targets.length) :
    (left :: targets)[index.succ.val]'index.succ.isLt =
      ((dyadicEdges depth left right)[(dyadicIndexOf depth left right targets factory index).val]'
        (dyadicIndexOf depth left right targets factory index).isLt).right := by
  let original := Fin.cast (congrArg List.length factory) index
  have same : (left :: targets)[index.succ.val]'index.succ.isLt =
      (left :: dyadicTargets depth left right)[original.succ.val]'original.succ.isLt :=
    getElem_congr (congrArg (List.cons left) factory) rfl index.succ.isLt
  exact same.trans (dyadic_target depth left right original)

end Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

end
