module

public import Purelib.Riemann.Integration.PreparedCoveredParentLists
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Data.List.Append

/-! # Original covering entries through exact parent casts and append offsets

The complete retained patch/containment subtype is preserved, including its
original nominal parent. Ordered bounded indices identify each occurrence;
heterogeneous equality transports only the exact list/parent indices.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- Equal bounded occurrences retain the whole original covering patch and endpoint witness. -/
theorem entry_congr {parents : List (CenteredEdge curve differential)} (covered : CoveredParents count parents)
    {first last : Fin parents.length} (equal : first = last) : HEq (covered.entry first) (covered.entry last) := by
  cases equal
  rfl

/-- Exact parent-list transport preserves the SAME complete covering entry at equal natural coordinates. -/
theorem castParents_entry_heq {first last : List (CenteredEdge curve differential)}
    (equal : first = last) (covered : CoveredParents count first)
    (firstIndex : Fin first.length) (lastIndex : Fin last.length) (index_eq : firstIndex.val = lastIndex.val) :
    HEq ((covered.castParents equal).entry lastIndex) (covered.entry firstIndex) := by
  cases equal
  exact covered.entry_congr (Fin.ext index_eq.symm)

end Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

namespace Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- A bounded left append occurrence retains its whole original covering patch and finish certificate. -/
theorem entry_append_left : {first last : List (CenteredEdge curve differential)} →
    (firstCover : CoveredParents count first) → (lastCover : CoveredParents count last) →
    (index : Fin first.length) → (bound : index.val < (first ++ last).length) →
    HEq ((append firstCover lastCover).entry ⟨index.val, bound⟩) (firstCover.entry index)
  | [], _, .nil, _, index, _ => Fin.elim0 index
  | _ :: _, _, .cons _ _ _, _, ⟨0, _⟩, _ => by
      rewrite [append_cons]
      exact HEq.rfl
  | _ :: _, _, .cons _ _ remaining, lastCover, ⟨index + 1, bounded⟩, bound => by
      rewrite [append_cons]
      exact entry_append_left remaining lastCover ⟨index, Nat.lt_of_succ_lt_succ bounded⟩
        (Nat.lt_of_succ_lt_succ bound)

/-- A bounded right append occurrence retains its SAME original covering entry after the actual left prefix. -/
theorem entry_append_right : {first last : List (CenteredEdge curve differential)} →
    (firstCover : CoveredParents count first) → (lastCover : CoveredParents count last) →
    (index : Fin last.length) → (bound : first.length + index.val < (first ++ last).length) →
    HEq ((append firstCover lastCover).entry ⟨first.length + index.val, bound⟩) (lastCover.entry index)
  | [], _, .nil, lastCover, index, _ => by
      rewrite [append_nil]
      exact lastCover.entry_congr (Fin.ext (Nat.zero_add index.val))
  | parent :: first, last, .cons patch inside remaining, lastCover, index, bound => by
      have shift : (parent :: first).length + index.val = (first.length + index.val) + 1 :=
        Nat.succ_add first.length index.val
      have shifted : (first.length + index.val) + 1 < (first ++ last).length + 1 :=
        Eq.mp (congrArg (fun value => value < (first ++ last).length + 1) shift) bound
      have small : first.length + index.val < (first ++ last).length := Nat.lt_of_succ_lt_succ shifted
      have indices : (⟨(parent :: first).length + index.val, bound⟩ : Fin ((parent :: first) ++ last).length) =
          (⟨first.length + index.val, small⟩ : Fin (first ++ last).length).succ := Fin.ext shift
      rewrite [append_cons]
      exact ((CoveredParents.cons patch inside (append remaining lastCover)).entry_congr indices).trans
        (entry_append_right remaining lastCover index small)

end Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents

end
