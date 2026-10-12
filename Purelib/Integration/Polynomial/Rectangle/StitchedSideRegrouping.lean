module
import Purelib.Data.List.OfFn.Basic

public import Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas

@[expose] public section

/-! Exact regrouping for the nonempty, variably sized finite cell banks used
by clipped perimeters. No joining chord is removed at a piece boundary. -/
namespace Purelib.Integration.Polynomial.Rectangle.StitchedSideRegrouping

open Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas.Entry (assemble concatenate regroup)

/-- Flat-mapping a retained list equals flattening the list of its mapped blocks. -/
private theorem flatMap_eq {α β : Type} (entries : List α) (value : α → List β) :
    entries.flatMap value = (entries.map value).flatten := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.append (value head)) ih

open Purelib.Data.List
open Purelib.Integration.Polynomial.Rectangle
/-- Pointwise equal indexed area entries have equal concatenated entries. -/
theorem concatenate_congr {count : Nat} {first last : Fin (count + 1) → StitchedSideAreas.Entry}
    (equal : ∀ index, first index = last index) : StitchedSideAreas.Entry.concatenate first =
      StitchedSideAreas.Entry.concatenate last :=
  congrArg₂ StitchedSideAreas.Entry.assemble (equal 0) (OfFn.Basic.ofFn_congr (fun index : Fin count => equal
    index.succ))

/-- An exact flattening of retained entry blocks permits concatenating each block before concatenating their summaries.

The original indexed entries and their ordered block decomposition remain fixed, preserving area and both boundary
points. -/
theorem concatenate_of_flatten {count total : Nat} {sizes : Fin (count + 1) → Nat}
    (whole : Fin (total + 1) → StitchedSideAreas.Entry)
    (pieces : (piece : Fin (count + 1)) → Fin (sizes piece + 1) → StitchedSideAreas.Entry)
    (equal : List.ofFn whole = (List.ofFn (fun piece => List.ofFn (pieces piece))).flatten) :
    StitchedSideAreas.Entry.concatenate whole = StitchedSideAreas.Entry.concatenate (fun piece =>
      StitchedSideAreas.Entry.concatenate (pieces piece)) := by
  let blocks := List.ofFn (fun piece : Fin count =>
    (pieces piece.succ 0, List.ofFn (fun index : Fin (sizes piece.succ) => pieces piece.succ index.succ)))
  have blockLists : blocks.map (fun block => block.1 :: block.2) =
      List.ofFn (fun piece : Fin count => List.ofFn (pieces piece.succ)) := by
    rw [OfFn.Basic.map_ofFn]
    exact OfFn.Basic.ofFn_congr (fun piece => OfFn.Basic.ofFn_succ.symm)
  have rest : (List.ofFn (fun piece : Fin count => List.ofFn (pieces piece.succ))).flatten =
      blocks.flatMap (fun block => block.1 :: block.2) :=
    (congrArg List.flatten blockLists).symm.trans (StitchedSideRegrouping.flatMap_eq blocks _).symm
  have all : List.ofFn whole = pieces 0 0 ::
      (List.ofFn (fun index : Fin (sizes 0) => pieces 0 index.succ) ++
        blocks.flatMap (fun block => block.1 :: block.2)) := by
    apply equal.trans
    rw [OfFn.Basic.ofFn_succ, List.flatten_cons, rest, OfFn.Basic.ofFn_succ]
    rfl
  rw [OfFn.Basic.ofFn_succ] at all
  have same := List.cons.inj all
  have grouped := (congrArg₂ StitchedSideAreas.Entry.assemble same.1 same.2).trans
    (StitchedSideAreas.Entry.regroup (pieces 0 0) (List.ofFn (fun index : Fin (sizes 0) => pieces 0 index.succ)) blocks)
  have summaries : blocks.map (fun block => block.1.assemble block.2) =
      List.ofFn (fun piece : Fin count => StitchedSideAreas.Entry.concatenate (pieces piece.succ)) := by
    rw [OfFn.Basic.map_ofFn]
    rfl
  exact grouped.trans (congrArg (StitchedSideAreas.Entry.assemble (StitchedSideAreas.Entry.concatenate (pieces 0)))
    summaries)

end Purelib.Integration.Polynomial.Rectangle.StitchedSideRegrouping
