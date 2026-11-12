module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Factorization
import Purelib.Data.Vector.Basic
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Fold
import Purelib.Data.List.OfFn.Basic
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original factor and root occurrences of flattened weighted blocks

Every original flattened block retains its original bounded factor occurrence
and its same retained final simple-root occurrence. The finite vector of these
views is materialized once, with exact original position and point readbacks.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Roots (Block)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List

universe u

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
variable {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
variable {function : Canonical → K}

/-- The same original factor's weighted cache attaches its multiplicity to its cached simple-root points. -/
theorem blocksAt_eq (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (position : Fin indices.length) :
    blocksAt stages images position =
      (rootsAt stages images position).map (weighted (contexts.get (indices.get position))) := by
  induction stages with
  | done => exact Fin.elim0 position
  | adjoin _ _ _ _ _ _ _ remaining previous =>
      rcases position with ⟨value, bound⟩
      cases value with
      | zero => exact images.1.blocks_eq
      | succ value => exact previous images.2 ⟨value, Nat.lt_of_succ_lt_succ bound⟩

/-- Attaching the original multiplicity preserves the same bounded root occurrence count. -/
theorem blocksAt_length (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (position : Fin indices.length) :
    (blocksAt stages images position).length = (rootsAt stages images position).length := by
  rewrite [blocksAt_eq]
  exact Map.length_map _ _

set_option genInjectivity false in
/-- One flattened block's original bounded factor and same cached final simple-root occurrence. -/
structure Origin (stages : Stages contexts indices K ring equality function) (images : Images stages) where
  /-- The original bounded occurrence in the displayed factor-stage list. -/
  factor : Fin indices.length
  /-- The same original bounded occurrence in that stage's retained final simple-root list. -/
  root : Fin (rootsAt stages images factor).length

constructive_injectivity Origin

namespace Origin

/-- Read the point at the same retained original factor-root occurrence. -/
@[expose] def point {stages : Stages contexts indices K ring equality function} {images : Images stages}
    (origin : Origin stages images) : stages.Scalar :=
  ((rootsAt stages images origin.factor).get origin.root).point

/-- Read the original bounded positive context of this same retained factor occurrence. -/
@[expose] def contextIndex {stages : Stages contexts indices K ring equality function} {images : Images stages}
    (origin : Origin stages images) : Fin contexts.length := indices.get origin.factor

/-- Read the same retained original positive context without repeating its enumeration. -/
@[expose] def context {stages : Stages contexts indices K ring equality function} {images : Images stages}
    (origin : Origin stages images) : PositiveContext entries := contexts.get origin.contextIndex

/-- Read the same local root coordinate with its original focused-factor degree bound. -/
@[expose] def localIndex {stages : Stages contexts indices K ring equality function} {images : Images stages}
    (origin : Origin stages images) : Fin origin.context.focus.part.polynomial.natDegree :=
  ⟨origin.root.val, rootsAt_length stages images origin.factor ▸ origin.root.isLt⟩

/-- The focused-degree bound preserves the same original local-root natural coordinate. -/
theorem localIndex_val {stages : Stages contexts indices K ring equality function} {images : Images stages}
    (origin : Origin stages images) : origin.localIndex.val = origin.root.val := rfl

/-- Recover the original flattened natural position of the same bounded factor-root view. -/
@[expose] def position {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function)
    (images : Images stages) (origin : Origin stages images) : Nat :=
  match indices, stages with
  | [], .done => Fin.elim0 origin.factor
  | _ :: _, .adjoin _ _ _ _ _ _ _ remaining =>
      match origin with
      | ⟨⟨0, _⟩, root⟩ => root.val
      | ⟨⟨value + 1, bound⟩, root⟩ =>
          images.1.blocks.length + position remaining images.2 ⟨⟨value, Nat.lt_of_succ_lt_succ bound⟩, root⟩

/-- Locate the same original factor-root occurrence at a bounded flattened weighted-block index. -/
@[expose] def ofIndex {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function)
    (images : Images stages) (index : Fin (blocks stages images).length) : Origin stages images :=
  match indices, stages with
  | [], .done => Fin.elim0 index
  | _ :: _, .adjoin _ _ _ _ _ _ _ remaining =>
      if head : index.val < images.1.blocks.length then
        ⟨0, ⟨index.val, (images.1.blocks_length.trans images.1.roots_length.symm) ▸ head⟩⟩
      else
        let tailIndex : Fin (blocks remaining images.2).length := ⟨index.val - images.1.blocks.length, by
          have bound := index.isLt
          change index.val < (images.1.blocks ++ blocks remaining images.2).length at bound
          rewrite [Append.length_append] at bound
          omega0⟩
        let original := ofIndex remaining images.2 tailIndex
        ⟨original.factor.succ, original.root⟩

/-- A bounded flattened block reads back its same original natural position. -/
theorem position_ofIndex (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (index : Fin (blocks stages images).length) :
    position stages images (ofIndex stages images index) = index.val := by
  induction stages with
  | done => exact Fin.elim0 index
  | adjoin _ _ _ _ _ _ _ remaining previous =>
      rewrite [ofIndex]
      split
      · rfl
      · rename_i head
        dsimp only
        change images.1.blocks.length +
          position remaining images.2 (ofIndex remaining images.2 ⟨index.val - images.1.blocks.length, _⟩) = _
        rewrite [previous images.2]
        exact Nat.add_sub_of_le (Nat.le_of_not_gt head)

/-- A weighted cached block reads the same point as its same bounded simple-root occurrence. -/
private theorem image_point {A L : Type*} {context : PositiveContext entries} {original : List (Block A)}
    {embedding : A → L} (image : Image context original embedding) (index : Fin image.blocks.length) :
    (image.blocks.get index).point =
      (image.roots.get ⟨index.val, (image.blocks_length.trans image.roots_length.symm) ▸ index.isLt⟩).point := by
  have rootBound : index.val < image.roots.length :=
    (image.blocks_length.trans image.roots_length.symm) ▸ index.isLt
  have mappedBound : index.val < (image.roots.map (weighted context)).length := image.blocks_eq ▸ index.isLt
  have same := getElem_congr image.blocks_eq (Eq.refl index.val) index.isLt
  have mapped := Map.getElem_map (weighted context) image.roots index.val rootBound mappedBound
  have reading := congrArg Block.point (same.trans mapped)
  exact reading

/-- The flattened weighted block and its original factor-root view read the same retained point. -/
theorem point_ofIndex (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (index : Fin (blocks stages images).length) :
    ((blocks stages images).get index).point = (ofIndex stages images index).point := by
  induction stages with
  | done => exact Fin.elim0 index
  | adjoin _ _ _ _ _ _ _ remaining previous =>
      rewrite [ofIndex]
      split
      · rename_i head
        have reading := Append.getElem_append_left images.1.blocks (blocks remaining images.2)
          index.val head index.isLt
        exact (congrArg Block.point reading).trans (image_point images.1 ⟨index.val, head⟩)
      · rename_i head
        dsimp only
        let tailIndex : Fin (blocks remaining images.2).length := ⟨index.val - images.1.blocks.length, by
          have bound := index.isLt
          change index.val < (images.1.blocks ++ blocks remaining images.2).length at bound
          rewrite [Append.length_append] at bound
          omega0⟩
        have offset : images.1.blocks.length + tailIndex.val = index.val :=
          Nat.add_sub_of_le (Nat.le_of_not_gt head)
        have same := getElem_congr (Eq.refl (images.1.blocks ++ blocks remaining images.2)) offset.symm index.isLt
        have right := Append.getElem_append_right images.1.blocks (blocks remaining images.2)
          tailIndex.val tailIndex.isLt (offset.symm ▸ index.isLt)
        exact (congrArg Block.point (same.trans right)).trans (previous images.2 tailIndex)

/-- Every weighted image block retains its same original context multiplicity. -/
private theorem image_multiplicity {A L : Type*} {context : PositiveContext entries} {original : List (Block A)}
    {embedding : A → L} (image : Image context original embedding) (index : Fin image.blocks.length) :
    (image.blocks.get index).multiplicity = context.focus.multiplicity := by
  have rootBound : index.val < image.roots.length :=
    (image.blocks_length.trans image.roots_length.symm) ▸ index.isLt
  have mappedBound : index.val < (image.roots.map (weighted context)).length := image.blocks_eq ▸ index.isLt
  have same := getElem_congr image.blocks_eq (Eq.refl index.val) index.isLt
  have mapped := Map.getElem_map (weighted context) image.roots index.val rootBound mappedBound
  exact congrArg Block.multiplicity (same.trans mapped)

/-- A flattened block retains the actual multiplicity of its same original bounded positive context. -/
theorem multiplicity_ofIndex (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (index : Fin (blocks stages images).length) :
    ((blocks stages images).get index).multiplicity = (ofIndex stages images index).context.focus.multiplicity := by
  induction stages with
  | done => exact Fin.elim0 index
  | adjoin _ _ _ _ _ _ _ remaining previous =>
      rewrite [ofIndex]
      split
      · rename_i head
        have reading := Append.getElem_append_left images.1.blocks (blocks remaining images.2)
          index.val head index.isLt
        exact (congrArg Block.multiplicity reading).trans (image_multiplicity images.1 ⟨index.val, head⟩)
      · rename_i head
        dsimp only
        let tailIndex : Fin (blocks remaining images.2).length := ⟨index.val - images.1.blocks.length, by
          have bound := index.isLt
          change index.val < (images.1.blocks ++ blocks remaining images.2).length at bound
          rewrite [Append.length_append] at bound
          omega0⟩
        have offset : images.1.blocks.length + tailIndex.val = index.val :=
          Nat.add_sub_of_le (Nat.le_of_not_gt head)
        have same := getElem_congr (Eq.refl (images.1.blocks ++ blocks remaining images.2)) offset.symm index.isLt
        have right := Append.getElem_append_right images.1.blocks (blocks remaining images.2)
          tailIndex.val tailIndex.isLt (offset.symm ▸ index.isLt)
        exact (congrArg Block.multiplicity (same.trans right)).trans (previous images.2 tailIndex)

/-- The original flattened-index scan sums every same factor-local root occurrence in its original order. -/
private theorem fold_ofIndex (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (value : Origin stages images → Nat) :
    (List.ofFn (fun index : Fin (blocks stages images).length => value (ofIndex stages images index))).foldr Nat.add 0 =
      (List.ofFn (fun factor : Fin indices.length =>
        (List.ofFn (fun root : Fin (rootsAt stages images factor).length =>
          value ⟨factor, root⟩)).foldr Nat.add 0)).foldr Nat.add 0 := by
  induction stages with
  | done => rfl
  | @adjoin K ring equality function selected indices mapped mappedEq normalized degree tower roots rootsEq
      remaining previous =>
      let complete : Stages contexts (selected :: indices) K ring equality function :=
        .adjoin mapped mappedEq normalized degree tower roots rootsEq remaining
      let read : Fin (blocks complete images).length → Nat := fun index => value (ofIndex complete images index)
      have size : (blocks complete images).length = images.1.blocks.length + (blocks remaining images.2).length :=
        Append.length_append _ _
      let common : Fin (images.1.blocks.length + (blocks remaining images.2).length) → Nat :=
        fun index => read ⟨index.val, size.symm ▸ index.isLt⟩
      have materialized : List.ofFn read = List.ofFn common := by
        apply OfFn.Basic.ofFn_congr_size size
        intro first second same
        exact congrArg read (Fin.ext same)
      have first : List.ofFn (fun index : Fin images.1.blocks.length =>
          common (index.castLE (Nat.le_add_right _ _))) =
          List.ofFn (fun root : Fin images.1.roots.length => value ⟨0, root⟩) := by
        apply OfFn.Basic.ofFn_congr_size (images.1.blocks_length.trans images.1.roots_length.symm)
        intro index root same
        change value (ofIndex complete images ⟨index.val, _⟩) = value ⟨0, root⟩
        rewrite [ofIndex, dif_pos index.isLt]
        exact congrArg (fun retained => value ⟨0, retained⟩) (Fin.ext same)
      let later : Origin remaining images.2 → Nat := fun origin => value ⟨origin.factor.succ, origin.root⟩
      have last : List.ofFn (fun index : Fin (blocks remaining images.2).length =>
          common (index.natAdd images.1.blocks.length)) =
          List.ofFn (fun index : Fin (blocks remaining images.2).length =>
            later (ofIndex remaining images.2 index)) := by
        apply OfFn.Basic.ofFn_congr
        intro index
        have beyond : ¬images.1.blocks.length + index.val < images.1.blocks.length :=
          Nat.not_lt_of_ge (Nat.le_add_right _ _)
        change value (ofIndex complete images ⟨images.1.blocks.length + index.val, _⟩) = _
        rewrite [ofIndex, dif_neg beyond]
        have tailBound : images.1.blocks.length + index.val - images.1.blocks.length <
            (blocks remaining images.2).length := by
          rewrite [Nat.add_sub_cancel_left]
          exact index.isLt
        have original : (⟨images.1.blocks.length + index.val - images.1.blocks.length, tailBound⟩ :
            Fin (blocks remaining images.2).length) = index := Fin.ext (Nat.add_sub_cancel_left _ _)
        exact congrArg (fun retained => later (ofIndex remaining images.2 retained)) original
      have split : (List.ofFn read).foldr Nat.add 0 =
          (List.ofFn (fun root : Fin images.1.roots.length => value ⟨0, root⟩)).foldr Nat.add 0 +
          (List.ofFn (fun factor : Fin indices.length =>
            (List.ofFn (fun root : Fin (rootsAt remaining images.2 factor).length =>
              later ⟨factor, root⟩)).foldr Nat.add 0)).foldr Nat.add 0 := by
        rewrite [materialized, OfFn.Basic.ofFn_add, first, last, Fold.foldr_add_append,
          previous images.2 later]
        rfl
      apply split.trans
      rewrite [OfFn.Basic.ofFn_succ]
      rfl

/-- The original vector retaining one factor-root view per original flattened weighted block. -/
abbrev Table (stages : Stages contexts indices K ring equality function) (images : Images stages) :=
  Vec (Origin stages images) (blocks stages images).length

/-- Materialize the original bounded factor-root views once in flattened block order. -/
@[expose] def prepare (stages : Stages contexts indices K ring equality function) (images : Images stages) :
    Table stages images := vectorOfFn (ofIndex stages images)

/-- Each retained vector entry preserves its same original flattened natural position. -/
theorem prepare_position (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (index : Fin (blocks stages images).length) :
    position stages images (prepare stages images index) = index.val := by
  rewrite [prepare, vectorOfFn_apply]
  exact position_ofIndex stages images index

/-- Each retained vector entry reads the same original weighted-block point. -/
theorem prepare_point (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (index : Fin (blocks stages images).length) :
    ((blocks stages images).get index).point = (prepare stages images index).point := by
  rewrite [prepare, vectorOfFn_apply]
  exact point_ofIndex stages images index

/-- Each retained origin view preserves its same original positive-context multiplicity. -/
theorem prepare_multiplicity (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (index : Fin (blocks stages images).length) :
    ((blocks stages images).get index).multiplicity = (prepare stages images index).context.focus.multiplicity := by
  rewrite [prepare, vectorOfFn_apply]
  exact multiplicity_ofIndex stages images index

/-- Folding the same materialized origin vector visits every retained factor-local root occurrence once. -/
theorem fold_prepare (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (value : Origin stages images → Nat) :
    (List.ofFn (fun index : Fin (blocks stages images).length =>
      value (prepare stages images index))).foldr Nat.add 0 =
      (List.ofFn (fun factor : Fin indices.length =>
        (List.ofFn (fun root : Fin (rootsAt stages images factor).length =>
          value ⟨factor, root⟩)).foldr Nat.add 0)).foldr Nat.add 0 := by
  have table : List.ofFn (fun index : Fin (blocks stages images).length => value (prepare stages images index)) =
      List.ofFn (fun index : Fin (blocks stages images).length => value (ofIndex stages images index)) := by
    apply OfFn.Basic.ofFn_congr
    intro index
    rewrite [prepare, vectorOfFn_apply]
    rfl
  exact (congrArg (fun values : List Nat => values.foldr Nat.add 0) table).trans (fold_ofIndex stages images value)

/-- The retained origin fold uses each original focused factor's degree bound on its local coordinate. -/
theorem fold_prepare_degree (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (value : (context : Fin contexts.length) → Fin (contexts.get context).focus.part.polynomial.natDegree → Nat) :
    (List.ofFn (fun index : Fin (blocks stages images).length =>
      let original := prepare stages images index
      value original.contextIndex original.localIndex)).foldr Nat.add 0 =
      (List.ofFn (fun factor : Fin indices.length =>
        (List.ofFn (value (indices.get factor))).foldr Nat.add 0)).foldr Nat.add 0 := by
  apply (fold_prepare stages images (fun original => value original.contextIndex original.localIndex)).trans
  apply congrArg (fun entries : List Nat => entries.foldr Nat.add 0)
  apply OfFn.Basic.ofFn_congr
  intro factor
  apply congrArg (fun entries : List Nat => entries.foldr Nat.add 0)
  apply OfFn.Basic.ofFn_congr_size (rootsAt_length stages images factor)
  intro first second same
  exact congrArg (value (indices.get factor)) (Fin.ext same)

/-- A complete original context enumeration sums every focused-degree occurrence once in original order. -/
theorem fold_prepare_complete (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (complete : indices = List.ofFn (fun index : Fin contexts.length => index))
    (value : (context : Fin contexts.length) → Fin (contexts.get context).focus.part.polynomial.natDegree → Nat) :
    (List.ofFn (fun index : Fin (blocks stages images).length =>
      let original := prepare stages images index
      value original.contextIndex original.localIndex)).foldr Nat.add 0 =
      (List.ofFn (fun context : Fin contexts.length =>
        (List.ofFn (value context)).foldr Nat.add 0)).foldr Nat.add 0 := by
  apply (fold_prepare_degree stages images value).trans
  cases complete
  apply congrArg (fun entries : List Nat => entries.foldr Nat.add 0)
  apply OfFn.Basic.ofFn_congr_size (OfFn.Basic.length_ofFn (function := fun index : Fin contexts.length => index))
  intro first second same
  have original : (List.ofFn (fun index : Fin contexts.length => index)).get first = second :=
    (getElem_congr (Eq.refl (List.ofFn (fun index : Fin contexts.length => index))) same first.isLt).trans
      (OfFn.Basic.getElem_ofFn (fun index : Fin contexts.length => index) second (same ▸ first.isLt))
  cases original
  rfl

end Origin

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images

end
