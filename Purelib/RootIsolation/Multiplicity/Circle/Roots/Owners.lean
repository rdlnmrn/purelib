module

public import Purelib.RootIsolation.Multiplicity.Circle.Inventory
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Bank
public import Purelib.Polynomial.Dense.Roots.Word.Selection
import Purelib.Data.List.Fold
public import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original geometric occurrences of retained formal root blocks

A bounded context and degree coordinate identify the same original geometric
observation and its retained radial state. The formal bank supplies these
coordinates in its original factor-root order. Only ownership and radial
labels are aligned here; no equality between a formal root and a geometric
point, or algebraic admissibility of a geometric label, is asserted.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots
open Purelib.Polynomial.Dense.Roots

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}

set_option genInjectivity false in
/-- The original context occurrence and focused-degree coordinate of one retained geometric owner.

An exact observation has its single coordinate. A higher observation uses
the identical coordinate in its original degree-sized track list. The
original factor and its cached states remain owned by the input inventory.
-/
structure Occurrence (input : PositiveSideInput source opposite) where
  /-- The same original bounded positive-context occurrence. -/
  context : Fin input.contexts.length
  /-- The same original focused-factor degree coordinate. -/
  localRoot : Fin (input.contexts.get context).focus.part.polynomial.natDegree

constructive_injectivity Occurrence

namespace Occurrence

/-- Transport an original cached context and degree coordinate without changing either natural index. -/
@[expose] def ofContext {contexts : List (PositiveContext input.entries)} (same : contexts = input.contexts)
    (context : Fin contexts.length) (root : Fin (contexts.get context).focus.part.polynomial.natDegree) :
    Occurrence input :=
  let original : Fin input.contexts.length := ⟨context.val, (congrArg List.length same) ▸ context.isLt⟩
  let sameContext : contexts.get context = input.contexts.get original :=
    getElem_congr same (Eq.refl context.val) context.isLt
  ⟨original, ⟨root.val, (congrArg (fun value => value.focus.part.polynomial.natDegree) sameContext) ▸ root.isLt⟩⟩

/-- The original context's natural coordinate is preserved by transport. -/
theorem ofContext_context {contexts : List (PositiveContext input.entries)} (same : contexts = input.contexts)
    (context : Fin contexts.length) (root : Fin (contexts.get context).focus.part.polynomial.natDegree) :
    (ofContext same context root).context.val = context.val := rfl

/-- The original local root's natural coordinate is preserved by transport. -/
theorem ofContext_localRoot {contexts : List (PositiveContext input.entries)} (same : contexts = input.contexts)
    (context : Fin contexts.length) (root : Fin (contexts.get context).focus.part.polynomial.natDegree) :
    (ofContext same context root).localRoot.val = root.val := rfl

/-- Read one geometric occurrence from the same retained formal origin, without repeating its enumeration. -/
@[expose] def ofOrigin (prepared : Prepared input)
    (origin : Stages.Images.Origin prepared.separation.prepared.stages prepared.separation.images) :
    Occurrence input :=
  ofContext prepared.separation.prepared.contexts_eq origin.contextIndex origin.localIndex

/-- Read the same retained factor observation and radial payload at its original bounded context. -/
@[expose] def factor (inventory : PositiveInventory clearance input family) (occurrence : Occurrence input) :=
  inventory.factorAt occurrence.context

/-- Read the original cached radial decision at the same focused-degree coordinate. -/
@[expose] def inside (inventory : PositiveInventory clearance input family) (occurrence : Occurrence input) : Bool :=
  let retained := occurrence.factor inventory
  Locations.insideAt retained.observation retained.locations occurrence.localRoot

/-- The original multiplicity attached to the same geometric context occurrence. -/
@[expose] def multiplicity (occurrence : Occurrence input) : Nat :=
  (input.contexts.get occurrence.context).focus.multiplicity

/-- Transporting the original context changes none of its original multiplicity. -/
theorem ofContext_multiplicity {contexts : List (PositiveContext input.entries)} (same : contexts = input.contexts)
    (context : Fin contexts.length) (root : Fin (contexts.get context).focus.part.polynomial.natDegree) :
    (ofContext same context root).multiplicity = (contexts.get context).focus.multiplicity := by
  exact congrArg (fun value => value.focus.multiplicity)
    (getElem_congr same (Eq.refl context.val) context.isLt).symm

/-- Summing same-context occurrence labels gives the original inventory's independently retained weighted count. -/
private theorem fold_contexts (inventory : PositiveInventory clearance input family)
    {contexts : List (PositiveContext input.entries)} (same : contexts = input.contexts) :
    (List.ofFn (fun context : Fin contexts.length =>
      (List.ofFn (fun root : Fin (contexts.get context).focus.part.polynomial.natDegree =>
        (ofContext same context root).multiplicity *
          (if (ofContext same context root).inside inventory then 1 else 0))).foldr Nat.add 0)).foldr Nat.add 0 =
      inventory.insideCount := by
  cases same
  have table : List.ofFn (fun context : Fin input.contexts.length =>
      (List.ofFn (fun root : Fin (input.contexts.get context).focus.part.polynomial.natDegree =>
        (ofContext rfl context root).multiplicity *
          (if (ofContext rfl context root).inside inventory then 1 else 0))).foldr Nat.add 0) =
      List.ofFn (fun context : Fin input.contexts.length =>
        (input.contexts.get context).focus.multiplicity * (inventory.factorAt context).insideCount) := by
    apply OfFn.Basic.ofFn_congr
    intro context
    let retained := inventory.factorAt context
    let labels := List.ofFn (fun root : Fin (input.contexts.get context).focus.part.polynomial.natDegree =>
      if Locations.insideAt retained.observation retained.locations root then (1 : Nat) else 0)
    have entries : List.ofFn (fun root : Fin (input.contexts.get context).focus.part.polynomial.natDegree =>
        (ofContext rfl context root).multiplicity *
          (if (ofContext rfl context root).inside inventory then 1 else 0)) =
        labels.map (fun value => (input.contexts.get context).focus.multiplicity * value) := by
      rewrite [OfFn.Basic.map_ofFn]
      rfl
    apply (congrArg (fun values : List Nat => values.foldr Nat.add 0) entries).trans
    apply (Fold.foldr_add_map_mul_left labels _).trans
    exact congrArg (fun count => (input.contexts.get context).focus.multiplicity * count)
      (Locations.insideAt_sum retained.observation retained.locations)
  apply (congrArg (fun values : List Nat => values.foldr Nat.add 0) table).trans
  exact DependentProduct.sum_ofFn input.contexts inventory.factors
    (fun context retained => (input.contexts.get context).focus.multiplicity * retained.insideCount)
    (fun value : Nat => value)

/-- Original formal-block order visits every same-context geometric coordinate with its original weighted label. -/
theorem fold_origins (prepared : Prepared input) (inventory : PositiveInventory clearance input family) :
    (List.ofFn (fun index : Fin prepared.bank.blocks.length =>
      let occurrence := ofOrigin prepared (prepared.origin index)
      occurrence.multiplicity * (if occurrence.inside inventory then 1 else 0))).foldr Nat.add 0 =
      inventory.insideCount := by
  let retained := prepared.separation.prepared
  let images := prepared.separation.images
  let value := fun (context : Fin retained.contexts.length)
      (root : Fin (retained.contexts.get context).focus.part.polynomial.natDegree) =>
    (ofContext retained.contexts_eq context root).multiplicity *
      (if (ofContext retained.contexts_eq context root).inside inventory then 1 else 0)
  have table : List.ofFn (fun index : Fin prepared.bank.blocks.length =>
      let occurrence := ofOrigin prepared (prepared.origin index)
      occurrence.multiplicity * (if occurrence.inside inventory then 1 else 0)) =
      List.ofFn (fun index : Fin (Stages.Images.blocks retained.stages images).length =>
        let original := Stages.Images.Origin.prepare retained.stages images index
        value original.contextIndex original.localIndex) := by
    apply OfFn.Basic.ofFn_congr_size (congrArg List.length prepared.blocks_eq)
    intro first second same
    unfold Prepared.origin
    rewrite [prepared.origins_eq]
    have original : (⟨first.val, (congrArg List.length prepared.blocks_eq) ▸ first.isLt⟩ :
        Fin (Stages.Images.blocks retained.stages images).length) = second := Fin.ext same
    exact congrArg (fun index =>
      let original := Stages.Images.Origin.prepare retained.stages images index
      value original.contextIndex original.localIndex) original
  apply (congrArg (fun values : List Nat => values.foldr Nat.add 0) table).trans
  exact (Stages.Images.Origin.fold_prepare_complete retained.stages images retained.indices_eq value).trans
    (fold_contexts inventory retained.contexts_eq)

/-- An aligned original occurrence keeps the multiplicity of its same retained formal origin. -/
theorem ofOrigin_multiplicity (prepared : Prepared input)
    (origin : Stages.Images.Origin prepared.separation.prepared.stages prepared.separation.images) :
    (ofOrigin prepared origin).multiplicity = origin.context.focus.multiplicity :=
  ofContext_multiplicity prepared.separation.prepared.contexts_eq origin.contextIndex origin.localIndex

/-- An aligned occurrence keeps the original multiplicity of its same Bank block. -/
theorem block_multiplicity (prepared : Prepared input) (index : Fin prepared.bank.blocks.length) :
    (prepared.bank.block index).multiplicity = (ofOrigin prepared (prepared.origin index)).multiplicity :=
  (prepared.multiplicity_eq_context index).trans (ofOrigin_multiplicity prepared (prepared.origin index)).symm

end Occurrence

set_option genInjectivity false in
/-- The once-materialized geometric occurrences and original weighted word selected by their cached radial labels.

Both the formal Bank and the geometric inventory retain the identical
positive-side input. The original factor and local-root coordinates are
stored once in Bank order. The original word selection consumes their
retained Boolean labels; its count agrees with the independent inventory
fold. These ownership and count laws assert no formal-root realization.
-/
structure Owners (prepared : Prepared input) (inventory : PositiveInventory clearance input family) where
  /-- The actual original context and focused-degree coordinates in formal Bank block order. -/
  occurrences : Vec (Occurrence input) prepared.bank.blocks.length
  /-- Every stored coordinate reads the same already retained original formal origin. -/
  occurrences_eq : occurrences = vectorOfFn (fun index => Occurrence.ofOrigin prepared (prepared.origin index))
  /-- The original multiplicity-expanded word selected once by the stored original radial labels. -/
  selection : Word.Selection prepared.bank
  /-- Each retained selection label reads the same stored occurrence's cached geometric decision. -/
  labels_eq : ∀ index, selection.labels index = (occurrences index).inside inventory
  /-- The selected weighted coordinate count equals the independent original radial inventory count. -/
  count_eq : selection.count = inventory.insideCount

constructive_injectivity Owners

namespace Owners

/-- Materialize the same original owner coordinates and select their weighted original word once.

The builder reads the Bank's cached origin vector and the inventory's cached
radial states. It invokes neither adjunction nor isolation nor refinement.
The original expanded word and its Boolean selection are produced once by
`Word.Selection.prepare` from the retained label vector.
-/
@[expose] def prepare (prepared : Prepared input) (inventory : PositiveInventory clearance input family) :
    Owners prepared inventory := by
  let occurrences := vectorOfFn (fun index => Occurrence.ofOrigin prepared (prepared.origin index))
  let labels := vectorOfFn (fun index => (occurrences index).inside inventory)
  let selection := Word.Selection.prepare prepared.bank labels
  have count : selection.count = inventory.insideCount := by
    apply selection.count_eq.trans
    have table : List.ofFn (fun index : Fin prepared.bank.blocks.length =>
        if labels index then (prepared.bank.block index).multiplicity else 0) =
        List.ofFn (fun index : Fin prepared.bank.blocks.length =>
          let occurrence := Occurrence.ofOrigin prepared (prepared.origin index)
          occurrence.multiplicity * (if occurrence.inside inventory then 1 else 0)) := by
      apply OfFn.Basic.ofFn_congr
      intro index
      have retained : labels index = (Occurrence.ofOrigin prepared (prepared.origin index)).inside inventory := by
        rewrite [vectorOfFn_apply, vectorOfFn_apply]
        rfl
      dsimp only
      rewrite [retained]
      cases chosen : (Occurrence.ofOrigin prepared (prepared.origin index)).inside inventory with
      | false => exact (Nat.mul_zero _).symm
      | true => exact (Occurrence.block_multiplicity prepared index).trans (Nat.mul_one _).symm
    exact (congrArg (fun values : List Nat => values.foldr Nat.add 0) table).trans
      (Occurrence.fold_origins prepared inventory)
  exact
    { occurrences := occurrences, occurrences_eq := rfl, selection := selection
      labels_eq := fun index => vectorOfFn_apply _ index, count_eq := count }

/-- The aligned context index is the original context index of the same retained formal Bank block. -/
theorem context_val {prepared : Prepared input} {inventory : PositiveInventory clearance input family}
    (owners : Owners prepared inventory) (index : Fin prepared.bank.blocks.length) :
    (owners.occurrences index).context.val = (prepared.contextIndex index).val := by
  rewrite [owners.occurrences_eq, vectorOfFn_apply]
  rfl

/-- The aligned local-root index is the original retained factor-root occurrence of the same Bank block. -/
theorem localRoot_val {prepared : Prepared input} {inventory : PositiveInventory clearance input family}
    (owners : Owners prepared inventory) (index : Fin prepared.bank.blocks.length) :
    (owners.occurrences index).localRoot.val = (prepared.origin index).root.val := by
  rewrite [owners.occurrences_eq, vectorOfFn_apply]
  rfl

/-- The actual selected word length equals the independent original multiplicity-weighted inside count. -/
theorem length_eq {prepared : Prepared input} {inventory : PositiveInventory clearance input family}
    (owners : Owners prepared inventory) : owners.selection.word.length = inventory.insideCount :=
  owners.selection.length_eq.trans owners.count_eq

/-- Every accepted original word occurrence carries the same retained strict inside decision. -/
theorem accepted {prepared : Prepared input} {inventory : PositiveInventory clearance input family}
    (owners : Owners prepared inventory) (index : Fin owners.selection.word.length) :
    (owners.occurrences (owners.selection.word[index.val]'index.isLt)).inside inventory = true :=
  (owners.labels_eq _).symm.trans (owners.selection.accepted index)

end Owners

end Purelib.RootIsolation.Multiplicity.Circle.Roots

end
