module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
public import Purelib.Data.List.DependentProduct
public import Purelib.Riemann.Integration.PreparedCoveredParentLists
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Integration.PreparedCoveredParentLists.Entries
import Purelib.Data.List.Append
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility

/-! # Stored original six-channel sources at covered parent occurrences

The existing dependent list product stores one completed parent preparation
per original occurrence. Each entry reuses that occurrence's retained
covering patch and finish witness. Lookup reads the stored source request,
endpoint plans, physical cells and observations without running a producer.
An ordered Source.Path or a continued-sheet bank admission is separate.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Riemann.Integration
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}

/-- Original occurrence-indexed source preparations on the identical finite covered-parent list.

The existing list product retains actual entries instead of a function that
would repeat endpoint queries or source selections for different rows. Its
family preserves each exact original parent, patch and endpoint admission.
-/
abbrev PreparedParents (covered : CoveredParents count parents) (floor : Nat)
    (targets : CellEndpoints.Targets original stage) :=
  DependentProduct parents (fun index => PreparedParent (covered.entry index).1 count floor
    (covered.entry index).2 targets)

namespace PreparedParents

variable {covered : CoveredParents count parents} {floor : Nat}
variable {targets : CellEndpoints.Targets original stage}

/-- Transport the complete retained preparation product along an exact equality of its original target cache.

Equality elimination changes only the nominal target index. Every source,
request, endpoint owner, selected model and query remains the original data;
no preparation factory or point request is executed.
-/
@[expose] def castTargets {replacement : CellEndpoints.Targets original stage}
    (prepared : PreparedParents covered floor targets) (equal : targets = replacement) :
    PreparedParents covered floor replacement := by
  cases equal
  exact prepared

/-- Transport the complete retained product along equality of its original covering spine.

Both covers have the same original parent list. Equality elimination retains
all patches, source requests, endpoint owners and stored cache entries;
no parent preparation or observation factory is evaluated.
-/
@[expose] def castCover {replacement : CoveredParents count parents}
    (prepared : PreparedParents covered floor targets) (equal : covered = replacement) :
    PreparedParents replacement floor targets := by
  cases equal
  exact prepared

/-- Append the two exact stored preparation products under the same original covered-parent append. -/
@[expose] def append : {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (firstCover : CoveredParents count first) → (lastCover : CoveredParents count last) →
    PreparedParents firstCover floor targets → PreparedParents lastCover floor targets →
    PreparedParents (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover) floor targets
  | [], _, .nil, lastCover, _, last =>
      last.castCover (PreparedCoveredParentLists.CoveredParents.append_nil lastCover).symm
  | _ :: _, _, .cons patch inside remaining, lastCover, first, last =>
      castCover
        (⟨first.1, append remaining lastCover first.2 last⟩ :
          PreparedParents (CoveredParents.cons patch inside
            (PreparedCoveredParentLists.CoveredParents.append remaining lastCover)) floor targets)
        (PreparedCoveredParentLists.CoveredParents.append_cons patch inside remaining lastCover).symm

/-- The actual appended source has the original selected head cell and unchanged appended tail. -/
theorem append_cons {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last)
    (head : PreparedParent patch count floor inside targets)
    (firstPrepared : PreparedParents firstCover floor targets)
    (lastPrepared : PreparedParents lastCover floor targets) :
    append (CoveredParents.cons patch inside firstCover) lastCover ⟨head, firstPrepared⟩ lastPrepared =
      castCover (covered := CoveredParents.cons patch inside
          (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover))
        (⟨head, append firstCover lastCover firstPrepared lastPrepared⟩ :
          PreparedParents (CoveredParents.cons patch inside
            (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover)) floor targets)
        (PreparedCoveredParentLists.CoveredParents.append_cons patch inside firstCover lastCover).symm := (rfl)

/-- Read one completed original parent cache at its exact bounded list occurrence without another query. -/
@[expose] def entry (prepared : PreparedParents covered floor targets) (index : Fin parents.length) :
    PreparedParent (covered.entry index).1 count floor (covered.entry index).2 targets :=
  DependentProduct.get parents prepared index

/-- Cover-index transport preserves the same complete retained entry at its original bounded occurrence. -/
theorem entry_castCover {replacement : CoveredParents count parents}
    (prepared : PreparedParents covered floor targets) (equal : covered = replacement)
    (index : Fin parents.length) :
    HEq ((prepared.castCover equal).entry index) (prepared.entry index) := by
  cases equal
  rfl

/-- Transport a complete original cover and source-preparation product through their SAME parent-list equality.

The dependent pair moves as a whole. Every original patch, endpoint
containment, prepared source, request and cache is retained; no covering
or source factory is evaluated.
-/
@[expose] def castParents {nextParents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (equal : parents = nextParents) (originalCovered : CoveredParents count parents)
    (prepared : PreparedParents originalCovered floor targets) :
    Σ nextCovered : CoveredParents count nextParents, PreparedParents nextCovered floor targets := by
  cases equal
  exact ⟨originalCovered, prepared⟩

/-- Parent-list transport preserves the complete old dependent cover/source pair heterogeneously. -/
theorem castParents_heq {nextParents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (equal : parents = nextParents) (originalCovered : CoveredParents count parents)
    (prepared : PreparedParents originalCovered floor targets) :
    HEq (castParents equal originalCovered prepared)
      (⟨originalCovered, prepared⟩ : Σ kept : CoveredParents count parents, PreparedParents kept floor targets) := by
  cases equal
  rfl

section Cells

open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

/-- Read the ordered whole physical CellModels from an actual retained source preparation product.

The original dependent product supplies each complete source cell cache.
Only a list spine is allocated; no source request, point, root, model or
observation is acquired by this projection.
-/
def cells (prepared : PreparedParents covered floor targets) (channel : Fin 6) : List CellModel :=
  DependentProduct.mapToList parents prepared (fun _ entry => entry.preparation.cell.models.cell channel)

/-- The empty original source bank contains no physical cell. -/
theorem cells_nil (channel : Fin 6) :
    cells (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      (covered := .nil) PUnit.unit channel = [] := (rfl)

/-- The first retained whole physical cell precedes the identical original source-product tail. -/
theorem cells_cons {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count remaining) (head : PreparedParent patch count floor inside targets)
    (tail : PreparedParents covered floor targets) (channel : Fin 6) :
    cells (covered := CoveredParents.cons patch inside covered) ⟨head, tail⟩ channel =
      head.preparation.cell.models.cell channel :: cells tail channel := (rfl)

end Cells

section PrefixSuffix

open Purelib.Riemann.Paths

/-- Cut the retained source product at a finite parent count without preparing any source again.

The original prefix and suffix covers determine both returned products.
Each whole prepared parent is reused, and a zero cut returns the literal
original suffix. Counts beyond the list retain the whole finite prefix.
Both products keep the same original endpoint targets and source floor.
-/
@[expose] def splitAt : (steps : Nat) → {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → PreparedParents covered floor targets →
    PreparedParents (PreparedPathParentCaches.CoveredParents.take steps covered) floor targets ×
      PreparedParents (PreparedPathParentCaches.CoveredParents.drop steps covered) floor targets
  | 0, _, _, prepared => ⟨PUnit.unit, prepared⟩
  | _ + 1, [], .nil, _ => ⟨PUnit.unit, PUnit.unit⟩
  | steps + 1, _ :: _, .cons _ _ covered, prepared =>
      let remaining := splitAt steps covered prepared.2
      ⟨⟨prepared.1, remaining.1⟩, remaining.2⟩

/-- A zero cut retains the whole original source bank as its exact suffix. -/
theorem splitAt_zero (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets) :
    splitAt 0 covered prepared = ⟨PUnit.unit, prepared⟩ := (rfl)

/-- Cutting the retained source product preserves its whole physical cell list in original order.

The two returned products read the same complete cached cells for every
channel. Repeated entries, original source stages and both sides of the cut
remain in their literal occurrence order.
-/
theorem cells_splitAt : (steps : Nat) → {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (channel : Fin 6) →
    cells prepared channel = cells (splitAt steps covered prepared).1 channel ++
      cells (splitAt steps covered prepared).2 channel
  | 0, _, _, _, _ => rfl
  | _ + 1, [], .nil, _, _ => rfl
  | steps + 1, _ :: _, .cons _ _ covered, prepared, channel => by
      change prepared.1.preparation.cell.models.cell channel :: cells prepared.2 channel =
        prepared.1.preparation.cell.models.cell channel ::
          (cells (splitAt steps covered prepared.2).1 channel ++ cells (splitAt steps covered prepared.2).2 channel)
      exact congrArg (List.cons (prepared.1.preparation.cell.models.cell channel))
        (cells_splitAt steps covered prepared.2 channel)

end PrefixSuffix

section Split

open Purelib.Riemann.Integration
open Purelib.Data.List

/-- The exact parent and patch of one original prepared occurrence. -/
private def Entry :=
  Σ parent : CenteredEdge (Fibre.frameCurve frame) basis,
    {patch : PreparedPatch parent // (patch.neighborhood count).box.Contains (parent.edge.point 1)}

/-- Equal original parents and whole covering entries identify the same dependent occurrence. -/
private theorem Entry.mk_eq
    {first last : CenteredEdge (Fibre.frameCurve frame) basis} (parentEq : first = last)
    (left : {patch : PreparedPatch first // (patch.neighborhood count).box.Contains (first.edge.point 1)})
    (right : {patch : PreparedPatch last // (patch.neighborhood count).box.Contains (last.edge.point 1)})
    (same : HEq left right) :
    (⟨first, left⟩ : Entry (frame := frame) (basis := basis) (count := count)) = ⟨last, right⟩ := by
  cases parentEq
  have identical := eq_of_heq same
  cases identical
  rfl

/-- The whole original source-preparation type at that unchanged occurrence. -/
private def Entry.prepared (entry : Entry (frame := frame) (basis := basis) (count := count)) :=
  PreparedParent entry.2.val count floor entry.2.property targets

/-- Equality of a whole original occurrence identifies its original prepared-parent type. -/
private theorem Entry.type_eq
    (left right : Entry (frame := frame) (basis := basis) (count := count)) (same : left = right) :
    PreparedParent left.2.val count floor left.2.property targets =
      PreparedParent right.2.val count floor right.2.property targets := by
  cases same
  rfl

/-- Read one complete stored physical cell at the supplied exact original occurrence. -/
private def Entry.cell (entry : Entry (frame := frame) (basis := basis) (count := count))
    (value : Entry.prepared (frame := frame) (basis := basis) (count := count)
      (floor := floor) (targets := targets) entry) (channel : Fin 6) :
    Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel :=
  let actual : PreparedParent entry.2.val count floor entry.2.property targets := value
  actual.preparation.cell.models.cell channel

/-- Equality of the original parent/patch occurrence transports its same complete physical cell. -/
private theorem Entry.cell_transport
    {left right : Entry (frame := frame) (basis := basis) (count := count)} (same : left = right)
    (value : Entry.prepared (frame := frame) (basis := basis) (count := count)
      (floor := floor) (targets := targets) left) (channel : Fin 6) :
    Entry.cell (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets) right
      (cast (congrArg (Entry.prepared (frame := frame) (basis := basis) (count := count)
        (floor := floor) (targets := targets)) same) value) channel =
    Entry.cell (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      left value channel := by
  cases same
  rfl

/-- The exact left append occurrence retains its original complete parent and patch. -/
private theorem leftEntry_eq
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last) (index : Fin first.length) :
    (⟨(first ++ last)[(DependentProduct.leftIndex first last index).val]'
        (DependentProduct.leftIndex first last index).isLt,
      (firstCover.append lastCover).entry (DependentProduct.leftIndex first last index)⟩ :
        Entry (frame := frame) (basis := basis) (count := count)) =
      ⟨first[index.val]'index.isLt, firstCover.entry index⟩ := by
  let global := DependentProduct.leftIndex first last index
  have valueEq : global.val = index.val := DependentProduct.leftIndex_val first last index
  have bound : index.val < (first ++ last).length :=
    Eq.mp (congrArg (fun value => value < (first ++ last).length) valueEq) global.isLt
  let fixed : Fin (first ++ last).length := ⟨index.val, bound⟩
  have indices : global = fixed := Fin.ext valueEq
  have parentsEq := (congrArg
    (fun actual : Fin (first ++ last).length => (first ++ last)[actual.val]'actual.isLt) indices).trans
      (Append.getElem_append_left first last index.val index.isLt bound)
  have same := ((firstCover.append lastCover).entry_congr indices).trans
    (PreparedCoveredParentLists.CoveredParents.entry_append_left
      firstCover lastCover index bound)
  exact Entry.mk_eq parentsEq _ _ same

/-- The exact left append occurrence has the same original prepared-parent type. -/
private theorem leftType_eq
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last) (index : Fin first.length) :
    PreparedParent ((firstCover.append lastCover).entry (DependentProduct.leftIndex first last index)).val
        count floor ((firstCover.append lastCover).entry (DependentProduct.leftIndex first last index)).property
        targets =
      PreparedParent (firstCover.entry index).val count floor (firstCover.entry index).property targets :=
  Entry.type_eq (floor := floor) (targets := targets)
    ⟨(first ++ last)[(DependentProduct.leftIndex first last index).val]'
      (DependentProduct.leftIndex first last index).isLt,
      (firstCover.append lastCover).entry (DependentProduct.leftIndex first last index)⟩
    ⟨first[index.val]'index.isLt, firstCover.entry index⟩ (leftEntry_eq firstCover lastCover index)

/-- The exact right append occurrence retains its original complete parent and patch. -/
private theorem rightEntry_eq
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last) (index : Fin last.length) :
    (⟨(first ++ last)[(DependentProduct.rightIndex first last index).val]'
        (DependentProduct.rightIndex first last index).isLt,
      (firstCover.append lastCover).entry (DependentProduct.rightIndex first last index)⟩ :
        Entry (frame := frame) (basis := basis) (count := count)) =
      ⟨last[index.val]'index.isLt, lastCover.entry index⟩ := by
  let global := DependentProduct.rightIndex first last index
  have valueEq : global.val = first.length + index.val := DependentProduct.rightIndex_val first last index
  have bound : first.length + index.val < (first ++ last).length :=
    Eq.mp (congrArg (fun value => value < (first ++ last).length) valueEq) global.isLt
  let fixed : Fin (first ++ last).length := ⟨first.length + index.val, bound⟩
  have indices : global = fixed := Fin.ext valueEq
  have parentsEq := (congrArg
    (fun actual : Fin (first ++ last).length => (first ++ last)[actual.val]'actual.isLt) indices).trans
      (Append.getElem_append_right first last index.val index.isLt bound)
  have same := ((firstCover.append lastCover).entry_congr indices).trans
    (PreparedCoveredParentLists.CoveredParents.entry_append_right
      firstCover lastCover index bound)
  exact Entry.mk_eq parentsEq _ _ same

/-- The exact right append occurrence has the same original prepared-parent type. -/
private theorem rightType_eq
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last) (index : Fin last.length) :
    PreparedParent ((firstCover.append lastCover).entry (DependentProduct.rightIndex first last index)).val
        count floor ((firstCover.append lastCover).entry (DependentProduct.rightIndex first last index)).property
        targets =
      PreparedParent (lastCover.entry index).val count floor (lastCover.entry index).property targets :=
  Entry.type_eq (floor := floor) (targets := targets)
    ⟨(first ++ last)[(DependentProduct.rightIndex first last index).val]'
      (DependentProduct.rightIndex first last index).isLt,
      (firstCover.append lastCover).entry (DependentProduct.rightIndex first last index)⟩
    ⟨last[index.val]'index.isLt, lastCover.entry index⟩ (rightEntry_eq firstCover lastCover index)

/-- Split one actual global source bank at its original cached cover boundary.

The original product split retains each complete left entry and the literal
whole suffix. Erased type transports identify the exact original covering
patches. Both rows keep the same global Targets and floor; no Point,
request, source, model or observation is constructed or refined.
-/
def split {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last)
    (prepared : PreparedParents (firstCover.append lastCover) floor targets) :
    PreparedParents firstCover floor targets × PreparedParents lastCover floor targets :=
  let divided := DependentProduct.split first last prepared
  ⟨DependentProduct.transport first (leftType_eq firstCover lastCover) divided.1,
    DependentProduct.transport last (rightType_eq firstCover lastCover) divided.2⟩

/-- A split left lookup is the same complete original prepared parent at its bounded global occurrence. -/
theorem entry_split_left {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last)
    (prepared : PreparedParents (firstCover.append lastCover) floor targets) (index : Fin first.length) :
    HEq ((split firstCover lastCover prepared).1.entry index)
      (prepared.entry (DependentProduct.leftIndex first last index)) := by
  unfold split entry
  dsimp only
  exact (DependentProduct.get_transport first (leftType_eq firstCover lastCover)
    (DependentProduct.split first last prepared).1 index).trans
      (heq_of_eq (DependentProduct.get_split_left first last prepared index))

/-- A split right lookup is the same complete original prepared parent in the literal retained suffix. -/
theorem entry_split_right {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last)
    (prepared : PreparedParents (firstCover.append lastCover) floor targets) (index : Fin last.length) :
    HEq ((split firstCover lastCover prepared).2.entry index)
      (prepared.entry (DependentProduct.rightIndex first last index)) := by
  unfold split entry
  dsimp only
  exact (DependentProduct.get_transport last (rightType_eq firstCover lastCover)
    (DependentProduct.split first last prepared).2 index).trans
      (heq_of_eq (DependentProduct.get_split_right first last prepared index))

/-- Splitting one retained source product preserves its entire original ordered physical cell list.

Both actual subproducts keep the same global endpoint Targets and source
floor. Only original covering-entry transports change dependent indices;
every returned CellModel is the supplied stored value.
-/
theorem split_cells {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last)
    (prepared : PreparedParents (firstCover.append lastCover) floor targets) (channel : Fin 6) :
    cells prepared channel = cells (split firstCover lastCover prepared).1 channel ++
      cells (split firstCover lastCover prepared).2 channel := by
  let divided := DependentProduct.split first last prepared
  have firstMapped := DependentProduct.mapToList_transport first (leftType_eq firstCover lastCover) divided.1
    (fun _ entry => entry.preparation.cell.models.cell channel)
  have firstSame := DependentProduct.mapToList_congr first divided.1
    (fun index entry => (cast (leftType_eq firstCover lastCover index) entry).preparation.cell.models.cell channel)
    (fun _ entry => entry.preparation.cell.models.cell channel)
    (fun index entry => Entry.cell_transport (leftEntry_eq firstCover lastCover index) entry channel)
  have lastMapped := DependentProduct.mapToList_transport last (rightType_eq firstCover lastCover) divided.2
    (fun _ entry => entry.preparation.cell.models.cell channel)
  have lastSame := DependentProduct.mapToList_congr last divided.2
    (fun index entry => (cast (rightType_eq firstCover lastCover index) entry).preparation.cell.models.cell channel)
    (fun _ entry => entry.preparation.cell.models.cell channel)
    (fun index entry => Entry.cell_transport (rightEntry_eq firstCover lastCover index) entry channel)
  have global := DependentProduct.mapToList_split first last prepared
    (fun _ entry => entry.preparation.cell.models.cell channel)
  have firstFinal : cells (frame := frame) (basis := basis) (count := count) (floor := floor)
      (parents := first) (covered := firstCover) (targets := targets)
      (split firstCover lastCover prepared).1 channel =
      DependentProduct.mapToList first divided.1 (fun _ entry => entry.preparation.cell.models.cell channel) :=
    by
      dsimp only [cells, split]
      exact firstMapped.trans firstSame
  have lastFinal : cells (frame := frame) (basis := basis) (count := count) (floor := floor)
      (parents := last) (covered := lastCover) (targets := targets)
      (split firstCover lastCover prepared).2 channel =
      DependentProduct.mapToList last divided.2 (fun _ entry => entry.preparation.cell.models.cell channel) :=
    by
      dsimp only [cells, split]
      exact lastMapped.trans lastSame
  have joined := (congrArg (fun left => left ++
    DependentProduct.mapToList last divided.2 (fun _ entry => entry.preparation.cell.models.cell channel))
      firstFinal).symm.trans
        (congrArg (List.append (cells (frame := frame) (basis := basis) (count := count) (floor := floor)
          (parents := first) (covered := firstCover) (targets := targets)
          (split firstCover lastCover prepared).1 channel)) lastFinal.symm)
  exact global.trans joined

end Split

/-- Exact parent-list transport retains the whole original preparation at the SAME bounded occurrence.

Both finite indices carry their original list bounds. Their equal
natural coordinate identifies the occurrence after the whole covering
and prepared-source pair is transported; no Point or model is prepared.
-/
theorem castParents_entry_heq {nextParents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (equal : parents = nextParents) (originalCovered : CoveredParents count parents)
    (prepared : PreparedParents originalCovered floor targets)
    (first : Fin parents.length) (last : Fin nextParents.length) (same : first.val = last.val) :
    HEq ((castParents equal originalCovered prepared).2.entry last) (prepared.entry first) := by
  cases equal
  have equalIndex : first = last := Fin.ext same
  cases equalIndex
  rfl

end PreparedParents

/-- Materialize each covered occurrence's actual two-endpoint and six-channel source construction exactly once.

The original count and path allocations are shared. Each entry takes its
patch and finish witness from the supplied original coverage spine; no
covering seed, continued source owner or six-channel model is reconstructed
when a stored entry is subsequently read.
-/
def prepareCovered (covered : CoveredParents count parents) (floor : Nat)
    (targets : CellEndpoints.Targets original stage) : PreparedParents covered floor targets :=
  DependentProduct.ofFn parents (fun index =>
    let retained := covered.entry index
    prepareParent retained.1 count floor retained.2 targets)

/-- The canonical preparation stores the original head factory and the same canonical tail as one whole product.

The cover constructor and original successor occurrences determine both
parts. Every prepared Point, Vertex, request and model is retained in the
same product; this law does not run another preparation.
-/
theorem prepareCovered_cons {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count remaining) (floor : Nat) (targets : CellEndpoints.Targets original stage) :
    prepareCovered (CoveredParents.cons patch inside covered) floor targets =
      (⟨prepareParent patch count floor inside targets, prepareCovered covered floor targets⟩ :
        PreparedParents (CoveredParents.cons patch inside covered) floor targets) := by
  unfold prepareCovered
  rfl

/-- A materialized occurrence retains the complete original parent factory with all its selected caches. -/
theorem prepareCovered_entry (covered : CoveredParents count parents) (floor : Nat)
    (targets : CellEndpoints.Targets original stage) (index : Fin parents.length) :
    (prepareCovered covered floor targets).entry index =
      prepareParent (covered.entry index).1 count floor (covered.entry index).2 targets :=
  DependentProduct.get_ofFn parents (fun index =>
    let retained := covered.entry index
    prepareParent retained.1 count floor retained.2 targets) index

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
