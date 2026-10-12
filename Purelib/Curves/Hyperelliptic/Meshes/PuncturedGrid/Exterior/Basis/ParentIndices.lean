module
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

public section

/-! Embed retained occurrence positions into the original common parent bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices

open Purelib.Data.List

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- Flatten the parent caches in retained surface-occurrence order.

Each occurrence contributes its cached parent list unchanged. Mapping and flattening preserve the order of occurrences,
the order within each cache and repeated parent data. -/
@[expose] def occurrenceParents (occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)) :=
  (occurrences.map (fun occurrence => occurrence.compared.entered.cache.parents)).flatten

/-- Read an original surface occurrence using its retained finite index bound. -/
@[expose] def occurrenceAt (occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential))
    (index : Fin occurrences.length) := occurrences[index.val]'index.isLt

/-- Embed an occurrence-local parent index into the complete original flattened parent list.

The construction uses prefix lengths and preserves distinct positions even when parent data repeat. -/
@[expose] def embed : (occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)) →
    (outer : Fin occurrences.length) →
    Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt occurrences
      outer).compared.entered.cache.parents.length →
    Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents occurrences).length
  | [], outer, _ => Fin.elim0 outer
  | head :: tail, ⟨0, _⟩, inner =>
      ⟨inner.val, by
        simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents,
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt, List.getElem_cons_zero,
          List.map_cons, List.flatten_cons, Append.length_append] using
          Nat.lt_add_right (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents
            tail).length inner.isLt⟩
  | head :: tail, ⟨outer + 1, bound⟩, inner =>
      let next := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed tail ⟨outer,
        Nat.lt_of_succ_lt_succ bound⟩ inner
      ⟨head.compared.entered.cache.parents.length + next.val,
        by
          simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents, List.map_cons,
            List.flatten_cons, Append.length_append] using
            Nat.add_lt_add_left next.isLt head.compared.entered.cache.parents.length⟩

/-- The embedded parent index is its local index plus the length of all preceding occurrence caches.

Structural recursion accumulates exactly the retained prefix lengths. The resulting natural offset identifies a position
even when earlier occurrences contain repeated or empty parent caches. -/
private theorem embed_val (occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential))
    (outer : Fin occurrences.length)
    (inner : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt occurrences
      outer).compared.entered.cache.parents.length) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed occurrences outer inner).val =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents (occurrences.take
      outer.val)).length + inner.val := by
  induction occurrences with
  | nil => exact Fin.elim0 outer
  | cons head tail ih =>
    rcases outer with ⟨outer, bound⟩
    cases outer with
    | zero => exact (Nat.zero_add inner.val).symm
    | succ outer =>
      change head.compared.entered.cache.parents.length +
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed tail ⟨outer, Nat.lt_of_succ_lt_succ
        bound⟩ inner).val = _
      rw [ih ⟨outer, Nat.lt_of_succ_lt_succ bound⟩ inner]
      simp only [List.take_succ_cons, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents,
        List.map_cons, List.flatten_cons, Append.length_append,
        Nat.add_assoc, -eq_self]
      rfl

/-- Reading an embedded position returns the same occurrence-local parent.

The supplied outer and inner bounds retain their original occurrences. Bounded concatenation readback removes the
accumulated prefix and reads that exact cached parent without searching for equal data. -/
private theorem embed_read : ∀ (occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential))
    (outer : Fin occurrences.length)
    (inner : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt occurrences
      outer).compared.entered.cache.parents.length),
    Integration.PreparedParentSplitSelection.parentAt
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents occurrences)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed occurrences outer inner) =
      Integration.PreparedParentSplitSelection.parentAt
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt occurrences
        outer).compared.entered.cache.parents inner
  | [], outer, _ => Fin.elim0 outer
  | head :: tail, ⟨0, _⟩, inner => Append.getElem_append_left _ _ inner.val inner.isLt _
  | head :: tail, ⟨outer + 1, bound⟩, inner => by
      let next := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed tail ⟨outer,
        Nat.lt_of_succ_lt_succ bound⟩ inner
      change (head.compared.entered.cache.parents ++
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents
        tail)[head.compared.entered.cache.parents.length + next.val]'(by
        rw [Append.length_append]
        exact Nat.add_lt_add_left next.isLt head.compared.entered.cache.parents.length) = _
      exact (Append.getElem_append_right _ _ next.val next.isLt _).trans
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed_read tail ⟨outer,
          Nat.lt_of_succ_lt_succ bound⟩ inner)

/-- Enumerating through an equality transport of finite indices preserves the complete ordered list. -/
private theorem ofFn_cast {Item : Type u} {first last : Nat} (equal : first = last)
    (values : Fin last → Item) :
    List.ofFn (fun position : Fin first => values (Fin.cast equal position)) = List.ofFn values := by
  cases equal
  rfl

/-- Enumerating each retained occurrence and then its parents is exactly the
original flattened enumeration, including empty occurrences and repeated data. -/
private theorem embed_all {Item : Type u}
    (occurrences : List
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
      regular domains differential))
    (values : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents occurrences).length
      → Item) :
    (List.ofFn (fun outer : Fin occurrences.length =>
      List.ofFn (fun inner => values (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed occurrences
        outer inner)))).flatten = List.ofFn values := open Purelib in by
  induction occurrences with
  | nil => rfl
  | cons head tail ih =>
    rw [Data.List.OfFn.Basic.ofFn_succ, List.flatten_cons]
    let count := head.compared.entered.cache.parents.length
    have lengthEq : count + (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents
      tail).length =
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents (head :: tail)).length :=
          (Append.length_append ..).symm
    let shifted (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents
      tail).length) : Item :=
      values (Fin.cast lengthEq (position.natAdd count))
    have remaining := ih shifted
    have tailEq :
        (List.ofFn (fun outer : Fin tail.length => List.ofFn (fun inner =>
          values (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed (head :: tail) outer.succ
            inner)))).flatten = List.ofFn shifted := by
      exact remaining
    rw [tailEq]
    have full := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.ofFn_cast lengthEq values
    rw [Data.List.OfFn.Basic.ofFn_add] at full
    exact full

/-- Transporting a parent index along list equality preserves its exact parent readback. -/
private theorem parentAt_cast
    {first last : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} (equal : first =
      last)
    (index : Fin first.length) : Integration.PreparedParentSplitSelection.parentAt last (Fin.cast (congrArg List.length
      equal) index) = Integration.PreparedParentSplitSelection.parentAt first index := by
  cases equal
  rfl

variable {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential}
  (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  regular domains program)

/-- The local position is embedded by its occurrence prefix, not by equality
search on parent data. Repeated parents retain distinct positions. -/
@[expose] def parentIndex (outer : Fin prepared.occurrences.length)
    (inner : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    Fin program.cache.parents.length :=
  Fin.cast (congrArg List.length prepared.parents_eq)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed prepared.occurrences outer inner)

/-- The selected program-cache position reads the original occurrence-local parent. -/
theorem parentIndex_read (outer : Fin prepared.occurrences.length)
    (inner : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    Integration.PreparedParentSplitSelection.parentAt program.cache.parents
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex prepared outer inner) =
      Integration.PreparedParentSplitSelection.parentAt
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents inner :=
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentAt_cast prepared.parents_eq
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed prepared.occurrences outer inner)).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed_read prepared.occurrences outer inner)

/-- The program-cache index is exactly the preceding occurrence-prefix length plus its local index. -/
theorem parentIndex_val (outer : Fin prepared.occurrences.length)
    (inner : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex prepared outer inner).val =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceParents (prepared.occurrences.take
        outer.val)).length + inner.val :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed_val prepared.occurrences outer inner

/-- Positional selection commutes with flattening the retained occurrence bank. -/
theorem parentIndex_all {Item : Type u} (values : Fin program.cache.parents.length → Item) :
    (List.ofFn (fun outer : Fin prepared.occurrences.length =>
      List.ofFn (fun inner => values (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex
        prepared outer inner)))).flatten = List.ofFn values :=
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.embed_all prepared.occurrences (fun position =>
    values (Fin.cast (congrArg List.length prepared.parents_eq) position))).trans
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.ofFn_cast (congrArg List.length
        prepared.parents_eq) values)

/-- A canonical mesh block selects the same original parent position consumed
by the component's common-basis numerical bank. -/
@[expose] def blockIndex (outer : Fin prepared.occurrences.length)
    {vertical forward : Bool} {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (block : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) vertical
      forward physical) :
    Fin program.cache.parents.length := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex
      prepared outer block.index

/-- The common-bank position selected by a physical block reads its exact original cached parent. -/
theorem blockIndex_read (outer : Fin prepared.occurrences.length)
    {vertical forward : Bool} {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (block : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) vertical
      forward physical) :
    Integration.PreparedParentSplitSelection.parentAt program.cache.parents
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.blockIndex prepared outer block) =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
        block.index :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex_read prepared outer block.index

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
