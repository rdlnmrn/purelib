module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.Nat.Subtraction

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
public import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves

open Purelib.Riemann

@[expose] public section

/-! Locate the actual closed-bank parent in the retained surface occurrence
spine. Positional selection preserves repeated parents and cached splits. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- Flatten the original parent caches in retained surface-occurrence order. -/
def occurrenceParents (occurrences : List
  (ExteriorProgram.SurfaceOccurrence
  regular domains differential)) :=
  (occurrences.map (fun occurrence => occurrence.compared.entered.cache.parents)).flatten

set_option genInjectivity false in
/-- An original occurrence and local cache index identifying the supplied parent.

The occurrence membership and exact parent readback preserve position and repeated parent data. -/
structure LocatedParent (occurrences : List
  (ExteriorProgram.SurfaceOccurrence
  regular domains differential))
    (parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential) where
  /-- The original surface occurrence containing the selected parent position. -/ occurrence :
    ExteriorProgram.SurfaceOccurrence
    regular domains differential
  /-- The retained occurrence belongs to the supplied original occurrence list. -/ member : occurrence ∈ occurrences
  /-- The bounded original parent position inside that occurrence's cache. -/ index : Fin
    occurrence.compared.entered.cache.parents.length
  /-- The supplied parent is exactly the cache entry at the retained local index. -/ parent_eq : parent =
    Integration.PreparedParentSplitSelection.parentAt occurrence.compared.entered.cache.parents index

constructive_injectivity LocatedParent

/-- Locate a flattened parent position in the original occurrence spine by prefix lengths.

The result retains the actual occurrence and its bounded local cache index. -/
def locate : (occurrences : List
  (ExteriorProgram.SurfaceOccurrence
  regular domains differential)) →
    (index : Fin (BoundaryParentLocation.occurrenceParents
      occurrences).length) →
    LocatedParent occurrences
      (Integration.PreparedParentSplitSelection.parentAt
      (BoundaryParentLocation.occurrenceParents occurrences) index)
  | [], index => Fin.elim0 index
  | head :: tail, index => by
      have bound : index.val < head.compared.entered.cache.parents.length +
        (BoundaryParentLocation.occurrenceParents tail).length := by
        have retained := index.isLt
        simp only [BoundaryParentLocation.occurrenceParents, -eq_self,
          -iff_self] at retained
        change index.val < (head.compared.entered.cache.parents ++
          BoundaryParentLocation.occurrenceParents tail).length at retained
        rw [Data.List.Append.length_append] at retained
        exact retained
      if inside : index.val < head.compared.entered.cache.parents.length then
        refine ⟨head, List.Mem.head _, ⟨index.val, inside⟩, ?_⟩
        exact Data.List.Append.getElem_append_left
          head.compared.entered.cache.parents
          (BoundaryParentLocation.occurrenceParents tail)
          index.val inside index.isLt
      else
        have after : head.compared.entered.cache.parents.length ≤ index.val := Nat.le_of_not_lt inside
        let next : Fin (BoundaryParentLocation.occurrenceParents
          tail).length :=
          ⟨index.val - head.compared.entered.cache.parents.length, Data.Nat.Subtraction.sub_lt_left_of_lt_add after
            bound⟩
        let found := BoundaryParentLocation.locate tail next
        refine ⟨found.occurrence, List.Mem.tail _ found.member, found.index, ?_⟩
        have offset : head.compared.entered.cache.parents.length +
            (index.val - head.compared.entered.cache.parents.length) = index.val :=
          Data.Nat.Subtraction.add_sub_of_le after
        have shiftedBound : head.compared.entered.cache.parents.length +
            (index.val - head.compared.entered.cache.parents.length) <
            (head.compared.entered.cache.parents ++
              BoundaryParentLocation.occurrenceParents tail).length :=
          offset.symm ▸ index.isLt
        have read := Data.List.Append.getElem_append_right
          head.compared.entered.cache.parents
          (BoundaryParentLocation.occurrenceParents tail)
          (index.val - head.compared.entered.cache.parents.length) next.isLt shiftedBound
        exact ((getElem_congr rfl offset.symm index.isLt).trans read).trans found.parent_eq

variable {program : PeriodPrograms.ExteriorProgram lifted differential}
  {prepared :
  ExteriorProgram.SurfacePreparation
  regular domains program}
  {requested : InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Select geometry from the actual root-closed program's parent index.
The request and surface preparation prove the entire positional readback. -/
def locateParent (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (i : Fin comparison.original.plans.length) :
      LocatedParent prepared.occurrences
      (comparison.Parent i) := by
  have equal : BoundaryParentLocation.occurrenceParents prepared.occurrences
    =
      comparison.original.plans.map (fun plan => plan.parent) :=
    prepared.parents_eq.trans comparison.original.parents_eq.symm
  have bound : i.val < (BoundaryParentLocation.occurrenceParents
    prepared.occurrences).length := by
    rw [equal, Data.List.Map.length_map]
    exact i.isLt
  have read := Integration.PreparedParentSplitSelection.mapped_read comparison.original.plans (fun plan => plan.parent)
    equal.symm i bound
  exact Eq.mp (congrArg (LocatedParent
    prepared.occurrences) read) (BoundaryParentLocation.locate
    prepared.occurrences ⟨i.val, bound⟩)

namespace LocatedParent
variable {occurrences : List
  (ExteriorProgram.SurfaceOccurrence
  regular domains differential)}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}

/-- The located parent belongs to its retained occurrence's original cache. -/
theorem parent_mem (located : LocatedParent
  occurrences parent) :
    parent ∈ located.occurrence.compared.entered.cache.parents :=
  Eq.mp (congrArg (fun value => value ∈ located.occurrence.compared.entered.cache.parents) located.parent_eq.symm)
    (List.getElem_mem located.index.isLt)

/-- An occurrence located in a retained component belongs to the containing surface's complete occurrence list. -/
theorem in_surface {component :
  ExteriorProgram.SurfaceComponent
  regular domains differential}
    (located : LocatedParent
      component.prepared.occurrences parent)
    (surface :
      ExteriorProgram.AllSurfacePreparation
      regular domains differential) (member : component ∈ surface.components) :
    located.occurrence ∈ surface.occurrences := open Purelib in by
  rw [surface.occurrences_eq]
  exact Data.List.Flatten.mem_flatMap.mpr ⟨component, member, located.member⟩

/-- Read the retained split at the selected local index; no splitting,
source preparation, or root-owner classification is repeated. -/
def selected (located : LocatedParent occurrences
  parent) :
    Integration.PreparedParentSplitSelection.Selected located.occurrence.compared.entered.mesh.splits parent :=
  Eq.mp (congrArg (Integration.PreparedParentSplitSelection.Selected located.occurrence.compared.entered.mesh.splits)
    located.parent_eq.symm)
    (Integration.PreparedParentSplitSelection.select located.occurrence.compared.entered.mesh.splits located.index)

end LocatedParent
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation
