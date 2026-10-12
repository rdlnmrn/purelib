module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval
import Purelib.Riemann.Integration.PreparedParentAxisLocation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Init.Data.Bool
import Init.Data.Fin.Basic
import Init.Data.List.Basic
import Init.Data.List.OfFn
import Init.Data.Nat.Basic
import Init.GetElem
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring

public section

/-! The retained occurrence's endpoint chain selects a crossing parent.
Embed its local position into the same closed-bank source order. -/
section

open Purelib.Data.List

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedParentAxisLocation
open Purelib.Riemann.Paths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation (occurrenceParents LocatedParent)
open Purelib.Riemann.Integration.PreparedParentSplitSelection (parentAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Riemann.Normalization
open
  SurfacePreparation.ClosedBoundaryComparison
open
  ExteriorProgram.SurfaceOccurrence
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

/-- Read the original surface occurrence at its retained bounded position. -/
@[expose] def occurrenceAt (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential))
    (index : Fin occurrences.length) := occurrences[index.val]'index.isLt

/-- Embed an original occurrence-local parent position into the complete flattened parent bank.

The recursive offsets preserve occurrence order and repeated parents without searching by payload equality. -/
@[expose] def embed : (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential)) →
    (outer : Fin occurrences.length) →
    Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt occurrences
      outer).compared.entered.cache.parents.length →
    Fin (BoundaryParentLocation.occurrenceParents occurrences).length
  | [], outer, _ => Fin.elim0 outer
  | head :: tail, ⟨0, _⟩, inner =>
      ⟨inner.val, by
        simpa only [BoundaryParentLocation.occurrenceParents,
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt, List.getElem_cons_zero,
          List.map_cons, List.flatten_cons, Append.length_append, -eq_self, -iff_self] using
          Nat.lt_add_right (BoundaryParentLocation.occurrenceParents tail).length inner.isLt⟩
  | head :: tail, ⟨outer + 1, bound⟩, inner =>
      let next := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed tail ⟨outer,
        Nat.lt_of_succ_lt_succ bound⟩ inner
      ⟨head.compared.entered.cache.parents.length + next.val,
        by
          simpa only [BoundaryParentLocation.occurrenceParents, List.map_cons, List.flatten_cons, Append.length_append,
            -eq_self, -iff_self] using
            Nat.add_lt_add_left next.isLt head.compared.entered.cache.parents.length⟩

/-- The embedded position equals the total parent count of earlier occurrences plus its original local position. -/
private theorem embed_val (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential))
    (outer : Fin occurrences.length)
    (inner : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt occurrences
      outer).compared.entered.cache.parents.length) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed occurrences outer inner).val =
      (BoundaryParentLocation.occurrenceParents (occurrences.take outer.val)).length + inner.val := by
  induction occurrences with
  | nil => exact Fin.elim0 outer
  | cons head tail ih =>
    rcases outer with ⟨outer, bound⟩
    cases outer with
    | zero => exact (Nat.zero_add inner.val).symm
    | succ outer =>
      change head.compared.entered.cache.parents.length +
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed tail ⟨outer,
        Nat.lt_of_succ_lt_succ bound⟩ inner).val = _
      rw [ih ⟨outer, Nat.lt_of_succ_lt_succ bound⟩ inner]
      simp only [List.take_succ_cons, BoundaryParentLocation.occurrenceParents, List.map_cons, List.flatten_cons,
        Append.length_append,
        Nat.add_assoc, -eq_self, -iff_self]
      rfl

/-- Reading the flattened bank at the embedded position returns the identical original occurrence parent. -/
private theorem embed_read : ∀ (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential))
    (outer : Fin occurrences.length)
    (inner : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt occurrences
      outer).compared.entered.cache.parents.length),
    PreparedParentSplitSelection.parentAt (BoundaryParentLocation.occurrenceParents occurrences)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed occurrences outer inner) =
      PreparedParentSplitSelection.parentAt
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt occurrences
        outer).compared.entered.cache.parents inner
  | [], outer, _ => Fin.elim0 outer
  | head :: tail, ⟨0, _⟩, inner =>
      Append.getElem_append_left _ _ inner.val inner.isLt _
  | head :: tail, ⟨outer + 1, bound⟩, inner => by
      let next := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed tail ⟨outer,
        Nat.lt_of_succ_lt_succ bound⟩ inner
      change (head.compared.entered.cache.parents ++ BoundaryParentLocation.occurrenceParents
        tail)[head.compared.entered.cache.parents.length + next.val]'(by
        rw [Append.length_append]
        exact Nat.add_lt_add_left next.isLt head.compared.entered.cache.parents.length) = _
      exact (Append.getElem_append_right head.compared.entered.cache.parents
        (BoundaryParentLocation.occurrenceParents tail) next.val next.isLt _).trans
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed_read tail ⟨outer,
          Nat.lt_of_succ_lt_succ bound⟩ inner)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

variable {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
  differential} {prepared :
  ExteriorProgram.SurfacePreparation
  regular domains program}
  {requested : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

/-- The flattened retained occurrence parents and the original closed comparison plans have the same length. -/
theorem parent_length (comparison : prepared.ClosedBoundaryComparison other requested minimum) :
    (BoundaryParentLocation.occurrenceParents prepared.occurrences).length = comparison.original.plans.length := by
  rw [show BoundaryParentLocation.occurrenceParents prepared.occurrences = comparison.original.plans.map (fun plan =>
    plan.parent) from
    prepared.parents_eq.trans comparison.original.parents_eq.symm, Map.length_map]

/-- Transport the original occurrence-local parent position into the retained closed comparison plan index. -/
@[expose] def sourceIndex (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (inner : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).compared.entered.cache.parents.length) :
    Fin comparison.original.plans.length :=
  Fin.cast (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.parent_length comparison)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed prepared.occurrences outer inner)

/-- The transported closed-bank index reads the identical original occurrence parent. -/
theorem sourceIndex_read (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (inner : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).compared.entered.cache.parents.length) :
    comparison.Parent (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison
      outer inner) =
      PreparedParentSplitSelection.parentAt
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents inner := by
  have equal : comparison.original.plans.map (fun plan => plan.parent) = BoundaryParentLocation.occurrenceParents
    prepared.occurrences :=
    comparison.original.parents_eq.trans prepared.parents_eq.symm
  have read := PreparedParentSplitSelection.mapped_read comparison.original.plans (fun plan => plan.parent)
    equal (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer inner)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed prepared.occurrences outer
      inner).isLt
  exact read.symm.trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed_read
    prepared.occurrences outer inner)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

/-- The occurrence's original positions in the retained closed bank. -/
@[expose] def parentIndices (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) : List (Fin comparison.original.plans.length) :=
  List.ofFn (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer)

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

/-- Enumerating the offset finite positions gives the consecutive natural-number range. -/
private theorem ofFn_range (count offset : Nat) :
    List.ofFn (fun i : Fin count => offset + i.val) = List.range' offset count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ]
    apply congrArg (List.cons offset)
    exact (OfFn.Basic.ofFn_congr (fun i : Fin count =>
      (Nat.add_assoc offset i.val 1).symm.trans (Nat.add_right_comm offset i.val 1))).trans (ih (offset + 1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

/-- The retained closed-bank parent indices are the consecutive range occupied by the original occurrence. -/
theorem parentIndices_values (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) :
    (comparison.parentIndices outer).map Fin.val =
      List.range' (BoundaryParentLocation.occurrenceParents (prepared.occurrences.take outer.val)).length
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
          outer).compared.entered.cache.parents.length := by
  rw
    [parentIndices,
    OfFn.Basic.map_ofFn]
  exact (OfFn.Basic.ofFn_congr (fun i =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed_val prepared.occurrences outer
    i)).trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.ofFn_range _ _)

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

/-- The retained occurrence-parent embedding preserves local position order. -/
private theorem embed_mono (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential))
    (outer : Fin occurrences.length)
    (i j : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt occurrences
      outer).compared.entered.cache.parents.length)
    (ordered : i.val ≤ j.val) : (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed
      occurrences outer i).val ≤ (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed
      occurrences outer j).val := by
  induction occurrences with
  | nil => exact Fin.elim0 outer
  | cons head tail ih =>
    rcases outer with ⟨outer, bound⟩
    cases outer with
    | zero => exact ordered
    | succ outer => exact Nat.add_le_add_left (ih ⟨outer, Nat.lt_of_succ_lt_succ bound⟩ i j ordered) _

/-- Adjacent original local positions remain adjacent in the complete flattened bank. -/
private theorem embed_next (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential))
    (outer : Fin occurrences.length)
    (i j : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt occurrences
      outer).compared.entered.cache.parents.length)
    (next : j.val = i.val + 1) : (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed
      occurrences outer j).val = (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed
      occurrences outer i).val + 1 := by
  induction occurrences with
  | nil => exact Fin.elim0 outer
  | cons head tail ih =>
    rcases outer with ⟨outer, bound⟩
    cases outer with
    | zero => exact next
    | succ outer =>
      change head.compared.entered.cache.parents.length +
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed tail ⟨outer,
        Nat.lt_of_succ_lt_succ bound⟩ j).val =
        (head.compared.entered.cache.parents.length +
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed tail ⟨outer,
          Nat.lt_of_succ_lt_succ bound⟩ i).val) + 1
      rw [ih ⟨outer, Nat.lt_of_succ_lt_succ bound⟩ i j next, Nat.add_assoc]

/-- Transport to the original closed plan bank preserves local parent order. -/
private theorem sourceIndex_mono (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (i j : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).compared.entered.cache.parents.length)
    (ordered : i.val ≤ j.val) : (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex
      comparison outer i).val ≤ (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex
      comparison outer j).val :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed_mono prepared.occurrences outer i j
    ordered

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

set_option genInjectivity false in
/-- An original closed-bank parent whose projected interval contains the supplied query.

The retained index and occurrence assignment identify the actual parent; the lower endpoint is included and the upper
endpoint is excluded. -/
structure CrossingParent (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (project : InverseRootPolynomial.Gaussian → InverseRootPolynomial.Coordinate) (query :
      InverseRootPolynomial.Coordinate) where
  /-- The original parent's retained position in the closed plan bank. -/ index : Fin comparison.original.plans.length
  /-- The original occurrence and local position identifying this exact closed-bank parent. -/ assigned :
    BoundaryParentLocation.LocatedParent prepared.occurrences (comparison.Parent index)
  /-- The projected original parent start is at or below the query. -/ lower : project ((comparison.Parent
    index).edge.point 0) ≤ query
  /-- The query lies strictly below the projected original parent finish. -/ upper : query < project ((comparison.Parent
    index).edge.point 1)

constructive_injectivity CrossingParent

/-- Search only the retained occurrence cache. Its endpoint-chain theorem proves success, and the original list
equalities provide the closed-bank index. -/
@[expose] def locateOccurrenceAxis (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (project : InverseRootPolynomial.Gaussian →
      InverseRootPolynomial.Coordinate) (query : InverseRootPolynomial.Coordinate)
    (lower : project (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).start ≤ query)
    (upper : query < project (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).finish) :

      CrossingParent
      comparison project query := by
  let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    prepared.occurrences outer
  let found := ParentCache.locateAxis occurrence.compared.entered.cache project query lower upper
  let index := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer
    found.index
  have read := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_read comparison outer
    found.index
  let assigned : BoundaryParentLocation.LocatedParent prepared.occurrences (comparison.Parent index) :=
    ⟨occurrence, List.getElem_mem outer.isLt, found.index, read⟩
  refine ⟨index, assigned, ?_, ?_⟩
  · exact (congrArg (fun parent => project (parent.edge.point 0)) read).trans_le found.lower
  · exact found.upper.trans_eq (congrArg (fun parent => project (parent.edge.point 1)) read).symm

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis signedInterval
  blockMidpoint)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

/-- Each retained member of a proper parent chain has strictly increasing parameter endpoints. -/
private theorem proper_member {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} (member : parent ∈ parents) :
    parent.parameterEdge.left.parameter < parent.parameterEdge.right.parameter := by
  induction parents with
  | nil => cases member
  | cons head tail ih =>
    rcases Membership.mem_cons.mp member with rfl | member
    · exact proper.1
    · exact ih proper.2 member

/-- The signed selected coordinate of an affine segment is affine in its original parameter. -/
private theorem signed_affine (vertical forward : Bool) (first last : InverseRootPolynomial.Gaussian) (parameter :
  InverseRootPolynomial.Coordinate) :
    SourceBlockParameters.signedAxis vertical forward (PreparedSegmentCuts.point first last parameter) =
      SourceBlockParameters.signedAxis vertical forward first + parameter * (SourceBlockParameters.signedAxis vertical
        forward last - SourceBlockParameters.signedAxis vertical forward first) := by
  cases vertical <;> cases forward <;>
    dsimp [SourceBlockParameters.signedAxis, SourceIntervals.axisCoordinate, PreparedSegmentCuts.point] <;> ring1

/-- Strict parent order follows from the retained occurrence geometry alone. -/
theorem source_parent_ordered (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    (member : parent ∈ occurrence.compared.entered.cache.parents) :
    SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward (parent.edge.point 0) <
      SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward (parent.edge.point 1) := by
  have endpoints := PreparedSegmentBoundaryGeometry.segment_parent_endpoints occurrence.compared.entered.cache member
  have proper := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.proper_member
    occurrence.compared.entered.cache.proper member
  have direction := occurrence.source_span_endpoints.1.trans_lt
    (occurrence.sourceSpan.ordered.trans_eq occurrence.source_span_endpoints.2.symm)
  have affine (parameter : InverseRootPolynomial.Coordinate) :
      SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward (occurrence.segment.pointAt
        parameter) =
        SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward occurrence.start + parameter
          *
          (SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward occurrence.finish -
            SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward occurrence.start) :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.signed_affine _ _ _ _ _
  rw [endpoints.1, endpoints.2, affine, affine]
  exact Fraction.Order.Arithmetic.add_lt_add_left_direct
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct proper (Fraction.Order.Arithmetic.sub_pos_direct
      direction)) _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

/-- Source-order monotonicity uses the actual occurrence's parent cache and its positional embedding into the closed
bank, preserving repeated parents. -/
theorem locateOccurrenceAxis_mono (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) {a b : InverseRootPolynomial.Coordinate} (increasing : a ≤ b)
    (aLower : SourceBlockParameters.signedAxis
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).start ≤ a)
    (aUpper : a < SourceBlockParameters.signedAxis
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).finish)
    (bLower : SourceBlockParameters.signedAxis
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).start ≤ b)
    (bUpper : b < SourceBlockParameters.signedAxis
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).finish) :
    let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer
    let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
    (comparison.locateOccurrenceAxis outer project a aLower aUpper).index.val ≤
      (comparison.locateOccurrenceAxis outer project b bLower bUpper).index.val := by
  let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    prepared.occurrences outer
  let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_mono comparison outer _ _
    (ParentCache.locateAxis_mono occurrence.compared.entered.cache project
      (fun _ member => (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.source_parent_ordered
        occurrence member).le) increasing aLower aUpper bLower bUpper)

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

/-- The original occurrence endpoints bound both endpoints of every indexed retained parent. -/
private theorem sourceIndex_bounds (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (i : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer
    let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
    project occurrence.start ≤ project ((comparison.Parent
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer
      i)).edge.point 0) ∧
      project ((comparison.Parent (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex
        comparison outer i)).edge.point 1) ≤ project occurrence.finish := by
  let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    prepared.occurrences outer
  let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
  have bounds := ParentCache.parent_bounds occurrence.compared.entered.cache project
    (fun _ member => (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.source_parent_ordered
      occurrence member).le) i
  have firstEq := congrArg (fun parent : PreparedSubdivisionModelCore.CenteredEdge curve differential =>
    project (parent.edge.point 0))
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_read comparison outer i)
  have lastEq := congrArg (fun parent : PreparedSubdivisionModelCore.CenteredEdge curve differential =>
    project (parent.edge.point 1))
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_read comparison outer i)
  exact ⟨bounds.1.trans_eq firstEq.symm, lastEq.trans_le bounds.2⟩

/-- Ordered distinct retained parent positions have separated projected intervals. -/
private theorem sourceIndex_separated (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (i j : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).compared.entered.cache.parents.length)
    (before : (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer
      i).val < (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer
      j).val) :
    let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer
    let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
    project ((comparison.Parent (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex
      comparison outer i)).edge.point 1) ≤
      project ((comparison.Parent (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex
        comparison outer j)).edge.point 0) := by
  let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    prepared.occurrences outer
  let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
  have localOrder : i.val < j.val := Nat.lt_of_not_ge (fun reverse =>
    (Nat.not_lt_of_ge (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_mono
      comparison outer j i reverse)) before)
  have separated := ParentCache.parents_separated occurrence.compared.entered.cache project
    (fun _ member => (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.source_parent_ordered
      occurrence member).le) i j localOrder
  have firstEq := congrArg (fun parent : PreparedSubdivisionModelCore.CenteredEdge curve differential =>
    project (parent.edge.point 1))
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_read comparison outer i)
  have lastEq := congrArg (fun parent : PreparedSubdivisionModelCore.CenteredEdge curve differential =>
    project (parent.edge.point 0))
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_read comparison outer j)
  exact firstEq.trans_le (separated.trans_eq lastEq.symm)

/-- Ordered retained parents with a common projected endpoint occupy adjacent original positions. -/
private theorem sourceIndex_no_skip (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (i j : Fin (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).compared.entered.cache.parents.length)
    (before : (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer
      i).val < (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer
      j).val)
    (joint : SourceBlockParameters.signedAxis
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward
        ((comparison.Parent (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex
          comparison outer i)).edge.point 1) =
      SourceBlockParameters.signedAxis
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
        prepared.occurrences outer).sourceForward
        ((comparison.Parent (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex
          comparison outer j)).edge.point 0)) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer j).val =
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex comparison outer i).val + 1
      := by
  let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    prepared.occurrences outer
  let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
  have localOrder : i.val < j.val := Nat.lt_of_not_ge (fun reverse =>
    (Nat.not_lt_of_ge (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_mono
      comparison outer j i reverse)) before)
  have firstEq := congrArg (fun parent : PreparedSubdivisionModelCore.CenteredEdge curve differential =>
    project (parent.edge.point 1))
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_read comparison outer i)
  have lastEq := congrArg (fun parent : PreparedSubdivisionModelCore.CenteredEdge curve differential =>
    project (parent.edge.point 0))
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_read comparison outer j)
  have next := ParentCache.parents_no_skip occurrence.compared.entered.cache project
    (fun _ member => Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.source_parent_ordered
      occurrence member) i j localOrder (firstEq.symm.trans (joint.trans lastEq))
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed_next prepared.occurrences outer i
    j next

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

/-- Every interval of the actual occurrence's face mesh selects a source parent. The side geometry supplies orientation
and both search bounds. -/
@[expose] def locateSideInterval (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (meshes : RegularDomainMeshes.RegularMeshes domains
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.sheet)
    (physical : PreparedAxisPartitions.Interval)
    (present : physical ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical) :

      CrossingParent
      comparison
      (SourceBlockParameters.signedAxis
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
        prepared.occurrences outer).sourceForward)
      (SourceBlockParameters.blockMidpoint
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceForward physical) := by
  let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    prepared.occurrences outer
  let mesh := meshes.entries.get occurrence.sideOccurrence.position
  change physical ∈ SourceIntervals.axisIntervals mesh occurrence.sourceVertical at present
  have bounds : occurrence.sourceSpan.lower ≤ (SourceBlockParameters.signedInterval occurrence.sourceForward
    physical).lower ∧
      (SourceBlockParameters.signedInterval occurrence.sourceForward physical).upper ≤ occurrence.sourceSpan.upper := by
    cases vertical : occurrence.sourceVertical with
    | false =>
      have presentX : physical ∈ mesh.partition.x.intervals := by
        simpa only [SourceIntervals.axisIntervals, vertical, if_neg (show (false : Bool) ≠ true from Bool.noConfusion),
          if_pos (show (true : Bool) = true from rfl), -eq_self, -iff_self] using present
      have bound := mesh.partition.x.interval_bounds presentX
      cases forward : occurrence.sourceForward with
      | true =>
        simpa only [SurfaceOccurrence.sourceSpan, vertical, forward, SourceBlockParameters.signedInterval,
          if_neg (show (false : Bool) ≠ true from Bool.noConfusion), if_pos (show (true : Bool) = true from rfl),
          -eq_self, -iff_self] using bound
      | false =>
        have reversed := And.intro (Fraction.Order.Arithmetic.neg_le_neg_direct bound.2)
          (Fraction.Order.Arithmetic.neg_le_neg_direct bound.1)
        simpa only [SurfaceOccurrence.sourceSpan, vertical, forward, SourceBlockParameters.signedInterval, if_neg (show
          (false : Bool) ≠ true from Bool.noConfusion), if_pos (show (true : Bool) = true from rfl), -eq_self,
          -iff_self] using reversed
    | true =>
      have presentY : physical ∈ mesh.partition.y.intervals := by
        simpa only [SourceIntervals.axisIntervals, vertical, if_neg (show (false : Bool) ≠ true from Bool.noConfusion),
          if_pos (show (true : Bool) = true from rfl), -eq_self, -iff_self] using present
      have bound := mesh.partition.y.interval_bounds presentY
      cases forward : occurrence.sourceForward with
      | true =>
        simpa only [SurfaceOccurrence.sourceSpan, vertical, forward, SourceBlockParameters.signedInterval,
          if_neg (show (false : Bool) ≠ true from Bool.noConfusion), if_pos (show (true : Bool) = true from rfl),
          -eq_self, -iff_self] using bound
      | false =>
        have reversed := And.intro (Fraction.Order.Arithmetic.neg_le_neg_direct bound.2)
          (Fraction.Order.Arithmetic.neg_le_neg_direct bound.1)
        simpa only [SurfaceOccurrence.sourceSpan, vertical, forward, SourceBlockParameters.signedInterval, if_neg (show
          (false : Bool) ≠ true from Bool.noConfusion), if_pos (show (true : Bool) = true from rfl), -eq_self,
          -iff_self] using reversed
  have midpoint := PreparedSegmentCuts.midpoint_bounds (SourceBlockParameters.signedInterval occurrence.sourceForward
    physical)
  exact comparison.locateOccurrenceAxis outer (SourceBlockParameters.signedAxis occurrence.sourceVertical
    occurrence.sourceForward)
    (SourceBlockParameters.blockMidpoint occurrence.sourceForward physical)
    (occurrence.source_span_endpoints.1.trans_le (bounds.1.trans midpoint.1.le))
    ((midpoint.2.trans_le bounds.2).trans_eq occurrence.source_span_endpoints.2.symm)

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

/-- Increasing signed interval midpoints select nondecreasing original closed-bank parent positions. -/
private theorem locateSideInterval_mono (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (meshes : RegularDomainMeshes.RegularMeshes domains
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.sheet)
    (first last : PreparedAxisPartitions.Interval)
    (firstPresent : first ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (lastPresent : last ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (ordered : SourceBlockParameters.blockMidpoint
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceForward first ≤
      SourceBlockParameters.blockMidpoint
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceForward last) :
    (comparison.locateSideInterval outer meshes first firstPresent).index.val ≤
      (comparison.locateSideInterval outer meshes last lastPresent).index.val := by
  exact comparison.locateOccurrenceAxis_mono outer ordered _ _ _ _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

/-- The parent selected for an actual side interval remains within the original occurrence span. -/
theorem locateSideInterval_bounds (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (meshes : RegularDomainMeshes.RegularMeshes domains
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.sheet)
    (physical : PreparedAxisPartitions.Interval)
    (present : physical ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical) :
    let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer
    let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
    let parent := comparison.Parent (comparison.locateSideInterval outer meshes physical present).index
    project occurrence.start ≤ project (parent.edge.point 0) ∧ project (parent.edge.point 1) ≤ project occurrence.finish
      := by
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_bounds comparison outer _

/-- Starting at the occurrence start rules out an omitted parent prefix. -/
theorem locateSideInterval_at_start (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (meshes : RegularDomainMeshes.RegularMeshes domains
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.sheet)
    (physical : PreparedAxisPartitions.Interval)
    (present : physical ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (endpoint : SourceBlockParameters.signedAxis
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward
      ((comparison.Parent (comparison.locateSideInterval outer meshes physical present).index).edge.point 0) =
      SourceBlockParameters.signedAxis
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
        prepared.occurrences outer).sourceForward
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
          outer).start) :
    (comparison.locateSideInterval outer meshes physical present).index.val =
      (BoundaryParentLocation.occurrenceParents (prepared.occurrences.take outer.val)).length := by
  let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    prepared.occurrences outer
  let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
  have position := ParentCache.parent_at_start occurrence.compared.entered.cache project
    (fun _ member => Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.source_parent_ordered
      occurrence member) _
    ((congrArg (fun parent : PreparedSubdivisionModelCore.CenteredEdge curve differential =>
      project (parent.edge.point 0))
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_read comparison outer
        _)).symm.trans endpoint)
  exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed_val prepared.occurrences outer
    _).trans (by rw [position, Nat.add_zero])

/-- Ending at the occurrence finish rules out an omitted parent suffix. -/
theorem locateSideInterval_at_finish (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (meshes : RegularDomainMeshes.RegularMeshes domains
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.sheet)
    (physical : PreparedAxisPartitions.Interval)
    (present : physical ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (endpoint : SourceBlockParameters.signedAxis
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward
      ((comparison.Parent (comparison.locateSideInterval outer meshes physical present).index).edge.point 1) =
      SourceBlockParameters.signedAxis
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
        prepared.occurrences outer).sourceForward
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
          outer).finish) :
    (comparison.locateSideInterval outer meshes physical present).index.val + 1 =
      (BoundaryParentLocation.occurrenceParents (prepared.occurrences.take outer.val)).length +
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
          outer).compared.entered.cache.parents.length := by
  let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    prepared.occurrences outer
  let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
  have position := ParentCache.parent_at_finish occurrence.compared.entered.cache project
    (fun _ member => Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.source_parent_ordered
      occurrence member) _
    ((congrArg (fun parent : PreparedSubdivisionModelCore.CenteredEdge curve differential =>
      project (parent.edge.point 1))
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_read comparison outer
        _)).symm.trans endpoint)
  exact (congrArg (fun n : Nat => n + 1)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.embed_val prepared.occurrences outer
    _)).trans
    ((Nat.add_assoc _ _ _).trans (congrArg (fun n : Nat => _ + n) position))

/-- Ordered distinct selections retain the geometric separation of their parents. The comparison uses positions, not
equality of parent payloads. -/
theorem locateSideInterval_separated (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (meshes : RegularDomainMeshes.RegularMeshes domains
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.sheet)
    (first last : PreparedAxisPartitions.Interval)
    (firstPresent : first ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (lastPresent : last ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (ordered : (comparison.locateSideInterval outer meshes first firstPresent).index.val <
      (comparison.locateSideInterval outer meshes last lastPresent).index.val) :
    let occurrence := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer
    let project := SourceBlockParameters.signedAxis occurrence.sourceVertical occurrence.sourceForward
    project ((comparison.Parent (comparison.locateSideInterval outer meshes first firstPresent).index).edge.point 1) ≤
      project ((comparison.Parent (comparison.locateSideInterval outer meshes last lastPresent).index).edge.point 0) :=
        by
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_separated comparison outer _
    _ ordered

/-- Distinct ordered side selections meeting at a parent endpoint have consecutive original closed-bank positions. -/
theorem locateSideInterval_no_skip (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (meshes : RegularDomainMeshes.RegularMeshes domains
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.sheet)
    (first last : PreparedAxisPartitions.Interval)
    (firstPresent : first ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (lastPresent : last ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (ordered : (comparison.locateSideInterval outer meshes first firstPresent).index.val <
      (comparison.locateSideInterval outer meshes last lastPresent).index.val)
    (joint : SourceBlockParameters.signedAxis
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward
        ((comparison.Parent (comparison.locateSideInterval outer meshes first firstPresent).index).edge.point 1) =
      SourceBlockParameters.signedAxis
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
        prepared.occurrences outer).sourceForward
        ((comparison.Parent (comparison.locateSideInterval outer meshes last lastPresent).index).edge.point 0)) :
    (comparison.locateSideInterval outer meshes last lastPresent).index.val =
      (comparison.locateSideInterval outer meshes first firstPresent).index.val + 1 := by
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.sourceIndex_no_skip comparison outer _ _
    ordered joint

/-- Physical interval order agrees with the closed parent order on forward sides and reverses it on backward sides. No
parent-order certificate is supplied. -/
theorem locateSideInterval_order (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length)
    (meshes : RegularDomainMeshes.RegularMeshes domains
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.sheet)
    (first last : PreparedAxisPartitions.Interval)
    (firstPresent : first ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (lastPresent : last ∈ SourceIntervals.axisIntervals (meshes.entries.get
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
        outer).sourceVertical)
    (ordered : first.upper ≤ last.lower) :
    if (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).sourceForward then
      (comparison.locateSideInterval outer meshes first firstPresent).index.val ≤
        (comparison.locateSideInterval outer meshes last lastPresent).index.val
    else
      (comparison.locateSideInterval outer meshes last lastPresent).index.val ≤
        (comparison.locateSideInterval outer meshes first firstPresent).index.val := by
  let forward := (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    prepared.occurrences outer).sourceForward
  have firstBounds := PreparedSegmentCuts.midpoint_bounds (SourceBlockParameters.signedInterval forward first)
  have lastBounds := PreparedSegmentCuts.midpoint_bounds (SourceBlockParameters.signedInterval forward last)
  cases direction : forward with
  | true =>
    have between : (SourceBlockParameters.signedInterval forward first).upper ≤ (SourceBlockParameters.signedInterval
      forward last).lower := by
      simpa only [direction, SourceBlockParameters.signedInterval, if_neg (show (false : Bool) ≠ true from
        Bool.noConfusion), if_pos (show (true : Bool) = true from rfl), -eq_self, -iff_self] using ordered
    have indices := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.locateSideInterval_mono
      comparison outer meshes first last firstPresent lastPresent
      (firstBounds.2.le.trans (between.trans lastBounds.1.le))
    simpa only [show (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward = true from direction, if_neg (show (false : Bool) ≠ true from
      Bool.noConfusion), if_pos (show (true : Bool) = true from rfl), -eq_self, -iff_self] using indices
  | false =>
    have between : (SourceBlockParameters.signedInterval forward last).upper ≤ (SourceBlockParameters.signedInterval
      forward first).lower := by
      simpa only [direction, SourceBlockParameters.signedInterval, if_neg (show (false : Bool) ≠ true from
        Bool.noConfusion), if_pos (show (true : Bool) = true from rfl), -eq_self, -iff_self] using
        Fraction.Order.Arithmetic.neg_le_neg_direct ordered
    have indices := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.locateSideInterval_mono
      comparison outer meshes last first lastPresent firstPresent
      (lastBounds.2.le.trans (between.trans firstBounds.1.le))
    simpa only [show (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      prepared.occurrences outer).sourceForward = false from direction, if_neg (show (false : Bool) ≠ true from
      Bool.noConfusion), if_pos (show (true : Bool) = true from rfl), -eq_self, -iff_self] using indices

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

end
