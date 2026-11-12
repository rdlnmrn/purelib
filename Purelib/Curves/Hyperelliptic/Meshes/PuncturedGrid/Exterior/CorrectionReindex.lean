module
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSelection

open Purelib.Riemann.Meshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh

public section

/-! Reindex the actual exterior occurrence sum onto the original face,
sheet and side classification, without replacing any primitive bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceOccurrence)
open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Normalization

attribute [local congr] FiniteSum.Fin.sumFin_congr
variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- Every original located regular side is a positively oriented source of its retained triangle. -/
private theorem CorrectionReindex.source_positive (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side :
  GridLiftedDualSteps.GridSide) :
    Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive
      (LocatedFace.sideSource
      (lifted.mesh.locateFace position sheet) side) lifted.mesh.triangulation.faces := by
  unfold LocatedFace.sideSource
    Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive
    Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.project
  rw [lifted.mesh.triangleIndex_face]
  cases side <;> first
    | exact List.mem_cons_self
    | exact List.mem_cons_of_mem _ List.mem_cons_self
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- Equal retained side sources identify the same regular position, sheet and rectangle side. -/
private theorem CorrectionReindex.source_injective
    (p q : Fin base.faces.regulars.length) (s t : Fin 2) (side next : GridLiftedDualSteps.GridSide)
    (equal :
      (LocatedFace.sideSource
      (lifted.mesh.locateFace p s) side) =
      (LocatedFace.sideSource
      (lifted.mesh.locateFace q t) next)) :
    p = q ∧ s = t ∧ side = next := by
  have indices := congrArg (fun source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge
    lifted.mesh.triangles.length => source.source.val) equal
  have first := congrArg (fun source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge
    lifted.mesh.triangles.length => source.first.val) equal
  have last := congrArg (fun source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge
    lifted.mesh.triangles.length => source.last.val) equal
  have sb := s.isLt
  have tb := t.isLt
  cases side <;> cases next <;>
    dsimp only [LocatedFace.sideSource,
      GridLiftedMesh.LiftedMesh.triangleIndex, GridLiftedDualSteps.GridSide.kind,
      Topology.Mesh.QuadrilateralDual.QuadOccurrence.upperSide,
        Face.Corners.FaceCorners.firstCorner,
        Face.Corners.FaceCorners.lastCorner,
        -eq_self, -iff_self] at indices first last
  all_goals first
    | change (0 : Nat) = 0 at first
    | change (0 : Nat) = 1 at first
    | change (0 : Nat) = 2 at first
    | change (1 : Nat) = 0 at first
    | change (1 : Nat) = 1 at first
    | change (1 : Nat) = 2 at first
    | change (2 : Nat) = 0 at first
    | change (2 : Nat) = 1 at first
    | change (2 : Nat) = 2 at first
  all_goals first
    | change (0 : Nat) = 0 at last
    | change (0 : Nat) = 1 at last
    | change (0 : Nat) = 2 at last
    | change (1 : Nat) = 0 at last
    | change (1 : Nat) = 1 at last
    | change (1 : Nat) = 2 at last
    | change (2 : Nat) = 0 at last
    | change (2 : Nat) = 1 at last
    | change (2 : Nat) = 2 at last
  all_goals try rewrite [if_pos (rfl : true = true)] at indices
  all_goals try rewrite [if_neg Bool.false_ne_true] at indices
  all_goals first
    | exact ⟨Fin.ext (by omega), Fin.ext (by omega), rfl⟩
    | exact False.elim (by omega)

/-- Every original exterior cap occurrence has forward side-source orientation. -/
private theorem CorrectionReindex.occurrence_forward (prepared :
  AllSurfacePreparation
  regular domains differential)
    (occurrence :
      SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences) :
    occurrence.sideOccurrence.backward = false := by
  have projected := (congrArg (fun source => source.project lifted.mesh.triangulation.faces)
    occurrence.side_source).trans
    occurrence.placement.location.sourceEdge_project
  have indexed : occurrence.placement.indexed ∈ lifted.exteriorBoundaries.flatten :=
    prepared.indexed_eq ▸ List.Map.mem_map_of_mem member
  have actual : occurrence.sideOccurrence.source.project lifted.mesh.triangulation.faces ∈ lifted.boundaryLoops.flatten
    := by
    rw [projected, LiftedPuncturedGrid.boundaryLoops, List.Flatten.flatten_append]
    exact Data.List.Membership.mem_append.mpr (Or.inl indexed)
  have canonical := lifted.exterior_side_member occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
    occurrence.sideOccurrence.side (prepared.occurrence_exterior occurrence member)
  have physical : ((LocatedFace.sideSource
    (lifted.mesh.locateFace occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet)
    occurrence.sideOccurrence.side)).project lifted.mesh.triangulation.faces ∈ lifted.boundaryLoops.flatten := by
    rw [LiftedPuncturedGrid.boundaryLoops, List.Flatten.flatten_append]
    exact Data.List.Membership.mem_append.mpr (Or.inl canonical)
  have noReverse := ((lifted.boundaryLoops_edge_iff _).mp physical).2
  cases backward : occurrence.sideOccurrence.backward with
  | false => rfl
  | true =>
    have reverse : occurrence.sideOccurrence.source.project lifted.mesh.triangulation.faces =
        (((LocatedFace.sideSource
          (lifted.mesh.locateFace occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet)
          occurrence.sideOccurrence.side)).project lifted.mesh.triangulation.faces).reverse := by
      simp only [SegmentSideSources.LiftedMesh.SideOccurrence.source, backward,
        if_pos (rfl : true = true), -eq_self, -iff_self]
      rfl
    exact (noReverse (reverse ▸ Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member
      (BranchHoleSourceComparison.physicalSource_positive lifted _ actual))).elim

/-- The original exterior occurrence edge is the projection of its same positioned and sheeted regular-cell side. -/
private theorem CorrectionReindex.occurrence_edge (prepared :
  AllSurfacePreparation
  regular domains differential)
    (occurrence :
      SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences) :
    occurrence.placement.indexed =
      ((LocatedFace.sideSource
        (lifted.mesh.locateFace occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet)
        occurrence.sideOccurrence.side)).project lifted.mesh.triangulation.faces := by
  have projected := (congrArg (fun source => source.project lifted.mesh.triangulation.faces)
    occurrence.side_source).trans
    occurrence.placement.location.sourceEdge_project
  have equal : occurrence.sideOccurrence.source =
      (LocatedFace.sideSource
        (lifted.mesh.locateFace occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet)
        occurrence.sideOccurrence.side) := by
    simp only [SegmentSideSources.LiftedMesh.SideOccurrence.source,
      CorrectionReindex.occurrence_forward prepared occurrence member,
      if_neg (by decide : false ≠ true), -eq_self, -iff_self]
    rfl
  exact projected.symm.trans (congrArg (fun source => source.project lifted.mesh.triangulation.faces) equal)

/-- Sum Gaussian values over bottom, right, top and left in that retained order. -/
private def CorrectionReindex.sideSum (values : GridLiftedDualSteps.GridSide → Gaussian.Basic.Canonical) :
  Gaussian :=
  values .bottom + values .right + values .top + values .left

/-- Sum the four original side values over every regular position and both sheets. -/
private def CorrectionReindex.gridSum (values : Fin base.faces.regulars.length → Fin 2 →
  GridLiftedDualSteps.GridSide →
  Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (fun sheet =>
    CorrectionReindex.sideSum (values p sheet)))

/-- Pointwise equal retained side values have equal complete grid sums. -/
private theorem CorrectionReindex.grid_congr (first last : Fin base.faces.regulars.length → Fin 2 →
  GridLiftedDualSteps.GridSide →
  Gaussian.Basic.Canonical)
    (equal : ∀ p sheet side, first p sheet side = last p sheet side) :
      CorrectionReindex.gridSum first =
      CorrectionReindex.gridSum last := by
  apply FiniteSum.Fin.sumFin_congr
  intro p
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (equal p sheet .bottom) (equal p sheet .right)) (equal p sheet .top)) (equal p sheet .left)

/-- Interchange the finite auxiliary-index sum with the original face, sheet and side sum. -/
private theorem CorrectionReindex.grid_swap {count : Nat}
    (values : Fin base.faces.regulars.length → Fin 2 → GridLiftedDualSteps.GridSide → Fin count →
      Gaussian.Basic.Canonical) :
    CorrectionReindex.gridSum (fun p sheet side => FiniteSum.Fin.sumFin
      (values p sheet side)) =
      FiniteSum.Fin.sumFin (fun i => CorrectionReindex.gridSum (fun p sheet
        side => values p sheet side i)) := by
  have sides (p : Fin base.faces.regulars.length) (sheet : Fin 2) :
      CorrectionReindex.sideSum (fun side => FiniteSum.Fin.sumFin (values p
        sheet side)) = FiniteSum.Fin.sumFin (fun i =>
        CorrectionReindex.sideSum (fun side => values p sheet side i)) := by
    simp only [CorrectionReindex.sideSum, FiniteSum.Fin.sumFin_add,
      -eq_self, -iff_self]
    rfl
  unfold CorrectionReindex.gridSum
  rw [FiniteSum.Fin.sumFin_congr (fun p => FiniteSum.Fin.sumFin_congr (sides p))]
  rw [FiniteSum.Fin.sumFin_congr (fun p => FiniteSum.Fin.sumFin_swap (fun sheet i =>
    CorrectionReindex.sideSum (fun side => values p sheet side i)))]
  exact FiniteSum.Fin.sumFin_swap _

/-- A grid sum supported at one original position, sheet and side returns exactly that value. -/
private theorem CorrectionReindex.grid_delta (p : Fin base.faces.regulars.length) (sheet : Fin 2) (side :
  GridLiftedDualSteps.GridSide)
    (values : Fin base.faces.regulars.length → Fin 2 → GridLiftedDualSteps.GridSide → Gaussian.Basic.Canonical) :
    CorrectionReindex.gridSum (fun q t next => if q = p ∧ t = sheet ∧ next =
      side then values q t next else 0) = values p sheet side := by
  have sides (q : Fin base.faces.regulars.length) (t : Fin 2) :
      CorrectionReindex.sideSum (fun next => if q = p ∧ t = sheet ∧ next =
        side then values q t next else 0) =
        if q = p then (if t = sheet then values q t side else 0) else 0 := by
    by_cases qp : q = p
    · by_cases ts : t = sheet
      · dsimp only [CorrectionReindex.sideSum]
        rewrite [if_pos qp, if_pos ts]
        cases side with
        | bottom =>
          rewrite [if_pos ⟨qp, ts, rfl⟩, if_neg (by intro same; cases same.2.2), if_neg (by intro same; cases same.2.2),
            if_neg (by intro same; cases same.2.2)]
          simp only [Gaussian.Basic.add_zero, -eq_self, -iff_self]
          rfl
        | right =>
          rewrite [if_neg (by intro same; cases same.2.2), if_pos ⟨qp, ts, rfl⟩, if_neg (by intro same; cases same.2.2),
            if_neg (by intro same; cases same.2.2)]
          simp only [Gaussian.Basic.add_zero, Gaussian.Basic.zero_add, -eq_self, -iff_self]
          rfl
        | top =>
          rewrite [if_neg (by intro same; cases same.2.2), if_neg (by intro same; cases same.2.2), if_pos ⟨qp, ts, rfl⟩,
            if_neg (by intro same; cases same.2.2)]
          simp only [Gaussian.Basic.add_zero, Gaussian.Basic.zero_add, -eq_self, -iff_self]
          rfl
        | left =>
          rewrite [if_neg (by intro same; cases same.2.2), if_neg (by intro same; cases same.2.2), if_neg (by
            intro same; cases same.2.2), if_pos ⟨qp, ts, rfl⟩]
          simp only [Gaussian.Basic.add_zero, Gaussian.Basic.zero_add, -eq_self, -iff_self]
          rfl
      · have empty (next : GridLiftedDualSteps.GridSide) :
            (if q = p ∧ t = sheet ∧ next = side then values q t next else 0) = 0 :=
          if_neg (fun same => ts same.2.1)
        dsimp only [CorrectionReindex.sideSum]
        rewrite [empty .bottom, empty .right, empty .top, empty .left, if_pos qp, if_neg ts]
        simp only [Gaussian.Basic.zero_add, -eq_self, -iff_self]
        rfl
    · have empty (next : GridLiftedDualSteps.GridSide) :
          (if q = p ∧ t = sheet ∧ next = side then values q t next else 0) = 0 :=
        if_neg (fun same => qp same.1)
      dsimp only [CorrectionReindex.sideSum]
      rewrite [empty .bottom, empty .right, empty .top, empty .left, if_neg qp]
      simp only [Gaussian.Basic.zero_add, -eq_self, -iff_self]
      rfl
  unfold CorrectionReindex.gridSum
  rw [FiniteSum.Fin.sumFin_congr (fun q => FiniteSum.Fin.sumFin_congr (sides q))]
  have rows (q : Fin base.faces.regulars.length) :
      FiniteSum.Fin.sumFin (fun t => if q = p then (if t = sheet then values q t side else 0) else 0) =
        if q = p then values q sheet side else 0 := by
    by_cases same : q = p
    · calc
        _ = FiniteSum.Fin.sumFin (fun t => if t = sheet then values q t side else 0) :=
          FiniteSum.Fin.sumFin_congr (fun t => if_pos same)
        _ = values q sheet side := FiniteSum.Fin.sumFin_ite_eq sheet _
        _ = _ := (if_pos same).symm
    · calc
        _ = FiniteSum.Fin.sumFin (fun _ : Fin 2 => (0 : Gaussian.Basic.Canonical)) :=
          FiniteSum.Fin.sumFin_congr (fun t => if_neg same)
        _ = 0 := FiniteSum.Fin.sumFin_zero
        _ = _ := (if_neg same).symm
  exact (FiniteSum.Fin.sumFin_congr rows).trans (FiniteSum.Fin.sumFin_ite_eq p _)

/-- Read a retained side value only when its original neighbor classification selects the exterior component. -/
private def CorrectionReindex.selectedValue (neighbors : PuncturedGridFaces.PuncturedFaces.NeighborBank
  base.faces)
    (values : Fin base.faces.regulars.length → Fin 2 → GridLiftedDualSteps.GridSide → Gaussian.Basic.Canonical)
    (p : Fin base.faces.regulars.length) (sheet : Fin 2) (side : GridLiftedDualSteps.GridSide) : Gaussian :=
  (PhysicalComponentValues.SideNeighbor.componentValue
    (FaceNeighbors.at
    (neighbors.entries.get p) side)) .exterior (values p sheet side)

/-- Selection by one retained exterior occurrence returns exactly its original positioned and sheeted side value. -/
private theorem CorrectionReindex.selected_at_occurrence (prepared :
  AllSurfacePreparation
  regular domains differential)
    (neighbors : PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces)
    (values : Fin base.faces.regulars.length → Fin 2 → GridLiftedDualSteps.GridSide → Gaussian.Basic.Canonical)
    (index : Fin prepared.occurrences.length) :
    CorrectionReindex.gridSum (fun p sheet side => if
      (prepared.occurrences[index.val]'index.isLt).placement.indexed =
      ((LocatedFace.sideSource
        (lifted.mesh.locateFace p sheet) side)).project lifted.mesh.triangulation.faces
      then CorrectionReindex.selectedValue neighbors values p sheet side
        else 0) =
    let occurrence := prepared.occurrences[index.val]'index.isLt
    values occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side := by
  let occurrence := prepared.occurrences[index.val]'index.isLt
  have member : occurrence ∈ prepared.occurrences := List.getElem_mem index.isLt
  have edgeEq := CorrectionReindex.occurrence_edge prepared occurrence
    member
  have terms (p : Fin base.faces.regulars.length) (sheet : Fin 2) (side : GridLiftedDualSteps.GridSide) :
      (if occurrence.placement.indexed =
        ((LocatedFace.sideSource
        (lifted.mesh.locateFace p sheet) side)).project lifted.mesh.triangulation.faces
        then CorrectionReindex.selectedValue neighbors values p sheet side
          else 0) =
      if p = occurrence.sideOccurrence.position ∧ sheet = occurrence.sideOccurrence.sheet ∧ side =
        occurrence.sideOccurrence.side
        then CorrectionReindex.selectedValue neighbors values p sheet side
          else 0 := by
    by_cases same : p = occurrence.sideOccurrence.position ∧ sheet = occurrence.sideOccurrence.sheet ∧ side =
      occurrence.sideOccurrence.side
    · rcases same with ⟨rfl, rfl, rfl⟩
      rw [if_pos edgeEq, if_pos ⟨rfl, rfl, rfl⟩]
    · have different : occurrence.placement.indexed ≠
          ((LocatedFace.sideSource
            (lifted.mesh.locateFace p sheet) side)).project lifted.mesh.triangulation.faces := by
        intro equal
        have sources := TriangleSourceUniqueness.LiftedMesh.source_eq_of_project_eq
          lifted.mesh (CorrectionReindex.source_positive _ _ _)
            (CorrectionReindex.source_positive _ _ _)
          (edgeEq.symm.trans equal)
        have slots := CorrectionReindex.source_injective _ _ _ _ _ _ sources
        exact same ⟨slots.1.symm, slots.2.1.symm, slots.2.2.symm⟩
      rw [if_neg different, if_neg same]
  exact (CorrectionReindex.grid_congr _ _ terms).trans
    ((CorrectionReindex.grid_delta _ _ _ _).trans
    (prepared.occurrence_selected neighbors occurrence member _))

/-- Exact unsigned reindexing for arbitrary retained side weights. Signs are
supplied by the caller's actual side valuation, not inferred from totals. -/
private theorem CorrectionReindex.selected_sum_eq (prepared :
  AllSurfacePreparation
  regular domains differential)
    (neighbors : PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces)
    (values : Fin base.faces.regulars.length → Fin 2 → GridLiftedDualSteps.GridSide → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (fun sheet =>
      (PhysicalComponentValues.SideNeighbor.componentValue
        (FaceNeighbors.at
        (neighbors.entries.get p) .bottom)) .exterior (values p sheet .bottom) +
      (PhysicalComponentValues.SideNeighbor.componentValue
        (FaceNeighbors.at
        (neighbors.entries.get p) .right)) .exterior (values p sheet .right) +
      (PhysicalComponentValues.SideNeighbor.componentValue
        (FaceNeighbors.at
        (neighbors.entries.get p) .top)) .exterior (values p sheet .top) +
      (PhysicalComponentValues.SideNeighbor.componentValue
        (FaceNeighbors.at
        (neighbors.entries.get p) .left)) .exterior (values p sheet .left))) =
    FiniteSum.Fin.sumFin (fun index : Fin prepared.occurrences.length =>
      let occurrence := prepared.occurrences[index.val]'index.isLt
      values occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side) := by
  let terms := fun p sheet side (index : Fin prepared.occurrences.length) =>
    if (prepared.occurrences[index.val]'index.isLt).placement.indexed =
      ((LocatedFace.sideSource
        (lifted.mesh.locateFace p sheet) side)).project lifted.mesh.triangulation.faces
      then CorrectionReindex.selectedValue neighbors values p sheet side
        else 0
  have each (p : Fin base.faces.regulars.length) (sheet : Fin 2) (side : GridLiftedDualSteps.GridSide) :
      CorrectionReindex.selectedValue neighbors values p sheet side =
        FiniteSum.Fin.sumFin (terms p sheet side) := by
    by_cases zero : CorrectionReindex.selectedValue neighbors values p sheet
      side = 0
    · have zeros (index : Fin prepared.occurrences.length) : terms p sheet side index = 0 := by
        dsimp only [terms, -eq_self, -iff_self]
        rw [zero]
        exact ite_self _
      exact zero.trans ((FiniteSum.Fin.sumFin_congr zeros).trans FiniteSum.Fin.sumFin_zero).symm
    · obtain ⟨_, _, weighted⟩ := prepared.selected_side_weight neighbors p sheet side (values p sheet side) zero
      exact (weighted (fun _ => CorrectionReindex.selectedValue neighbors
        values p sheet side)).symm
  exact (CorrectionReindex.grid_congr _ _ each).trans
    ((CorrectionReindex.grid_swap terms).trans
    (FiniteSum.Fin.sumFin_congr (fun index =>
      CorrectionReindex.selected_at_occurrence prepared neighbors values
      index)))

/-- The original exterior-component selector preserves Gaussian negation. -/
private theorem CorrectionReindex.selected_neg {face : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank}
  {side :
  GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedGridFaces.PuncturedFaces.SideNeighbor base.faces face side) (value :
      Gaussian.Basic.Canonical) :
    PhysicalComponentValues.SideNeighbor.componentValue neighbor .exterior (-value) =
      -PhysicalComponentValues.SideNeighbor.componentValue neighbor .exterior value
      := by
  cases neighbor with
  | exterior _ => rfl
  | neighbor _ _ _ location => cases location <;> exact (neg_zero).symm

/-- The original exterior selector commutes with the finite two-sheet sum. -/
private theorem CorrectionReindex.selected_sum {face : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank}
  {side :
  GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedGridFaces.PuncturedFaces.SideNeighbor base.faces face side) (values : Fin 2 →
      Gaussian.Basic.Canonical) :
    PhysicalComponentValues.SideNeighbor.componentValue neighbor .exterior
      (FiniteSum.Fin.sumFin values) = FiniteSum.Fin.sumFin (fun sheet =>
      PhysicalComponentValues.SideNeighbor.componentValue neighbor .exterior (values
      sheet)) := by
  cases neighbor with
  | exterior _ => rfl
  | neighbor _ _ _ location => cases location <;> exact FiniteSum.Fin.sumFin_zero.symm

/-- Apply the original negative orientation to top and left sides, retaining bottom and right values. -/
private def CorrectionReindex.signed (side : GridLiftedDualSteps.GridSide) (value : Gaussian.Basic.Canonical) :
  Gaussian :=
  if side = .top ∨ side = .left then -value else value

/-- The complete signed exterior side sum equals the original normal-form component evaluation. -/
private theorem CorrectionReindex.signed_grid (neighbors : PuncturedGridFaces.PuncturedFaces.NeighborBank
  base.faces)
    (values : Fin base.faces.regulars.length → Fin 2 → GridLiftedDualSteps.GridSide → Gaussian.Basic.Canonical) :
    CorrectionReindex.gridSum (fun p sheet side =>
      (PhysicalComponentValues.SideNeighbor.componentValue
      (FaceNeighbors.at
      (neighbors.entries.get p) side)) .exterior (CorrectionReindex.signed
      side (values p sheet side))) =
      SelectedPhysicalComponents.componentEvaluation neighbors (fun _ => true) (fun
        side p => FiniteSum.Fin.sumFin (fun sheet => values p sheet side)) .exterior := by
  have bottom (value : Gaussian.Basic.Canonical) :
      CorrectionReindex.signed .bottom value = value := by
    exact if_neg (by intro same; rcases same with same | same <;> cases same)
  have right (value : Gaussian.Basic.Canonical) :
      CorrectionReindex.signed .right value = value := by
    exact if_neg (by intro same; rcases same with same | same <;> cases same)
  have top (value : Gaussian.Basic.Canonical) :
      CorrectionReindex.signed .top value = -value :=
    if_pos (Or.inl rfl)
  have left (value : Gaussian.Basic.Canonical) :
      CorrectionReindex.signed .left value = -value :=
    if_pos (Or.inr rfl)
  simp only [CorrectionReindex.gridSum,
    CorrectionReindex.sideSum, bottom, right, top, left, if_pos (rfl : true
    = true),
    CorrectionReindex.selected_neg, FiniteSum.Fin.sumFin_add,
      FiniteSum.Fin.sumFin_neg,
    SelectedPhysicalComponents.componentEvaluation,
      SelectedPerimeterIdentity.SelectedSides.value,
    CorrectionReindex.selected_sum,
      FaceNeighbors.at, -eq_self,
      -iff_self]
  ring1

/-- Reindex arbitrary oriented side data onto the actual exterior component.
This also applies to conjugated energy values and retained endpoint chords. -/
theorem
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.oriented_sum_eq_component
  (prepared :
  AllSurfacePreparation
  regular domains differential)
    (neighbors : PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces)
    (values : Fin base.faces.regulars.length → Fin 2 → GridLiftedDualSteps.GridSide → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index : Fin prepared.occurrences.length =>
      let occurrence := prepared.occurrences[index.val]'index.isLt
      SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        occurrence.sideOccurrence
        (values occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side)) =
      SelectedPhysicalComponents.componentEvaluation neighbors (fun _ => true)
        (fun side position => FiniteSum.Fin.sumFin (fun sheet => values position sheet side)) .exterior := by
  have reindexed := CorrectionReindex.selected_sum_eq prepared neighbors
    (fun p sheet side => CorrectionReindex.signed side (values p sheet
    side))
  have each (index : Fin prepared.occurrences.length) :
      let occurrence := prepared.occurrences[index.val]'index.isLt
      SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        occurrence.sideOccurrence
        (values occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side) =
      CorrectionReindex.signed occurrence.sideOccurrence.side
        (values occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side) := by
    intro occurrence
    have forward := CorrectionReindex.occurrence_forward prepared occurrence
      (List.getElem_mem index.isLt)
    simp only
      [SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented,
      forward, if_neg (by decide : false ≠ true), -eq_self, -iff_self]
    rfl
  exact (FiniteSum.Fin.sumFin_congr each).trans (reindexed.symm.trans
    (CorrectionReindex.signed_grid neighbors values))

variable {cuts : RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth :
  Nat} {fixed : (sheet : Fin 2) → RegularDomainMeshes.RegularMeshes.Preflights
  domains sheet}
  {meshTarget : Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    meshTarget}

/-- The original cap occurrence remainder is exactly the exterior component
of the normal-form physical correction, on the same normalized perimeters
and triangle readings. No transport equality is supplied by the caller. -/
theorem
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.fineRemainder_eq_physical
  (prepared :
  AllSurfacePreparation
  regular domains differential)
    (neighbors : PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces)
    (perimeters : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
      (right : TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
      :
    prepared.fineRemainder perimeters left right =
      PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors
        left right .exterior := by
  have readback := FiniteSum.Fin.sumFin_congr (fun index : Fin prepared.occurrences.length =>
    ((prepared.occurrences[index.val]'index.isLt).fineRemainder_eq perimeters left right).symm)
  exact (Gaussian.Norm.Sum.Indexed.sumFin_map prepared.occurrences
    (fun occurrence => occurrence.fineRemainder perimeters left right)).symm.trans
      (readback.symm.trans ((prepared.oriented_sum_eq_component neighbors
        (fun p sheet side => HoleAreaRemainder.sideAreaRemainder perimeters p sheet
          side)).trans
          (FullHoleRemainder.component_remainder perimeters neighbors left right
            .exterior)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
