module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedExteriorPathGeometry
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceAlignment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Orientation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents

public section

/-! The retained cap occurrences are actual exterior sides of the original
neighbor classification. This transports values, not just boundary points. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSelection

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

/-- A nondegenerate horizontal segment on one rectangle side lies at the lower or upper vertical coordinate. -/
private theorem horizontal_boundary {box : Purelib.Geometry.Rational.Box} {lower upper height :
  Purelib.Data.Rat.Fraction.Rational}
    (proper : lower < upper) (same : Purelib.Riemann.Paths.PreparedBoundarySegments.SameSide box ⟨lower, height⟩ ⟨upper,
      height⟩) :
    height = box.yLower ∨ height = box.yUpper := by
  rcases same with left | right | bottom | top
  · exact ((ne_of_lt proper) (left.1.trans left.2.symm)).elim
  · exact ((ne_of_lt proper) (right.1.trans right.2.symm)).elim
  · exact Or.inl bottom.1
  · exact Or.inr top.1

/-- A nondegenerate vertical segment on one rectangle side lies at the left or right horizontal coordinate. -/
private theorem vertical_boundary {box : Purelib.Geometry.Rational.Box} {lower upper horizontal :
  Purelib.Data.Rat.Fraction.Rational}
    (proper : lower < upper) (same : Purelib.Riemann.Paths.PreparedBoundarySegments.SameSide box ⟨horizontal, lower⟩
      ⟨horizontal, upper⟩) :
    horizontal = box.xLower ∨ horizontal = box.xUpper := by
  rcases same with left | right | bottom | top
  · exact Or.inl left.1
  · exact Or.inr right.1
  · exact ((ne_of_lt proper) (bottom.1.trans bottom.2.symm)).elim
  · exact ((ne_of_lt proper) (top.1.trans top.2.symm)).elim

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSelection in
/-- A proper contained rectangle side lying on the ambient boundary is its corresponding exterior side. -/
private theorem side_exterior {face ambient : Purelib.Geometry.Rational.Box} {side :
  Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide}
    (proper : face.Proper) (inside : face.Refines ambient) (boundary :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary face ambient side) :
    side.Exterior face ambient := by
  cases side with
  | bottom =>
    rcases horizontal_boundary proper.1 boundary.2.2 with same | same
    · exact same
    · exact ((ne_of_lt (proper.2.trans_le inside.2.2.2)) same).elim
  | top =>
    rcases horizontal_boundary proper.1 boundary.2.2.reverse with same | same
    · exact ((ne_of_lt (inside.2.2.1.trans_lt proper.2)) same.symm).elim
    · exact same
  | left =>
    rcases vertical_boundary proper.2 boundary.2.2.reverse with same | same
    · exact same
    · exact ((ne_of_lt (proper.1.trans_le inside.2.1)) same).elim
  | right =>
    rcases vertical_boundary proper.2 boundary.2.2 with same | same
    · exact ((ne_of_lt (inside.1.trans_lt proper.1)) same.symm).elim
    · exact same

/-- A retained walk on rectangle sides satisfies the same-side relation on every original edge. -/
private theorem walk_sameSide {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}
    {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} : {start finish : Gaussian.Basic.Canonical} → (walk :
      Purelib.Polynomial.Geometry.Grid.Walks.Walk grid start finish) →
    Purelib.Riemann.Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides ambient walk.path → walk.Edgewise
      (Purelib.Riemann.Paths.PreparedBoundarySegments.SameSide ambient)
  | _, _, .nil _, _ => trivial
  | _, _, .cons _ tail, sides => ⟨sides.1,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSelection.walk_sameSide tail sides.2⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSelection

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace AllSurfacePreparation

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceOccurrence)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- Equal retained exterior edges have equal original occurrence indices.

The simple exterior boundary gives distinct starting vertices in the same ordered occurrence list. -/
private theorem occurrence_index_injective (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (first last : Fin prepared.occurrences.length)
    (equal : (prepared.occurrences[first.val]'first.isLt).placement.indexed =
      (prepared.occurrences[last.val]'last.isLt).placement.indexed) : first = last := by
  have starts : (prepared.occurrences.map (fun occurrence => occurrence.placement.indexed.start)).Nodup := by
    have maps : (prepared.occurrences.map (fun occurrence => occurrence.placement.indexed)).map
        Topology.Polygon.Stokes.OrientedEdge.start =
        prepared.occurrences.map (fun occurrence => occurrence.placement.indexed.start) := Data.List.Map.map_map _ _ _
    have equal := maps.symm.trans
      (congrArg (List.map Topology.Polygon.Stokes.OrientedEdge.start) prepared.indexed_eq)
    exact equal.symm ▸ lifted.exteriorBoundaries_simple
  have distinct := Data.List.Pairwise.pairwise_map.mp starts
  have same := congrArg Topology.Polygon.Stokes.OrientedEdge.start equal
  rcases Nat.lt_trichotomy first.val last.val with before | equal | after
  · exact (Data.List.Pairwise.pairwise_getElem distinct _ _ first.isLt last.isLt before same).elim
  · exact Fin.ext equal
  · exact (Data.List.Pairwise.pairwise_getElem distinct _ _ last.isLt first.isLt after same.symm).elim

/-- Every edge of the original root-closed exterior has exactly one retained
occurrence index. The witness reads the original list, including its sheet;
it does not select or prepare a replacement geometric path. -/
private theorem occurrence_index_unique (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (edge : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)
    (member : edge ∈ lifted.exteriorBoundaries.flatten) :
    ∃ index : Fin prepared.occurrences.length,
      (prepared.occurrences[index.val]'index.isLt).placement.indexed = edge ∧
      ∀ other : Fin prepared.occurrences.length,
        (prepared.occurrences[other.val]'other.isLt).placement.indexed = edge → other = index := by
  have retained : edge ∈ prepared.occurrences.map (fun occurrence => occurrence.placement.indexed) :=
    prepared.indexed_eq.symm ▸ member
  obtain ⟨occurrence, belongs, edgeEq⟩ := Data.List.Map.mem_map.mp retained
  have indexed : occurrence ∈ List.ofFn (fun i : Fin prepared.occurrences.length =>
      prepared.occurrences[i.val]'i.isLt) :=
    (Data.List.OfFn.Basic.ofFn_getElem prepared.occurrences).symm ▸ belongs
  obtain ⟨index, occurrenceEq⟩ := Data.List.OfFn.Basic.mem_ofFn.mp indexed
  have found := (congrArg (fun value => value.placement.indexed) occurrenceEq).trans edgeEq
  exact ⟨index, found, fun other same => prepared.occurrence_index_injective other index (same.trans found.symm)⟩

/-- The exterior edge selects exactly one original occurrence, for arbitrary
Gaussian weights. This is the multiplicity identity needed when interchanging
the occurrence sum with the face-and-sheet sum. -/
theorem occurrence_weight (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (edge : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)
    (member : edge ∈ lifted.exteriorBoundaries.flatten) :
    ∃ index : Fin prepared.occurrences.length,
      (prepared.occurrences[index.val]'index.isLt).placement.indexed = edge ∧
      ∀ values : Fin prepared.occurrences.length → Gaussian.Basic.Canonical,
        FiniteSum.Fin.sumFin (fun other =>
          if (prepared.occurrences[other.val]'other.isLt).placement.indexed = edge then values other else 0) =
          values index := by
  obtain ⟨index, found, unique⟩ := prepared.occurrence_index_unique edge member
  refine ⟨index, found, ?_⟩
  intro values
  have terms (other : Fin prepared.occurrences.length) :
      (if (prepared.occurrences[other.val]'other.isLt).placement.indexed = edge then values other else 0) =
        if other = index then values other else 0 := by
    by_cases same : other = index
    · subst other
      rw [if_pos found, if_pos rfl]
    · rw [if_neg same, if_neg (fun equal => same (unique other equal))]
  exact (FiniteSum.Fin.sumFin_congr terms).trans
    (FiniteSum.Fin.sumFin_ite_eq index values)

/-- Every retained cap occurrence is an actual exterior side of its original regular cell.

The original root-closed walk, edge projection and side boundary certificates identify the corresponding ambient-box
side. -/
theorem occurrence_exterior (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (occurrence :
      SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences) :
    occurrence.sideOccurrence.side.Exterior
      (base.faces.regulars[occurrence.sideOccurrence.position.val]'occurrence.sideOccurrence.position.isLt).cell.box
      (Hyperelliptic.Branches.Cuts.Ambient curve) := by
  have retained := prepared.occurrences_eq ▸ member
  obtain ⟨component, _, belongs⟩ := Data.List.Flatten.mem_flatMap.mp retained
  have indexed : occurrence.placement.indexed ∈ component.program.indexed :=
    component.prepared.occurrences_eq ▸ Data.List.Map.mem_map_of_mem belongs
  have onSide := Geometry.Grid.Walks.Walk.Edgewise.indexed lifted.edges lifted.vertices
    component.program.period.closed.walk
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSelection.walk_sameSide _
      (by rw [component.program.walk_eq]; exact
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorWalk_sides base)) component.program.sheet
    occurrence.placement.indexed indexed
  have endpoints := component.program.indexed_boundary _ indexed
  have projected := (congrArg (fun source => source.project lifted.mesh.triangulation.faces)
    occurrence.side_source).trans
    occurrence.placement.location.sourceEdge_project
  have boundary : Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences.SideOccurrence.OnBoundary
    occurrence.sideOccurrence (Hyperelliptic.Branches.Cuts.Ambient curve) := by
    unfold Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences.SideOccurrence.OnBoundary
    rw [projected]
    exact ⟨endpoints.1.1, endpoints.2.1, onSide⟩
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSelection.side_exterior

        (base.faces.regulars[occurrence.sideOccurrence.position.val]'
          occurrence.sideOccurrence.position.isLt).cell.box_proper

        (base.faces.regulars[occurrence.sideOccurrence.position.val]'
          occurrence.sideOccurrence.position.isLt).cell.box_refines
    (Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.BranchCellBank.LiftedMesh.SideOccurrence.boundary
      occurrence.sideOccurrence boundary)

/-- Every retained occurrence survives the normal-form exterior selector.
The value can contain the full fine path area and its endpoint corrections. -/
theorem occurrence_selected (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces)
    (occurrence :
      SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    (value : Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue
      (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
        (neighbors.entries.get occurrence.sideOccurrence.position) occurrence.sideOccurrence.side)
      .exterior value = value := by
  have exterior := prepared.occurrence_exterior occurrence member
  cases Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
    (neighbors.entries.get occurrence.sideOccurrence.position) occurrence.sideOccurrence.side with
  | exterior _ => rfl
  | neighbor cell _ matching _ =>
    exact (Meshes.GridLiftedDualSteps.GridSide.exterior_no_match exterior cell.box_proper cell.box_refines
      matching).elim

end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

end
