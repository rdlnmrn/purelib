module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSelection
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Riemann.Meshes.GridLiftedBoundarySimplicity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents

public section

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Riemann
open Purelib

/-! Every exterior-selected face side belongs to the actual root-labelled
exterior word. A reversed occurrence would require a cell outside the fixed
ambient box; strict interiority excludes all branch-hole words. -/
namespace Purelib

open Purelib.Topology.Polygon.Stokes

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

/-- The four strict coordinate-direction bits of an ordered pair of Gaussian endpoints. -/
private def Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction (ends :
  Gaussian.Basic.Canonical × Gaussian.Basic.Canonical) : Bool × Bool × Bool × Bool :=
  (decide (ends.1.re < ends.2.re), decide (ends.2.re < ends.1.re),
    decide (ends.1.im < ends.2.im), decide (ends.2.im < ends.1.im))

/-- The fixed coordinate-direction pattern of each oriented rectangle-edge kind. -/
private def Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.kindDirection :
  Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.Kind → Bool × Bool × Bool × Bool
  | .bottom => (true, false, false, false)
  | .right => (false, false, true, false)
  | .downDiagonal => (false, true, false, true)
  | .upDiagonal => (true, false, true, false)
  | .top => (false, true, false, false)
  | .left => (false, false, false, true)

/-- A proper rectangle edge has the direction pattern assigned to its edge kind. -/
private theorem Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction_coordinates {box :
  Geometry.Rational.Box} (proper : box.Proper) (kind
  : Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.Kind) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction
      (Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.coordinates box kind) =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.kindDirection kind  := by
  have noX : ¬ box.xUpper < box.xLower := fun less => proper.1.2 less.1
  have noY : ¬ box.yUpper < box.yLower := fun less => proper.2.2 less.1
  have selfXLower : ¬ box.xLower < box.xLower := fun less => less.2 less.1
  have selfXUpper : ¬ box.xUpper < box.xUpper := fun less => less.2 less.1
  have selfYLower : ¬ box.yLower < box.yLower := fun less => less.2 less.1
  have selfYUpper : ¬ box.yUpper < box.yUpper := fun less => less.2 less.1
  cases kind <;>
    dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction,
      Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.coordinates,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.kindDirection] <;>
    simp only [decide_eq_true proper.1, decide_eq_true proper.2,
      decide_eq_false noX, decide_eq_false noY,
      decide_eq_false selfXLower, decide_eq_false selfXUpper,
      decide_eq_false selfYLower, decide_eq_false selfYUpper, -eq_self, -iff_self] <;> rfl

/-- Reversing a proper rectangle side gives the direction pattern of its opposite side. -/
private theorem Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction_reverse {box :
  Geometry.Rational.Box} (proper : box.Proper) (side :
  Meshes.GridLiftedDualSteps.GridSide) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction
      (Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.coordinates box side.kind).swap =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.kindDirection side.opposite.kind  := by
  have noX : ¬ box.xUpper < box.xLower := fun less => proper.1.2 less.1
  have noY : ¬ box.yUpper < box.yLower := fun less => proper.2.2 less.1
  have selfXLower : ¬ box.xLower < box.xLower := fun less => less.2 less.1
  have selfXUpper : ¬ box.xUpper < box.xUpper := fun less => less.2 less.1
  have selfYLower : ¬ box.yLower < box.yLower := fun less => less.2 less.1
  have selfYUpper : ¬ box.yUpper < box.yUpper := fun less => less.2 less.1
  cases side <;>
    dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction,
      Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.coordinates,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.kindDirection,
      Meshes.GridLiftedDualSteps.GridSide.kind, Meshes.GridLiftedDualSteps.GridSide.opposite, Prod.swap] <;>
    simp only [decide_eq_true proper.1, decide_eq_true proper.2,
      decide_eq_false noX, decide_eq_false noY,
      decide_eq_false selfXLower, decide_eq_false selfXUpper,
      decide_eq_false selfYLower, decide_eq_false selfYUpper, -eq_self, -iff_self] <;> rfl

/-- The four direction bits distinguish all six oriented rectangle-edge kinds. -/
private theorem Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.kindDirection_injective :
  Function.Injective kindDirection := by
  intro first last equal
  cases first <;> cases last <;> first | rfl | cases equal

/-- The reverse of an ambient exterior side cannot be an edge of another proper contained cell.

Matching endpoint coordinates would force an opposite side outside the original ambient rectangle. -/
private theorem Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.no_reverse {face other ambient :
  Geometry.Rational.Box} (proper : face.Proper)
  (otherProper : other.Proper)
    (inside : other.Refines ambient) (side : Meshes.GridLiftedDualSteps.GridSide) (exterior : side.Exterior face
      ambient)
    (kind : Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.Kind) :
    (Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.coordinates face side.kind).swap ≠
      Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.coordinates other kind := by
  intro equal
  have same := Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.kindDirection_injective
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction_reverse proper side).symm.trans
    ((congrArg Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction equal).trans
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.direction_coordinates otherProper kind)))
  subst kind
  have x1 := congrArg (fun ends : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical => ends.1.re) equal
  have x2 := congrArg (fun ends : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical => ends.2.re) equal
  have y1 := congrArg (fun ends : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical => ends.1.im) equal
  have y2 := congrArg (fun ends : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical => ends.2.im) equal
  have matching : side.Matches face other := by
    cases side with
    | bottom => exact ⟨x2, x1, y1⟩
    | top => exact ⟨x1, x2, y1⟩
    | left => exact ⟨y1, y2, x1⟩
    | right => exact ⟨y2, y1, x1⟩
  exact Meshes.GridLiftedDualSteps.GridSide.exterior_no_match exterior otherProper inside matching

section LiftedPuncturedGrid

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}

/-- Every original located regular-cell side has positive orientation in its retained triangle. -/
private theorem Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.LiftedPuncturedGrid.side_positive
  (lifted : Meshes.LiftedPuncturedGrid base)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : Meshes.GridLiftedDualSteps.GridSide) :
    Purelib.Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
        (lifted.mesh.locateFace position sheet) side)
      lifted.mesh.triangulation.faces := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
    Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive
    Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.project
  rw [lifted.mesh.triangleIndex_face]
  cases side <;> first
    | exact List.mem_cons_self
    | exact List.mem_cons_of_mem _ List.mem_cons_self
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The reversed original exterior-side edge is absent from the retained triangulation occurrences. -/
private theorem Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.LiftedPuncturedGrid.side_no_reverse
  (lifted : Meshes.LiftedPuncturedGrid base)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : Meshes.GridLiftedDualSteps.GridSide)
    (exterior : side.Exterior (base.faces.regulars[position.val]'position.isLt).cell.box
      (Hyperelliptic.Branches.Cuts.Ambient curve)) :
    ((lifted.mesh.locateFace position sheet).lifted.quad.edge side.kind).reverse ∉
      Topology.Polygon.Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces := by
  intro member
  let located := lifted.mesh.locateFace position sheet
  let other := lifted.mesh.locateEdge _ member
  have equal := (congrArg Prod.swap (located.lifted.rectangleCoordinates.edge_coordinates side.kind)).symm.trans
    ((congrArg (fun edge : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count =>
      (lifted.vertices.coordinate edge.start, lifted.vertices.coordinate edge.finish)) other.edge_eq).symm.trans
        (other.lifted.rectangleCoordinates.edge_coordinates other.kind))
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.no_reverse
    (base.faces.regulars[position.val]'position.isLt).cell.box_proper
    other.face.cell.box_proper other.face.cell.box_refines side exterior other.kind equal

/-- A point inside a retained strictly interior branch hole cannot lie on the ambient rectangle boundary. -/
private theorem
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.LiftedPuncturedGrid.hole_not_on_ambient (hole :
  Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (point :
  Gaussian.Basic.Canonical)
    (inside : hole.cell.box.Contains point)
    (boundary : point.re = (Hyperelliptic.Branches.Cuts.Ambient curve).xLower ∨ point.re =
      (Hyperelliptic.Branches.Cuts.Ambient curve).xUpper ∨
      point.im = (Hyperelliptic.Branches.Cuts.Ambient curve).yLower ∨ point.im = (Hyperelliptic.Branches.Cuts.Ambient
        curve).yUpper) : False := by
  have strict := base.hole_interior hole
  rcases boundary with left | right | bottom | top
  · exact (ne_of_lt (strict.left.trans_le inside.1)) left.symm
  · exact (ne_of_lt (inside.2.1.trans_lt strict.right)) right
  · exact (ne_of_lt (strict.bottom.trans_le inside.2.2.1)) bottom.symm
  · exact (ne_of_lt (inside.2.2.2.trans_lt strict.top)) top

/-- A geometrically exterior regular side is an edge of the original
root-closed exterior word, with the same sheet and positive source. -/
theorem Riemann.Meshes.LiftedPuncturedGrid.exterior_side_member (lifted : Meshes.LiftedPuncturedGrid
  base)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : Meshes.GridLiftedDualSteps.GridSide)
    (exterior : side.Exterior (base.faces.regulars[position.val]'position.isLt).cell.box
      (Hyperelliptic.Branches.Cuts.Ambient curve)) :
    (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
      (lifted.mesh.locateFace position sheet) side).project lifted.mesh.triangulation.faces ∈
      lifted.exteriorBoundaries.flatten := by
  let located := lifted.mesh.locateFace position sheet
  have positive := Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.LiftedPuncturedGrid.side_positive lifted position
    sheet side)
  rw [Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource_project
    located] at positive ⊢
  have boundary := (lifted.boundaryLoops_edge_iff _).mpr
    ⟨positive, Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.LiftedPuncturedGrid.side_no_reverse lifted
      position sheet side exterior⟩
  rw [Meshes.LiftedPuncturedGrid.boundaryLoops, Data.List.Flatten.flatten_append] at boundary
  rcases Data.List.Membership.mem_append.mp boundary with outer | holes
  · exact outer
  · obtain ⟨word, wordMember, edgeMember⟩ := Topology.Surface.Sewing.SimpleBoundaryCycles.mem_flatten.mp holes
    obtain ⟨hole, _, wordEq⟩ := Data.List.Map.mem_map.mp wordMember
    rw [← wordEq] at edgeMember
    have inside := hole.liftedBoundary_start_inside lifted.vertices lifted.edges
      (Data.List.Map.mem_map_of_mem edgeMember)
    have coordinate := congrArg Prod.fst (located.lifted.rectangleCoordinates.edge_coordinates side.kind)
    dsimp only [Prod.fst] at coordinate
    have ambient : (lifted.vertices.coordinate (located.lifted.quad.edge side.kind).start).re =
      (Hyperelliptic.Branches.Cuts.Ambient curve).xLower ∨
        (lifted.vertices.coordinate (located.lifted.quad.edge side.kind).start).re =
          (Hyperelliptic.Branches.Cuts.Ambient curve).xUpper ∨
        (lifted.vertices.coordinate (located.lifted.quad.edge side.kind).start).im =
          (Hyperelliptic.Branches.Cuts.Ambient curve).yLower ∨
        (lifted.vertices.coordinate (located.lifted.quad.edge side.kind).start).im =
          (Hyperelliptic.Branches.Cuts.Ambient curve).yUpper := by
      rw [coordinate]
      cases side with
      | bottom => exact Or.inr (Or.inr (Or.inl exterior))
      | right => exact Or.inr (Or.inl exterior)
      | top => exact Or.inr (Or.inr (Or.inr exterior))
      | left => exact Or.inl exterior
    exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.LiftedPuncturedGrid.hole_not_on_ambient hole _
      inside ambient).elim

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
namespace AllSurfacePreparation

variable {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential
  genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- Every nonzero face-neighbor exterior term has one retained source with
exactly the original triangle, corners and sheet. Its coefficient in the
occurrence sum is one for arbitrary weights, not merely for area samples. -/
theorem
  selected_side_weight
    (prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : Meshes.GridLiftedDualSteps.GridSide)
    (value : Gaussian.Basic.Canonical)
    (selected : Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue
      (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
      (neighbors.entries.get position) side) .exterior value ≠ 0) :
    ∃ index : Fin prepared.occurrences.length,
      (prepared.occurrences[index.val]'index.isLt).sideOccurrence.source =
        Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
          (lifted.mesh.locateFace position sheet) side ∧
      ∀ values : Fin prepared.occurrences.length → Gaussian.Basic.Canonical,
        FiniteSum.Fin.sumFin (fun other =>
          if (prepared.occurrences[other.val]'other.isLt).placement.indexed =
            (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
              (lifted.mesh.locateFace position sheet) side).project lifted.mesh.triangulation.faces
          then values other else 0) = values index := by
  have exterior := Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.exterior_component_supported
    (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
    (neighbors.entries.get position) side) value selected
  have member := lifted.exterior_side_member position sheet side exterior
  obtain ⟨index, found, weighted⟩ := prepared.occurrence_weight _ member
  let occurrence := prepared.occurrences[index.val]'index.isLt
  have projected := ((congrArg (fun source => source.project lifted.mesh.triangulation.faces)
    occurrence.side_source).trans occurrence.placement.location.sourceEdge_project).trans found
  have physical : occurrence.sideOccurrence.source.project lifted.mesh.triangulation.faces ∈
    lifted.boundaryLoops.flatten := by
    rw [projected, Meshes.LiftedPuncturedGrid.boundaryLoops, Data.List.Flatten.flatten_append]
    exact Data.List.Membership.mem_append.mpr (Or.inl member)
  exact ⟨index, Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.source_eq_of_project_eq
    lifted.mesh
    (Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.physicalSource_positive lifted _ physical)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideCompleteness.LiftedPuncturedGrid.side_positive lifted position
      sheet side) projected, weighted⟩

end AllSurfacePreparation
end Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
end LiftedPuncturedGrid
end Purelib
