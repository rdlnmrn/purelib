module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PuncturedVertexStars
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
public import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSheetCancellation
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.VertexLiftChoices
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.VertexCellSteps
import Purelib.Riemann.Integration.PuncturedVertexConnections
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence

public section

/-!
# Both actual lifted occurrences of an original grid edge

One retained regular incident face supplies both triangle occurrences. Their
cached source edges project to the two original transported grid edges, with
the original orientation. Opposite-sheet cancellation is therefore about
those actual occurrences, including reversed sides of branch holes.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration.PuncturedVertexStars
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedFaces
open Purelib.Riemann.Meshes.PuncturedEdgeFaces
open Purelib.Riemann.Normalization
open Purelib.Topology.Mesh.QuadrilateralDual
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Topology.Mesh.QuadrilateralDual (QuadOccurrence)
open Purelib.Riemann.Integration.PuncturedVertexStars (VertexStar)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}

namespace EdgeOccurrences

/-- Equal original face-sheet indices give the same actual side-start sheet for both retained lifted-face occurrences.

The equality retains the original lifted faces and their endpoint coordinates. Their indexed start vertices therefore
read the same sheet from the original vertex bank. -/
theorem startSheet_equal {face : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank}
    {firstSheet lastSheet : Fin 2} (first : BranchCellBank.LiftedFace vertices edges face firstSheet)
    (last : BranchCellBank.LiftedFace vertices edges face lastSheet) (equal : firstSheet = lastSheet) (side :
      GridLiftedDualSteps.GridSide) :
    first.sideStartSheet side = last.sideStartSheet side := by
  cases equal
  have same := congrArg (fun quad => (quad.edge side.kind).start) (first.quad_eq last)
  rw [first.side_edge_eq, last.side_edge_eq] at same
  exact vertices.index_same_sheet _ (face.side side).vertices.1 _ _ same

/-- The actual lifts beginning on the two original vertex sheets occupy opposite retained face sheets.

The retained start-sheet equality excludes identical face sheets. Their two bounded coordinates identify the other
original sheet without selecting another incident face. -/
theorem selected_opposite (cell : PuncturedEdgeFaces.RegularEdgeCell base start finish)
    (first : cell.first.Lifted mesh 0) (last : cell.first.Lifted mesh 1) :
    last.value.sheet = BranchCutLifts.otherSheet first.value.sheet := by
  have different : first.value.sheet ≠ last.value.sheet := by
    intro same
    have sheets := startSheet_equal
      first.value.located.lifted last.value.located.lifted same cell.first.corner.side
    rw [first.value.start_eq, last.value.start_eq] at sheets
    exact (by decide : (0 : Fin 2) ≠ 1) sheets
  have unequal : first.value.sheet.val ≠ last.value.sheet.val := fun equal => different (Fin.ext equal)
  have firstBound := first.value.sheet.isLt
  have lastBound := last.value.sheet.isLt
  by_cases zero : first.value.sheet.val = 0
  · have firstEq : first.value.sheet = (⟨0, by decide⟩ : Fin 2) := Fin.ext zero
    rw [firstEq]
    exact Fin.ext (by change last.value.sheet.val = 1; omega)
  · have firstEq : first.value.sheet = (⟨1, by decide⟩ : Fin 2) := Fin.ext (show first.value.sheet.val = 1 by omega)
    rw [firstEq]
    exact Fin.ext (by change last.value.sheet.val = 0; omega)

/-- Equal actual grid-edge endpoints identify the indexed lift on the supplied original sheet. -/
private theorem indexedEdge_same {otherStart otherFinish : Data.Gaussian.Basic.Canonical}
    (edge : Walks.Edge base.bank.grid start finish) (other : Walks.Edge base.bank.grid otherStart otherFinish)
    (first : otherStart = start) (last : otherFinish = finish) (sheet : Fin 2) :
    edges.indexedEdge vertices other sheet = edges.indexedEdge vertices edge sheet := by
  cases first
  cases last
  exact edges.indexedEdge_eq vertices other edge (BranchCellBank.referenceAt base.bank.toBranchCellBank _
    edge.vertices.1).toLoop
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ edge.vertices.2).toLoop sheet

/-- The retained selected face side, with its actual reversal flag, projects to the original oriented indexed grid edge.
-/
private theorem side_projects (cell : PuncturedEdgeFaces.RegularEdgeCell base start finish) (edge : Walks.Edge
  base.bank.grid start finish)
    {sheet : Fin 2} (lifted : cell.first.Lifted mesh sheet) :
    (if cell.geometry.reversed then (lifted.value.located.lifted.quad.edge cell.geometry.side.kind).reverse
      else lifted.value.located.lifted.quad.edge cell.geometry.side.kind) = edges.indexedEdge vertices edge sheet := by
  let side := base.faces.regulars[cell.located.index.val].side cell.geometry.side
  have cellEq : base.faces.regulars[cell.located.index.val].cell = cell.geometry.cell := cell.first.indexed_cell
  cases orientation : cell.geometry.reversed with
  | false =>
      have firstEq : cell.geometry.side.start cell.geometry.cell.box = start := by
        have retained := cell.geometry.start_eq
        rw [orientation, if_neg (show false ≠ true by intro impossible; nomatch impossible)] at retained
        exact retained
      have lastEq : cell.geometry.side.finish cell.geometry.cell.box = finish := by
        have retained := cell.geometry.finish_eq
        rw [orientation, if_neg (show false ≠ true by intro impossible; nomatch impossible)] at retained
        exact retained
      rw [if_neg (show false ≠ true by intro impossible; nomatch impossible)]
      rw [lifted.value.located.lifted.side_edge_eq, lifted.startSheet_at cell.geometry.side firstEq]
      exact indexedEdge_same edge side (by
          rw [cellEq];
          exact firstEq) (by rw [cellEq]; exact lastEq) sheet
  | true =>
      have firstEq : cell.geometry.side.finish cell.geometry.cell.box = start := by
        have retained := cell.geometry.start_eq
        rw [orientation, if_pos (Eq.refl true)] at retained
        exact retained
      have lastEq : cell.geometry.side.start cell.geometry.cell.box = finish := by
        have retained := cell.geometry.finish_eq
        rw [orientation, if_pos (Eq.refl true)] at retained
        exact retained
      have opposite := edges.indexedEdge_opposite_of_endpoints vertices side edge
        (by rw [cellEq]; exact firstEq.symm) (by rw [cellEq]; exact lastEq.symm)
        (BranchCellBank.referenceAt base.bank.toBranchCellBank _ side.vertices.1).toLoop (BranchCellBank.referenceAt
          base.bank.toBranchCellBank _ side.vertices.2).toLoop
        (lifted.value.located.lifted.sideStartSheet cell.geometry.side)
      have transported : (edges.edge side).forward.target (lifted.value.located.lifted.sideStartSheet
        cell.geometry.side) = sheet :=
        (lifted.value.located.lifted.side_transport cell.geometry.side).trans (lifted.finishSheet_at cell.geometry.side
          firstEq)
      rw [transported] at opposite
      rw [if_pos (Eq.refl true)]
      rw [lifted.value.located.lifted.side_edge_eq]
      exact opposite.symm

/-- Select the actual retained triangle-edge occurrence of the original grid edge, preserving its orientation and face
sheet. -/
@[expose] def selectedSource (cell : PuncturedEdgeFaces.RegularEdgeCell base start finish) {sheet : Fin 2} (lifted :
  cell.first.Lifted mesh sheet) :
    SewnPrimitiveContacts.SourceEdge mesh.triangles.length :=
  let kind := cell.geometry.side.kind
  let source := mesh.triangleIndex cell.located.index lifted.value.sheet (QuadOccurrence.upperSide kind)
  if cell.geometry.reversed then ⟨source, FaceCorners.lastCorner kind, FaceCorners.firstCorner kind⟩
  else ⟨source, FaceCorners.firstCorner kind, FaceCorners.lastCorner kind⟩

/-- The selected actual triangle source edge projects exactly to the original indexed grid edge on its supplied sheet.
-/
theorem selectedSource_project (cell : PuncturedEdgeFaces.RegularEdgeCell base start finish) (edge : Walks.Edge
  base.bank.grid start finish)
    {sheet : Fin 2} (lifted : cell.first.Lifted mesh sheet) :
    (selectedSource cell lifted).project
      mesh.triangulation.faces = edges.indexedEdge vertices edge sheet := by
  have quadEq := (mesh.locateFace cell.located.index lifted.value.sheet).lifted.quad_eq lifted.value.located.lifted
  have selected : (selectedSource cell lifted).project
    mesh.triangulation.faces =
      if cell.geometry.reversed then (lifted.value.located.lifted.quad.edge cell.geometry.side.kind).reverse
      else lifted.value.located.lifted.quad.edge cell.geometry.side.kind := by
    cases orientation : cell.geometry.reversed
    · dsimp only [selectedSource]
      rw [orientation, if_neg (show false ≠ true by intro impossible; nomatch impossible)]
      dsimp only [SourceEdge.project]
      rw [mesh.triangleIndex_face, FaceCorners.source_edge, quadEq,
        if_neg (show false ≠ true by intro impossible; nomatch impossible)]
    · dsimp only [selectedSource]
      rw [orientation, if_pos (Eq.refl true)]
      dsimp only [SourceEdge.project]
      rw [mesh.triangleIndex_face]
      exact congrArg OrientedEdge.reverse ((FaceCorners.source_edge _ _).trans (congrArg (fun quad => quad.edge
        cell.geometry.side.kind) quadEq))
  exact selected.trans (side_projects cell edge lifted)

end EdgeOccurrences

set_option genInjectivity false in
/-- Both actual triangle occurrences of one original oriented grid edge.

A single retained regular incident face supplies their opposite face sheets and exact cached source-edge readbacks. -/
structure EdgeOccurrences (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (edge : Walks.Edge base.bank.grid
    start
  finish) where
  /-- The actual retained regular incident face and oriented grid-edge geometry. -/ cell :
    PuncturedEdgeFaces.RegularEdgeCell base start finish
  /-- The retained incident-face lift starting on original vertex sheet zero. -/ zero : cell.first.Lifted mesh 0
  /-- The retained incident-face lift starting on original vertex sheet one. -/ one : cell.first.Lifted mesh 1
  /-- The actual retained face sheets are opposite. -/ opposite : one.value.sheet = BranchCutLifts.otherSheet
    zero.value.sheet
  /-- The cached actual triangle source edge on original starting sheet zero. -/ zeroSource :
    SewnPrimitiveContacts.SourceEdge mesh.triangles.length
  /-- The zero-source cache is exactly the selected original incident-face occurrence. -/ zeroSource_eq : zeroSource =
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences.selectedSource cell zero
  /-- The cached actual triangle source edge on original starting sheet one. -/ oneSource :
    SewnPrimitiveContacts.SourceEdge mesh.triangles.length
  /-- The one-source cache is exactly the selected original incident-face occurrence. -/ oneSource_eq : oneSource =
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences.selectedSource cell one

constructive_injectivity EdgeOccurrences

namespace EdgeOccurrences

/-- Acquire one actual regular incident face and retain both original sheet lifts and their exact source-edge
occurrences. -/
@[expose] def build (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (edge : Walks.Edge base.bank.grid start
  finish) : EdgeOccurrences mesh edge :=
  let cell := RegularEdgeCell.acquire (VertexStar.build base start edge.vertices.1) edge
  let zero := cell.first.lift mesh 0
  let one := cell.first.lift mesh 1
  ⟨cell, zero, one, selected_opposite cell zero one,
    selectedSource cell zero, rfl,
    selectedSource cell one, rfl⟩

variable {edge : Purelib.Polynomial.Geometry.Grid.Walks.Edge base.bank.grid start finish}

/-- The cached zero-sheet source edge projects exactly to the original oriented indexed edge. -/
theorem zero_project (paired : EdgeOccurrences mesh edge) :
  paired.zeroSource.project mesh.triangulation.faces = edges.indexedEdge vertices edge 0 := by
  rw [paired.zeroSource_eq]
  exact selectedSource_project paired.cell edge
    paired.zero

/-- The cached one-sheet source edge projects exactly to the original oriented indexed edge. -/
theorem one_project (paired : EdgeOccurrences mesh edge) :
  paired.oneSource.project mesh.triangulation.faces = edges.indexedEdge vertices edge 1 := by
  rw [paired.oneSource_eq]
  exact selectedSource_project paired.cell edge
    paired.one

/-- Prepare the opposite-sheet primitive comparison on the actual retained incident face and its original corner pair.
-/
@[expose] def request (paired : EdgeOccurrences mesh edge)
  (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) (differential : Differentials.Basic.Differential
  genus)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    PairedEdgeRequests.PairedEdgeRequest (domains.get paired.cell.located.index) differential
      (FaceCorners.point base.faces.regulars[paired.cell.located.index.val].cell.box (FaceCorners.quad.edge
        paired.cell.geometry.side.kind).start)
      (FaceCorners.point base.faces.regulars[paired.cell.located.index.val].cell.box (FaceCorners.quad.edge
        paired.cell.geometry.side.kind).finish) target :=
  TriangleSheetCancellation.pairedEdgeRequest domains differential paired.cell.located.index
    paired.cell.geometry.side.kind target positive

/-- The two actual retained source-edge increments cancel within the requested target at sufficient original numerical
stages, including reversed edge orientations. -/
theorem accurate (paired : EdgeOccurrences mesh edge) {domains :
  DomainBanks.FaceDomainBank frames base.faces.regulars} {differential : Differentials.Basic.Differential genus}
    {leftIndex rightIndex : Nat} {leftBank : PrimitiveData.FacePrimitiveBank differential leftIndex domains} {rightBank
      : PrimitiveData.FacePrimitiveBank differential rightIndex domains}
    (left : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh) {target : InverseRootPolynomial.Coordinate}
    (request : PairedEdgeRequests.PairedEdgeRequest (domains.get paired.cell.located.index) differential
      (FaceCorners.point base.faces.regulars[paired.cell.located.index.val].cell.box (FaceCorners.quad.edge
        paired.cell.geometry.side.kind).start)
      (FaceCorners.point base.faces.regulars[paired.cell.located.index.val].cell.box (FaceCorners.quad.edge
        paired.cell.geometry.side.kind).finish) target)
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq (paired.zeroSource.increment left.values + paired.oneSource.increment
      right.values) < target := by
  have cases : paired.zero.value.sheet = (⟨0, by decide⟩ : Fin 2) ∨
      paired.zero.value.sheet = (⟨1, by decide⟩ : Fin 2) := by
    have bound := paired.zero.value.sheet.isLt
    by_cases zero : paired.zero.value.sheet.val = 0
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext (show paired.zero.value.sheet.val = 1 by omega))
  rcases cases with zero | one
  · change paired.zero.value.sheet = (0 : Fin 2) at zero
    have other : paired.one.value.sheet = 1 := by rw [paired.opposite, zero]; rfl
    have bound := TriangleSheetCancellation.opposite_edge_accurate left right paired.cell.located.index
      paired.cell.geometry.side.kind request leftLater rightLater
    rw [paired.zeroSource_eq, paired.oneSource_eq]
    cases orientation : paired.cell.geometry.reversed
    · dsimp only [selectedSource]
      rw [orientation, if_neg (show false ≠ true by intro impossible; nomatch impossible)]
      dsimp only [SourceEdge.increment]
      rw [zero, other]
      exact bound
    · dsimp only [selectedSource]
      rw [orientation, if_pos (Eq.refl true)]
      dsimp only [SourceEdge.increment]
      rw [zero, other]
      have same (a b c d : Data.Gaussian.Basic.Canonical) : a - b + (c - d) = -(b - a + (d - c)) := by ring1
      rw [same, Data.Gaussian.Norm.Basic.normSq_neg]
      exact bound
  · change paired.zero.value.sheet = (1 : Fin 2) at one
    have other : paired.one.value.sheet = 0 := by rw [paired.opposite, one]; rfl
    have bound := TriangleSheetCancellation.opposite_edge_accurate right left paired.cell.located.index
      paired.cell.geometry.side.kind request rightLater leftLater
    rw [paired.zeroSource_eq, paired.oneSource_eq]
    cases orientation : paired.cell.geometry.reversed
    · dsimp only [selectedSource]
      rw [orientation, if_neg (show false ≠ true by intro impossible; nomatch impossible)]
      dsimp only [SourceEdge.increment]
      rw [one, other]
      rw [add_comm]
      exact bound
    · dsimp only [selectedSource]
      rw [orientation, if_pos (Eq.refl true)]
      dsimp only [SourceEdge.increment]
      rw [one, other]
      have same (a b c d : Data.Gaussian.Basic.Canonical) : a - b + (c - d) = -(d - c + (b - a)) := by ring1
      rw [same, Data.Gaussian.Norm.Basic.normSq_neg]
      exact bound

end EdgeOccurrences
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

end
