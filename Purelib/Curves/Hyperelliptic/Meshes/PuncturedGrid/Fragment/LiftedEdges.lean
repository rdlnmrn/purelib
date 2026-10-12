module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Flatten
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.List.Permutation
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedQueryNegation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RectangleDetours
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries
import Purelib.Riemann.Meshes.GridLiftedEdgeConnections
import Init.ByCases
import Init.Data.Bool
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Tactic.QuotientFreeOmega
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence

public section

/-!
# Actual lifted grid edges containing original period fragments

The retained regular face and original fragment sheet determine an oriented
side of the existing lifted mesh. Its original-owner certificate transports
through that same clear face to the actual grid-edge start owner.
-/

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Data.List
open Purelib.Geometry
open Purelib.Polynomial.Clearance.Box
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Winding
open Purelib.Riemann.Integration.PreparedQueryNegation
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedFaces
open Purelib.Riemann.Meshes.GridLiftedMesh
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.ClearBoxPathWinding
open Purelib.Riemann.Paths.ClearBoxPaths
open Purelib.Riemann.Paths.OwnerLoopMonodromy
open Purelib.Riemann.Paths.PreparedPathTrace
open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels
open Purelib.Riemann.RootContinuation.RootPathTransport
open Purelib.Riemann.Topology
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon
open Purelib.Data.Rat

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.LocatedFace

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {position : Fin faces.regulars.length} {sheet : Fin 2}

/-- Select a side of this retained face, without another global edge lookup. -/
@[expose] def edgeLocation (located : mesh.LocatedFace position sheet) (kind : RectangleEdge.Kind) :
    LiftedFaces.EdgeLocation mesh.lifts (located.lifted.quad.edge kind) :=
  ⟨_, position, rfl, sheet, located.lifted, kind, rfl, fun candidate member => by
    let side := RectangleDetours.kindOfEdge located.lifted.quad candidate member
    rw [← mesh.triangleEdges_eq, ← side.property]
    exact Flatten.mem_flatMap.mpr ⟨_, Permutation.ofFn_mem _ _, located.occurrence.edge_mem side.val⟩⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.LocatedFace

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.RegularEdgeCell

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.PuncturedEdgeFaces (RegularEdgeCell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {start finish : Gaussian}

set_option genInjectivity false in
/-- The actual oriented lifted grid side containing an original regular-edge occurrence.

The retained face index, sheet and endpoint coordinates identify its original mesh route and preserve reachability of
both actual root owners. -/
structure LiftedSide (cell : PuncturedEdgeFaces.RegularEdgeCell base start finish)
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (sheet : Fin 2) where
  /-- The retained actual oriented edge in the original lifted vertex bank. -/ edge : Stokes.OrientedEdge vertices.count
  /-- The existing lifted-mesh route for this exact edge occurrence. -/ route : MeshPathWalks.EdgeRoute mesh edge
  /-- The route uses exactly the original located regular-face position. -/ position_eq : route.position =
    cell.located.index
  /-- The routed face is exactly the face at the original retained location. -/ face_eq : route.face =
    base.faces.regulars[cell.located.index.val]
  /-- The routed face sheet is exactly the supplied original fragment sheet. -/ sheet_eq : route.sheet = sheet
  /-- The actual lifted start coordinate is the original segment start. -/ start_eq : vertices.coordinate edge.start =
    start
  /-- The actual lifted finish coordinate is the original segment finish. -/ finish_eq : vertices.coordinate edge.finish
    = finish
  /-- This exact lifted edge is the original grid edge lifted on its retained starting sheet. -/ indexed_eq : ∀ original
    : Walks.Edge base.bank.grid start finish,
    edge = edges.indexedEdge vertices original (vertices.sheet edge.start)
  /-- Both actual lifted endpoint owners are reached from the same original face-sheet owner. -/ reached : ∀ models :
    BranchCellBank.FaceModels frames base.faces.regulars[cell.located.index.val],
    PreparedFaceTracePrefixes.Reached base.faces.regulars[cell.located.index.val].cell.box (models.frame.owners sheet)
      (vertices.owner frames edge.start) ∧
      PreparedFaceTracePrefixes.Reached base.faces.regulars[cell.located.index.val].cell.box (models.frame.owners sheet)
        (vertices.owner frames edge.finish)

constructive_injectivity LiftedSide

namespace LiftedSide

/-- Equal actual grid-edge endpoints give the same retained indexed lift on the supplied sheet.

The two original edge occurrences retain their endpoint owners. The supplied sheet and the endpoint equalities identify
their indexed lifts in the same retained edge bank. -/
theorem indexed_same {otherStart otherFinish : Gaussian}
    (original : Walks.Edge base.bank.grid start finish) (other : Walks.Edge base.bank.grid otherStart otherFinish)
    (first : otherStart = start) (last : otherFinish = finish) (sheet : Fin 2) :
    edges.indexedEdge vertices other sheet = edges.indexedEdge vertices original sheet := by
  cases first
  cases last
  exact edges.indexedEdge_eq vertices other original
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ original.vertices.1).toLoop
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ original.vertices.2).toLoop sheet

/-- The original forward face side equals the actual grid edge lifted on its retained starting sheet.

Both endpoint equalities refer to the original face side and edge occurrence. The indexed lift uses the sheet of the
same retained lifted start vertex. -/
theorem forward_indexed {face : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank} {sheet : Fin 2}
    (lifted : BranchCellBank.LiftedFace vertices edges face sheet) (side : GridLiftedDualSteps.GridSide)
    (original : Walks.Edge base.bank.grid start finish)
    (first : side.start face.cell.box = start) (last : side.finish face.cell.box = finish) :
    lifted.quad.edge side.kind = edges.indexedEdge vertices original (vertices.sheet (lifted.quad.edge side.kind).start)
      := by
  rw [lifted.side_edge_eq]
  change edges.indexedEdge vertices (face.side side) (lifted.sideStartSheet side) =
    edges.indexedEdge vertices original (vertices.sheet (vertices.index _ (face.side side).vertices.1
      (lifted.sideStartSheet side)))
  rw [vertices.sheet_index]
  exact indexed_same original
    (face.side side) first last _

/-- The reversed original face side equals the actual grid edge lifted on its retained final sheet.

Reversal interchanges the two original endpoint owners. The indexed reverse edge uses the sheet of the retained lifted
finish vertex without selecting a new edge bank. -/
theorem backward_indexed {face : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank} {sheet : Fin 2}
    (lifted : BranchCellBank.LiftedFace vertices edges face sheet) (side : GridLiftedDualSteps.GridSide)
    (original : Walks.Edge base.bank.grid start finish)
    (first : side.finish face.cell.box = start) (last : side.start face.cell.box = finish) :
    (lifted.quad.edge side.kind).reverse =
      edges.indexedEdge vertices original (vertices.sheet (lifted.quad.edge side.kind).finish) := by
  rw [lifted.side_edge_eq]
  change (edges.indexedEdge vertices (face.side side) (lifted.sideStartSheet side)).reverse =
    edges.indexedEdge vertices original (vertices.sheet (vertices.index _ (face.side side).vertices.2 ((edges.edge
      (face.side side)).forward.target (lifted.sideStartSheet side))))
  rw [vertices.sheet_index]
  exact (edges.indexedEdge_opposite_of_endpoints vertices (face.side side) original first.symm last.symm
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (face.side side).vertices.1).toLoop
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (face.side side).vertices.2).toLoop (lifted.sideStartSheet
      side)).symm

/-- Orientation follows the retained incident-cell certificate.

The sheet is the face sheet already selected for the original fragment. -/
@[expose] def build (cell : PuncturedEdgeFaces.RegularEdgeCell base start finish) (mesh : GridLiftedMesh.LiftedMesh
  vertices edges base.faces)
    (sheet : Fin 2) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.RegularEdgeCell.LiftedSide cell
      mesh sheet := by
  let located := mesh.locateFace cell.located.index sheet
  let location := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.LocatedFace.edgeLocation located
    cell.geometry.side.kind
  have cellEq : base.faces.regulars[cell.located.index.val].cell = cell.geometry.cell :=
    (congrArg RegularFace.cell cell.located.indexed).trans cell.located.cell_eq
  have coordinates := located.lifted.rectangleCoordinates.edge_coordinates cell.geometry.side.kind
  rw [cellEq] at coordinates
  have first : vertices.coordinate (located.lifted.quad.edge cell.geometry.side.kind).start =
      cell.geometry.side.start cell.geometry.cell.box := congrArg Prod.fst coordinates
  have last : vertices.coordinate (located.lifted.quad.edge cell.geometry.side.kind).finish =
      cell.geometry.side.finish cell.geometry.cell.box := congrArg Prod.snd coordinates
  cases orientation : cell.geometry.reversed with
  | false =>
      have startEq : cell.geometry.side.start cell.geometry.cell.box = start := by
        have retained := cell.geometry.start_eq
        rw [orientation, if_neg (by intro impossible; nomatch impossible)] at retained
        exact retained
      have finishEq : cell.geometry.side.finish cell.geometry.cell.box = finish := by
        have retained := cell.geometry.finish_eq
        rw [orientation, if_neg (by intro impossible; nomatch impossible)] at retained
        exact retained
      exact ⟨_, .forward location, rfl, rfl, rfl, first.trans startEq, last.trans finishEq,
        (fun original =>
          forward_indexed
          located.lifted cell.geometry.side original
          (by rw [cellEq]; exact startEq) (by rw [cellEq]; exact finishEq)),
        fun models => location.endpoints_reached models⟩
  | true =>
      have startEq : cell.geometry.side.finish cell.geometry.cell.box = start := by
        have retained := cell.geometry.start_eq
        rw [orientation, if_pos (Eq.refl true)] at retained
        exact retained
      have finishEq : cell.geometry.side.start cell.geometry.cell.box = finish := by
        have retained := cell.geometry.finish_eq
        rw [orientation, if_pos (Eq.refl true)] at retained
        exact retained
      exact ⟨(located.lifted.quad.edge cell.geometry.side.kind).reverse, .backward location,
        rfl, rfl, rfl, last.trans startEq, first.trans finishEq,
        (fun original =>
          backward_indexed
          located.lifted cell.geometry.side original
          (by rw [cellEq]; exact startEq) (by rw [cellEq]; exact finishEq)),
        fun models => ⟨(location.endpoints_reached models).2, (location.endpoints_reached models).1⟩⟩

end LiftedSide
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.RegularEdgeCell

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.Reached

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)

/-- Reverse a reachability proof by a finite clear return route.

The loop certificate proves the return owner; it does not assume trace-edge reversal. -/
theorem reverse_in_clear_box {polynomial : ClearPath.GaussianPolynomial} {box : Rational.Box} {start
  finish : Gaussian}
    {first : SquareRootContinuationChain.Owner (polynomial.eval start)} {last : SquareRootContinuationChain.Owner
      (polynomial.eval finish)}
    (clearance : Region.RegionClearance polynomial box) (degree : 0 < polynomial.natDegree)
    (reference : OwnerLoopMonodromy.WindingOneLoop polynomial start) (firstInside : box.Contains start) (lastInside :
      box.Contains finish)
    (reached : PreparedFaceTracePrefixes.Reached box first last) : PreparedFaceTracePrefixes.Reached box last first :=
      by
  obtain ⟨forward, forwardWinding⟩ := reached
  let route := Route.build clearance finish start lastInside firstInside
  let returned := TracedPath.build route.path route.within last
  have returnWinding := (TracedPath.winding_original returned).trans (Route.winding clearance degree route lastInside)
  have loopWinding : Polygon.Basic.chainRaw polynomial start (forward.append returned.trace.get).vertices = 8 * (0 :
    Int) := by
    rw [OwnerPath.append_winding, forwardWinding, returnWinding]
    omega
  have equivalent := OwnerPath.rootEquivalent_of_even_with_reference reference (forward.append returned.trace.get) 0
    loopWinding
  exact (show PreparedFaceTracePrefixes.Reached box last returned.finishOwner from ⟨returned.trace.get,
    returnWinding⟩).append (Reached.ofEquivalent equivalent)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.Reached

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank FaceDomains)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.PuncturedEdgeFaces (RegularEdgeCell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid} {parent :
    CenteredEdge curve source}
  {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
    {interval : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
  {fragment : RegularPrimitiveFragment axes
    parent partition interval}
  {domains : FaceDomainBank frames
    base.faces.regulars}
  {count : Nat} {target : Rational} {request :
    LocalRequest parent count target}

/-- Transporting the retained domain cache along equality of faces preserves actual owner reachability.

The equality changes only the face index of the retained domain cache. Eliminating that equality preserves the original
owner and reachability witness. -/
theorem castFace_reached {first last : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank}
    (equal : first = last) (cached : DomainBanks.FaceDomains frames first) {point : Gaussian}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval point)} (sheet : Fin 2)
    (reached : PreparedFaceTracePrefixes.Reached last.cell.box ((cached.castFace equal).models.frame.owners sheet)
      owner) :
    PreparedFaceTracePrefixes.Reached first.cell.box (cached.models.frame.owners sheet) owner := by
  cases equal
  exact reached

set_option genInjectivity false in
/-- Both actual program query owners are reached from the lifted start vertex of the complete containing grid edge.
Internal fragment endpoints retain their own coordinates and are not promoted to grid vertices.

The retained source endpoints are linked to the original assigned sheet entry and mesh route. Both reachability
certificates refer to their original cached owners. -/
structure LiftedSource (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request) (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces) where
  /-- The actual original containing lifted grid side on the fragment's retained sheet. -/ side :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.RegularEdgeCell.LiftedSide fragment.face mesh
    assigned.entry.sheet
  /-- The original fragment's final parameter lies in the retained unit interval. -/ finishInside : 0 ≤ interval.upper ∧
    interval.upper ≤ 1
  /-- The actual original first query owner is reached from the retained containing edge's start owner. -/ first_reached
    : PreparedFaceTracePrefixes.Reached base.faces.regulars[fragment.face.located.index.val].cell.box
    (vertices.owner frames side.edge.start)
    (PreparedEdge.ownerAtPoint parent.edge interval.lower assigned.fractionInside fragment.located.first
      fragment.located.first_eq.symm)
  /-- The actual original final query owner is reached from the same retained containing edge's start owner. -/
    finish_reached : PreparedFaceTracePrefixes.Reached base.faces.regulars[fragment.face.located.index.val].cell.box
    (vertices.owner frames side.edge.start)
    (PreparedEdge.ownerAtPoint parent.edge interval.upper finishInside fragment.located.last
      fragment.located.last_eq.symm)

constructive_injectivity LiftedSource

/-- Retain the fragment's actual containing grid side and transport both original query owners through that same clear
face from its start owner. -/
@[expose] def LiftedSource.build (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request) (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    LiftedSource assigned mesh := by
  let side := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.RegularEdgeCell.LiftedSide.build
    fragment.face mesh assigned.entry.sheet
  let face := base.faces.regulars[fragment.face.located.index.val]
  let cached := domains.get fragment.face.located.index
  have bounds := partition.interval_bounds fragment.located.member
  have finishInside : 0 ≤ interval.upper ∧ interval.upper ≤ 1 :=
    ⟨bounds.1.trans interval.ordered.le, bounds.2⟩
  have first := castFace_reached fragment.face.located.indexed cached assigned.entry.sheet
    (SheetEntry.first_query_reached assigned)
  have last := castFace_reached fragment.face.located.indexed cached assigned.entry.sheet
    (SheetEntry.finish_query_reached assigned finishInside)
  have corner := (side.reached cached.models).1
  have cornerInside : face.cell.box.Contains (vertices.coordinate side.edge.start) := by
    rw [side.start_eq]
    exact (congrArg RegularFace.cell fragment.face.located.indexed).symm ▸
      (fragment.face.located.cell_eq.symm ▸ fragment.face.geometry.first.corner.contains)
  have back := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.Reached.reverse_in_clear_box
    face.clearance (BranchIsolation.degreePositive curve)
    (BranchCellBank.referenceAt base.bank.toBranchCellBank face.cell.box.anchor (face.cell.anchor_mem
      face.member)).toLoop
    face.cell.box.contains_anchor cornerInside corner
  exact ⟨side, finishInside, back.append first, back.append last⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry

end
