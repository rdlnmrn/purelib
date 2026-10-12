module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.List.Permutation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib

public section

/-!
# Branch-hole cancellation for the retained cut owners

The physical boundary has no reverse triangle occurrence. Consequently any
source projecting to it is the unique positive triangle owner. This identifies
the paired cancellation sources with existing cut-path caches. The resulting
sewn increment bound retains the cached sewing allowance.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

/-- A triangle source is degenerate, positively oriented, or projects to the reverse of a triangle boundary edge. -/
private theorem corner_orientations {vertexCount faceCount : Nat}
    (faces : Fin faceCount → Topology.Polygon.Stokes.OrientedTriangle vertexCount) (source :
      Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge faceCount) :
    source.first = source.last ∨ Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source faces ∨
      (source.project faces).reverse ∈ (faces source.source).boundary := by
  rcases source with ⟨position, ⟨first, firstBound⟩, ⟨last, lastBound⟩⟩
  have firstCases : first = 0 ∨ first = 1 ∨ first = 2 := by omega
  have lastCases : last = 0 ∨ last = 1 ∨ last = 2 := by omega
  rcases firstCases with rfl | rfl | rfl <;> rcases lastCases with rfl | rfl | rfl <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl List.mem_cons_self)
      | exact Or.inr (Or.inl (List.mem_cons_of_mem _ List.mem_cons_self))
      | exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      | exact Or.inr (Or.inr List.mem_cons_self)
      | exact Or.inr (Or.inr (List.mem_cons_of_mem _ List.mem_cons_self))
      | exact Or.inr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison in
/-- A source projecting to the actual physical boundary has positive orientation because the reverse triangle occurrence
is absent. -/
theorem physicalSource_positive (lifted : Meshes.LiftedPuncturedGrid base)
    (source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length)
    (member : source.project lifted.mesh.triangulation.faces ∈ lifted.boundaryLoops.flatten) :
    Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source lifted.mesh.triangulation.faces := by
  have boundary := (lifted.boundaryLoops_edge_iff _).mp member
  rcases corner_orientations lifted.mesh.triangulation.faces source with same | positive | reverse
  · have equal : (source.project lifted.mesh.triangulation.faces).reverse = source.project
      lifted.mesh.triangulation.faces := by
      unfold Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.project
      rw [same]
      rfl
    exact (boundary.2 (equal.symm ▸ boundary.1)).elim
  · exact positive
  · exact (boundary.2 (Data.List.Flatten.mem_flatMap.mpr
      ⟨lifted.mesh.triangulation.faces source.source,
        Data.List.Permutation.ofFn_mem _ source.source, reverse⟩)).elim

/-- Every edge of a retained branch-hole boundary belongs to the original complete physical boundary. -/
private theorem hole_edge_member (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (retained : hole ∈ base.faces.holes) {edge : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count}
    (member : edge ∈ hole.liftedBoundary lifted.vertices lifted.edges) : edge ∈ lifted.boundaryLoops.flatten :=
  Topology.Surface.Sewing.SimpleBoundaryCycles.mem_flatten.mpr ⟨_, Data.List.Membership.mem_append.mpr
    (Or.inr (Data.List.Map.mem_map_of_mem retained)), member⟩

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {target :
    Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate}

/-- The actual physical boundary forces positive source orientation; a
caller need not certify which side the geometric lookup selected. -/
theorem hole_sources_positive (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (retained : hole ∈ base.faces.holes)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := lifted.mesh)
      domains differential hole.inwardBoundary target) :
    ∀ source ∈ request.sources, Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source
      lifted.mesh.triangulation.faces := by
  intro source member
  apply Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.physicalSource_positive lifted source
  apply Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.hole_edge_member hole retained
  rw [← Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation.cancellation_sources_project hole request]
  exact Data.List.Map.mem_map_of_mem member

/-- Existing occurrence caches are identified exactly, without rebuilding
their geometry or comparing independently prepared root paths. -/
theorem hole_sources_eq (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (retained : hole ∈ base.faces.holes)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := lifted.mesh)
      domains differential hole.inwardBoundary target)
    (sources : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
    (projected : sources.map (fun source => source.project lifted.mesh.triangulation.faces) =
      hole.liftedBoundary lifted.vertices lifted.edges) : sources = request.sources := by
  apply Topology.Mesh.TriangleSourceUniqueness.SourceEdge.list_eq_of_project_eq lifted.mesh.orientedEdges_unique
      (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.corners_injective lifted.mesh)
      sources request.sources ?_ (Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.hole_sources_positive
        hole retained request)
      (projected.trans (Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation.cancellation_sources_project hole
        request).symm)
  intro source member
  apply Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.physicalSource_positive lifted source
  apply Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.hole_edge_member hole retained
  rw [← projected]
  exact Data.List.Map.mem_map_of_mem member

/-- The shared triangle bound applies to the sources already retained by
the cut, rather than only to the auxiliary paired-walk source list. -/
theorem hole_source_sum_accurate (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (retained : hole ∈ base.faces.holes)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := lifted.mesh)
      domains differential hole.inwardBoundary target)
    {sampleIndex : Nat} {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential
      sampleIndex domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics lifted.mesh)
      (later : request.index ≤ sampleIndex)
    (sources : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
    (projected : sources.map (fun source => source.project lifted.mesh.triangulation.faces) =
      hole.liftedBoundary lifted.vertices lifted.edges) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.map fun source =>
      source.increment readings.values)) < target := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.hole_sources_eq hole retained request sources
    projected]
  exact request.accurate readings later

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
