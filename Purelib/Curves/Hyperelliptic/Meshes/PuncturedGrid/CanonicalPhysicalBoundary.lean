module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
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

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib

public section

/-! On the physical boundary the canonical edge chart is the unique
positive triangle source. The existing two-sheet hole request therefore
bounds this cochain directly, without a sewn-value transport premise. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}

/-- On an original physical boundary edge, the canonical valuation equals its unique positive triangle-source increment.

Both readings retain the same original lifted edge and triangle values. -/
theorem canonical_physical_source
    (source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length)
    (member : source.project lifted.mesh.triangulation.faces ∈ lifted.boundaryLoops.flatten)
    (values : Fin lifted.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh values (source.project
      lifted.mesh.triangulation.faces) = source.increment values := by
  have positive := Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.physicalSource_positive lifted source
    member
  have supported : source.project lifted.mesh.triangulation.faces ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences
    lifted.mesh.triangulation.faces ∨
      (source.project lifted.mesh.triangulation.faces).reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences
        lifted.mesh.triangulation.faces :=
    Or.inl (Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member positive)
  let route := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute lifted.mesh (source.project
    lifted.mesh.triangulation.faces) supported
  have routePositive := Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.physicalSource_positive lifted
    route.sourceEdge
    (route.sourceEdge_project.symm ▸ member)
  have same := Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.source_eq_of_project_eq
    lifted.mesh routePositive positive route.sourceEdge_project
  exact (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value lifted.mesh _ supported
    values).symm.trans
    (congrArg (fun chosen : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length =>
      chosen.increment values) same)

/-- The canonical valuation of an original physical source word equals the sum of its actual triangle-source increments.
-/
private theorem physical_word_value
    (sources : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
    (physical : ∀ source ∈ sources, source.project lifted.mesh.triangulation.faces ∈ lifted.boundaryLoops.flatten)
    (values : Fin lifted.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh values) (sources.map (fun source
      => source.project lifted.mesh.triangulation.faces)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.map (fun source => source.increment values)) := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      change Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh values (source.project
        lifted.mesh.triangulation.faces) + _ = source.increment values + _
      exact congrArg₂ (fun first last : Gaussian.Basic.Canonical => first + last)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary.canonical_physical_source source (physical source
          List.mem_cons_self) values)
        (ih (fun next member => physical next (List.mem_cons_of_mem _ member)))

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {target :
    Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate}

/-- The original two-sheet hole request bounds the canonical boundary valuation directly on the same retained triangle
readings. -/
theorem canonical_hole_accurate (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (retained : hole ∈ base.faces.holes)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := lifted.mesh)
      domains differential hole.inwardBoundary target)
    {index : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index
      domains}
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh triangles.values)
      (hole.liftedBoundary lifted.vertices lifted.edges)) < target := by
  have physical : ∀ source ∈ request.sources,
      source.project lifted.mesh.triangulation.faces ∈ lifted.boundaryLoops.flatten := by
    intro source member
    apply Topology.Surface.Sewing.SimpleBoundaryCycles.mem_flatten.mpr
    refine ⟨_, Data.List.Membership.mem_append.mpr (Or.inr (Data.List.Map.mem_map_of_mem retained)), ?_⟩
    rw [← Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation.cancellation_sources_project hole request]
    exact Data.List.Map.mem_map_of_mem member
  have equal := (congrArg (Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh triangles.values))
    (Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation.cancellation_sources_project hole request)).symm.trans
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary.physical_word_value request.sources physical
      triangles.values)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_lt (request.accurate triangles later)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
