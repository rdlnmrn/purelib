module
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Data.List

open Purelib.Riemann.Meshes

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-! Match each corrected single-lap hole to the actual clockwise physical
boundary, with its transported starting sheet. Physical source readings
agree exactly with the canonical valuation; no chart error is hidden here. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary (canonical_physical_source)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base}

/-- Every edge of a retained inward sheet lap belongs to the full physical hole boundary. -/
private theorem lap_member (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (sheet : Fin 2)
    {edge : Stokes.OrientedEdge lifted.vertices.count}
    (member : edge ∈ lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary sheet) :
    edge ∈ hole.liftedBoundary lifted.vertices lifted.edges := by
  rw [hole.liftedBoundary_eq]
  have cases : sheet = 0 ∨ sheet = 1 := by
    have bound := sheet.isLt
    by_cases zero : sheet.val = 0
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext (by change sheet.val = 1; omega))
  rcases cases with rfl | rfl
  · exact Data.List.Membership.mem_append.mpr (Or.inl member)
  · exact Data.List.Membership.mem_append.mpr (Or.inr member)

/-- Source increments on actual physical boundary occurrences equal their canonical edge values in the retained source
order. -/
private theorem physical_values (values : Fin lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (sources : List (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
    (physical : ∀ source ∈ sources, source.project lifted.mesh.triangulation.faces ∈ lifted.boundaryLoops.flatten) :
    sources.map (fun source => source.increment values) =
      sources.map (fun source => CanonicalEdgeValues.edgeValuation lifted.mesh values (source.project
        lifted.mesh.triangulation.faces)) := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      exact congrArg₂ List.cons (CanonicalPhysicalBoundary.canonical_physical_source source (physical source
        List.mem_cons_self) values).symm
        (ih (fun source member => physical source (List.mem_cons_of_mem _ member)))

/-- The retained physical hole-lap source increments equal the canonical indexed lap values on its transported starting
sheet. -/
theorem hole_lap_values (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (retained : hole ∈
  base.faces.holes)
    (paired : WalkOccurrences.PairedWalk lifted.mesh hole.inwardBoundary)
    (values : Fin lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) (sheet : Fin 2) :
    (paired.sources sheet).map (fun source => source.increment values) =
      (lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary sheet).map (CanonicalEdgeValues.edgeValuation
        lifted.mesh values) := by
  rw [← paired.sources_project, Data.List.Map.map_map]
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords.physical_values
  intro source member
  have projected : source.project lifted.mesh.triangulation.faces ∈
      (paired.sources sheet).map (fun source => source.project lifted.mesh.triangulation.faces) :=
    Map.mem_map_of_mem member
  rw [paired.sources_project] at projected
  exact SimpleBoundaryCycles.mem_flatten.mpr ⟨_, Data.List.Membership.mem_append.mpr
    (Or.inr (Map.mem_map_of_mem retained)), Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords.lap_member hole
      sheet projected⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords
