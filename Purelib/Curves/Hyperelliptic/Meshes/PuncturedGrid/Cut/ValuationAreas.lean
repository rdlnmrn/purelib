module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Fin
import Purelib.Data.List.Flatten
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.GeneratorExtension
import Purelib.Topology.Surface.Cut.VertexGluing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
import Purelib.Topology.Surface.Cut.PotentialAreas
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents

public section

/-! Whole-surface area and pointwise physical-boundary readbacks for actual test valuations. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ValuationAreas

open Purelib
open Purelib.Algebra
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest
open Purelib.Topology.Surface.Cut.GeneratorExtension
open _root_.Purelib.Topology.Surface.Cut renaming GeneratorExtension -> GeneratorExtension
open Purelib.Topology.Surface.Cut.VertexGluing
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Surface.Sewing.SewingRetraction
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut (GeneratorValuation)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}
  {values : Data.Vector Canonical
    lifted.cutBoundaryWord.alphabet.count}
  (data : GeneratorValuation lifted values)

/-- Vanishing holds on each physical incidence, not merely on the sum around a hole. -/
theorem boundary_edge_zero (edge : Stokes.OrientedEdge lifted.vertices.count)
    (member : edge ∈ lifted.boundaryLoops.flatten) : data.value edge = 0 := by
  obtain ⟨source, onBoundary, equal⟩ := Map.mem_map.mp
    ((lifted.cut_boundary_iff_boundaryComponents edge).mpr member)
  have zero := GeneratorExtension.physical_zero data.extension
    (GeneratorValuation.occurrences_unique lifted)
    data.physical source onBoundary
  exact equal ▸ zero

/-- A word supported on original physical boundary edges has zero retained valuation area. -/
theorem boundary_area_zero (word : List (Stokes.OrientedEdge lifted.vertices.count))
    (supported : ∀ edge ∈ word, edge ∈ lifted.boundaryLoops.flatten) : Purelib.Topology.Mesh.RetracingWords.wordArea
      data.value word = 0 := by
  have increments : word.map data.value = word.map (fun _ => (0 : Data.Gaussian.Basic.Canonical)) :=
    Map.map_congr_left (fun edge member =>
      boundary_edge_zero data edge (supported edge member))
  unfold RetracingWords.wordArea
  rw [increments]
  have zero (items : List (Stokes.OrientedEdge lifted.vertices.count)) :
      IncrementArea.pathArea (items.map (fun _ => (0 : Data.Gaussian.Basic.Canonical))) = 0 := by
    induction items with
    | nil => rfl
    | cons edge rest ih =>
        rw [List.map_cons, IncrementArea.pathArea_cons, ih, IncrementArea.area_zero_left, add_zero]
  exact zero word

/-- Every actual original exterior sheet-walk edge belongs to the retained physical boundary components. -/
private theorem exterior_supported (sheet : Fin 2) (edge : Stokes.OrientedEdge lifted.vertices.count)
    (member : edge ∈ lifted.edges.indexedEdges lifted.vertices base.bank.exterior sheet) :
    edge ∈ lifted.boundaryLoops.flatten := by
  have onExterior : ∀ sheet : Fin 2, ∀ edge ∈ lifted.edges.indexedEdges lifted.vertices base.bank.exterior sheet,
      edge ∈ lifted.edges.indexedEdges lifted.vertices base.bank.exterior 0 ++
        lifted.edges.indexedEdges lifted.vertices base.bank.exterior 1 := by
    intro selected
    refine Data.Fin.cases_induction ?_ (fun last => Data.Fin.cases_induction ?_ (fun impossible => Fin.elim0 impossible)
      last) selected
    · intro edge belongs
      exact Membership.mem_append.mpr (Or.inl belongs)
    · intro edge belongs
      exact Membership.mem_append.mpr (Or.inr belongs)
  change edge ∈ (lifted.exteriorBoundaries ++ _).flatten
  rw [Data.List.Flatten.flatten_append]
  apply Membership.mem_append.mpr
  apply Or.inl
  rw [lifted.exteriorBoundaries_flatten]
  exact onExterior sheet edge member

/-- The original retained exterior sheet walk has zero total generator valuation. -/
theorem exterior_value_zero (sheet : Fin 2) :
    SewingRetraction.wordValue data.value (lifted.edges.indexedEdges lifted.vertices base.bank.exterior sheet) = 0 := by
  apply GeneratorExtension.physical_word_zero data.extension
    (GeneratorValuation.occurrences_unique lifted)
    data.physical
  intro edge member
  exact (lifted.cut_boundary_iff_boundaryComponents edge).mpr
    (exterior_supported sheet edge member)

/-- The original retained exterior sheet walk has zero generator-valuation area. -/
theorem exterior_area_zero (sheet : Fin 2) :
    RetracingWords.wordArea data.value (lifted.edges.indexedEdges lifted.vertices base.bank.exterior sheet) = 0 :=
  boundary_area_zero data _
    (exterior_supported sheet)

/-- The retained cut covers every actual mesh face exactly once. -/
theorem surface_area : RetracingWords.wordArea data.value lifted.cutPolygon.patch.boundary =
    FiniteSum.Fin.sumFin (fun index => RetracingWords.wordArea data.value (lifted.mesh.triangulation.faces
      index).boundary) := by
  have readback := PotentialAreas.surface_area data.extension.readings
    (GeneratorValuation.occurrences_unique lifted)
  apply readback.trans
  apply (Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_perm (fun index => RetracingWords.wordArea data.value
    (lifted.mesh.triangulation.faces index).boundary)
    lifted.cutPolygon.coverage).trans
  rw [OfFn.Basic.map_ofFn]
  exact (Data.Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum _).symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ValuationAreas

end
