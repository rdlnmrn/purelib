module
public import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
public import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
public import Purelib.Topology.Surface.Word.GeneratorValuations
import Batteries.Logic
import Init.Core
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents

open Purelib

open Purelib.Data.List

open Purelib.Riemann

open Purelib.Riemann.Meshes

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut.BoundaryPairs

open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.GeneratorValuations

public section

/-!
# Original physical hole words in the retained cut alphabet

Each original lifted boundary edge is located in the existing one-sided cut
boundary. The executable word retains those cut edges and their triangle
owners. Its valuation is exactly the physical generator valuation used by
the chord-coordinate formula.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

/-- Select the first actual retained boundary edge mapping to the supplied physical edge, with membership and exact
projection certificates. -/
@[expose] def preimage {source target : Nat} (labels : Fin source → Fin target) (edge : Stokes.OrientedEdge target) :
    (boundary : List (Stokes.OrientedEdge source)) → edge ∈ boundary.map (OrientedEdge.map labels) →
      {original : Stokes.OrientedEdge source // original ∈ boundary ∧ OrientedEdge.map labels original = edge}
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member =>
      if same : OrientedEdge.map labels head = edge then ⟨head, List.mem_cons_self, same⟩
      else
        let found := preimage labels edge tail
          ((Membership.mem_cons.mp member).resolve_left (Ne.symm same))
        ⟨found.val, List.mem_cons_of_mem _ found.property.1, found.property.2⟩

/-- Lift the original ordered physical edge word to actual retained cut-boundary edges, preserving each exact projected
occurrence. -/
@[expose] def preimages {source target : Nat} (labels : Fin source → Fin target) (boundary : List (Stokes.OrientedEdge
  source)) :
    (word : List (Stokes.OrientedEdge target)) → (∀ edge ∈ word, edge ∈ boundary.map (OrientedEdge.map labels)) →
      {original : List (Stokes.OrientedEdge source) // (∀ edge ∈ original, edge ∈ boundary) ∧ original.map
        (OrientedEdge.map labels) = word}
  | [], _ => ⟨[], (fun _ member => (List.not_mem_nil member).elim), rfl⟩
  | head :: tail, member =>
      let found := preimage labels head boundary (member
        head List.mem_cons_self)
      let rest := preimages labels boundary tail
        (fun edge present => member edge (List.mem_cons_of_mem _ present))
      ⟨found.val :: rest.val, (fun _ present => (Membership.mem_cons.mp present).elim
        (fun equal => equal ▸ found.property.1) (rest.property.1 _)),
        congrArg₂ List.cons found.property.2 rest.property.2⟩

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}

set_option genInjectivity false in
/-- The actual retained cut-boundary word projecting to an original physical boundary word.

Every selected cut edge remains physical and retains its original triangle source occurrence. -/
structure PhysicalCutWord (lifted : Meshes.LiftedPuncturedGrid base) (original : List (Stokes.OrientedEdge
  lifted.vertices.count)) where
  /-- The cached ordered actual cut-boundary edges. -/ edges : List (Stokes.OrientedEdge
    lifted.cutPolygon.patch.cut.count)
  /-- Every selected actual cut edge belongs to the original one-sided physical boundary. -/ physical : ∀ edge ∈ edges,
    edge ∈ lifted.cutBoundaryPairs.boundary
  /-- The retained cut edges project exactly to the original ordered physical word. -/ project : edges.map
    (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) = original
  /-- The original triangle-source occurrences of these exact retained cut edges. -/ sources :
    SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut edges

constructive_injectivity PhysicalCutWord

namespace PhysicalCutWord

variable {original : List (Purelib.Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)}

/-- Select actual physical preimages of the original boundary word and cache their retained triangle-source
certificates. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base) (original : List (Stokes.OrientedEdge
  lifted.vertices.count))
    (physical : ∀ edge ∈ original, edge ∈ lifted.boundaryLoops.flatten) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords.PhysicalCutWord lifted original :=
  let selected := Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords.preimages
    lifted.cutPolygon.patch.cut.vertexLabels lifted.cutBoundaryPairs.boundary original
    (fun edge member => (lifted.cut_boundary_iff_boundaryComponents edge).mpr (physical edge member))
  let sources := PathSources.build lifted.cutPolygon.patch.cut selected.val (fun edge member =>
    Or.inl (lifted.cutBoundaryPairs.boundary_subset (selected.property.1 edge member)))
  ⟨selected.val, selected.property.1, selected.property.2, sources⟩

/-- The retained cut word has exactly the original physical word's length. -/
theorem length_eq (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords.PhysicalCutWord lifted original)
  : word.edges.length = original.length := by
  have equal := congrArg List.length word.project
  rw [Map.length_map] at equal
  exact equal

/-- The actual cached triangle-source occurrences project exactly to the original physical word. -/
theorem sources_project (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords.PhysicalCutWord lifted
  original) :
    word.sources.sources.map (fun source => source.project lifted.mesh.triangulation.faces) = original :=
  word.sources.sources_project.trans word.project

/-- Every actual physical boundary edge occurs as an original cut-alphabet generator. -/
private theorem physical_index {source target : Nat} {labels : Fin source → Fin target}
    (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)) {edge : Stokes.OrientedEdge source} :
    ∀ boundary : List (Stokes.OrientedEdge source), edge ∈ boundary →
      ∃ index : Fin (CutAlphabet.ofLists boundary pairs).count, (CutAlphabet.ofLists boundary pairs).generators index =
        edge
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩
      · obtain ⟨index, equal⟩ :=
          physical_index pairs tail
          member
        exact ⟨index.succ, equal⟩

/-- The physical generator valuation reads exactly the actual retained cut-edge endpoint increment. -/
private theorem generator_increment (values : PrimitiveSewing.PrimitiveValues lifted.cutPolygon.patch.cut.count)
    (edge : Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count) (physical : edge ∈ lifted.cutBoundaryPairs.boundary)
      :
    ProjectedEdgePairing.generatorValue lifted.cutBoundaryPairs (fun index =>
      values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).finish - values
        ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).start)
        (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels edge) = values edge.finish - values edge.start := by
  obtain ⟨index, equal⟩ := physical_index
    lifted.cutBoundaryPairs.pairs lifted.cutBoundaryPairs.boundary physical
  rw [← equal]
  apply ProjectedEdgePairing.generatorValue_generator lifted.cutBoundaryPairs
  rw [lifted.cutPolygon.patch.cut.boundary_eq]
  exact SewnPatch.boundary_unique lifted.cutPolygon.patch
    (SinglePolygon.originalEdges_unique
      lifted.cutPolygon lifted.mesh.orientedEdges_unique)

/-- This is the valuation appearing in the physical-cycle decomposition, read directly from the actual cut-generator
increments. -/
theorem generator_sum (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords.PhysicalCutWord lifted
  original) (values : PrimitiveSewing.PrimitiveValues lifted.cutPolygon.patch.cut.count) :
    SewingRetraction.wordValue (ProjectedEdgePairing.generatorValue lifted.cutBoundaryPairs (fun index =>
      values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).finish - values
        ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).start)) original =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (word.edges.map fun edge => values edge.finish - values edge.start)
        := by
  refine (congrArg (SewingRetraction.wordValue (ProjectedEdgePairing.generatorValue lifted.cutBoundaryPairs (fun index
    =>
    values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).finish -
      values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).start)))
        word.project).symm.trans ?_
  have sum : ∀ edges : List (Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count),
      (∀ edge ∈ edges, edge ∈ lifted.cutBoundaryPairs.boundary) →
      SewingRetraction.wordValue (ProjectedEdgePairing.generatorValue lifted.cutBoundaryPairs (fun index =>
        values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).finish -
          values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).start))
        (edges.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels)) =
          Data.Gaussian.Norm.Sum.Basic.gaussianSum (edges.map fun edge => values edge.finish - values edge.start)
            := by
    intro edges
    induction edges with
    | nil => intro _; rfl
    | cons head tail ih =>
        intro physical
        change _ + SewingRetraction.wordValue _ (tail.map _) = _ + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (tail.map _)
        exact congrArg₂ (fun first last : Data.Gaussian.Basic.Canonical => first + last)
          (generator_increment values head
            (physical head List.mem_cons_self))
          (ih (fun edge member => physical edge (List.mem_cons_of_mem _ member)))
  exact sum word.edges word.physical

end PhysicalCutWord

/-- Lift an actual retained branch-hole boundary to its original physical cut edges and triangle sources. -/
@[expose] def holeCutWord (lifted : Meshes.LiftedPuncturedGrid base) (hole : PuncturedGridFaces.BranchHole
  base.bank.toBranchCellBank)
    (retained : hole ∈ base.faces.holes) : PhysicalCutWord
      lifted (hole.liftedBoundary lifted.vertices lifted.edges) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords.PhysicalCutWord.build lifted _ (fun _ member =>
    SimpleBoundaryCycles.mem_flatten.mpr
    ⟨_, Membership.mem_append.mpr (Or.inr (Map.mem_map_of_mem retained)), member⟩)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords
