module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Addition
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
public import Purelib.Topology.Surface.Boundary.BoundaryCaps
public import Purelib.Topology.Surface.Sewing.AreaChainTests
import Init.Data.List.OfFn
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring
import Purelib.Riemann.Meshes.GridLiftedBoundary

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.List

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.BoundaryCaps

open Purelib.Topology.Surface.Sewing

public section

/-!
# Oppositely oriented fans on the retained exterior components

The words come from the already prepared surface occurrences. Each component
gets a distinct new apex, and the original surface faces are retained. Exact
finite Stokes cancels the exterior area and leaves precisely the branch-hole
area. This is the incidence part of the attachment; reciprocal-coordinate
geometry and positivity are separate obligations.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram exteriorWalk_even)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_map sumValues_congr)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    base.faces.regulars}

/-- The actual retained exterior program's indexed word closes on its original starting root sheet. -/
theorem indexed_closed (program : PeriodPrograms.ExteriorProgram lifted differential) :
    ∃ anchor, PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish program.indexed anchor anchor := by
  have winding : (ClearPath.rawWinding program.period.closed.walk.path) =
      8 * ((ClearPath.rawWinding program.period.closed.walk.path) / 8) := by
    rw [program.walk_eq]
    exact PeriodPrograms.exteriorWalk_even base
  have returned := RootEdgeBank.target_even lifted.edges
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩).toLoop
    program.period.closed.walk ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩
    ((ClearPath.rawWinding program.period.closed.walk.path) / 8) winding program.sheet
  exact ⟨_, lifted.edges.indexedEdges_closed lifted.vertices program.period.closed.walk
    ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ program.sheet returned⟩

namespace AllSurfacePreparation

/-- Read the actual ordered indexed exterior word of every retained surface component. -/
@[expose] def componentWords (components : List (ExteriorProgram.SurfaceComponent regular domains differential)) :
    List (List (Stokes.OrientedEdge lifted.vertices.count)) :=
  components.map (fun component => component.prepared.occurrences.map (fun item => item.placement.indexed))

/-- Flattening the retained component words gives exactly the original ordered surface-occurrence edge list. -/
private theorem componentWords_flatten (components : List (ExteriorProgram.SurfaceComponent regular domains
  differential)) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.componentWords components).flatten =
      (components.flatMap (fun component => component.prepared.occurrences)).map (fun item => item.placement.indexed) :=
        by
  induction components with
  | nil => rfl
  | cons head tail ih =>
      simp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.componentWords,
        List.map_cons, List.flatten_cons, Flatten.flatMap_cons, Map.map_append] at ih ⊢
      exact congrArg (List.append _) ih

/-- Every actual retained component word is a closed original lifted exterior path. -/
private theorem componentWords_closed (components : List (ExteriorProgram.SurfaceComponent regular domains
  differential)) :
    ∀ word ∈ Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.componentWords components, ∃
      anchor,
      PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor := by
  intro word member
  obtain ⟨component, _, equal⟩ := Map.mem_map.mp member
  rw [← equal, component.prepared.occurrences_eq]
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.indexed_closed component.program

namespace CapAttachment

/-- Embed an original retained surface vertex into the extended cap-attachment vertex set. -/
@[expose] def vertex {original components : Nat} (index : Fin original) : Fin (original + components) :=
  ⟨index.val, Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right original components)⟩

/-- Select the distinct new apex indexed by its actual original exterior component. -/
@[expose] def apex {original components : Nat} (index : Fin components) : Fin (original + components) :=
  ⟨original + index.val, Nat.add_lt_add_left index.isLt original⟩

/-- The inclusion of original retained surface vertices is injective. -/
theorem vertex_injective {original components : Nat} : Function.Injective
  (@Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex original
  components) := by
  intro first last equal
  have values := congrArg Fin.val equal
  exact Fin.ext values

/-- Distinct retained exterior component indices have distinct new apex vertices. -/
theorem apex_injective {original components : Nat} : Function.Injective
  (@Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.apex original
  components) := by
  intro first last equal
  have values := congrArg Fin.val equal
  apply Fin.ext
  change original + first.val = original + last.val at values
  exact Nat.Addition.add_left_cancel values

/-- Every original surface vertex is distinct from each newly attached cap apex. -/
theorem vertex_ne_apex {original components : Nat} (first : Fin original) (last : Fin components) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex (components :=
      components) first ≠
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.apex (original :=
      original) last := by
  intro equal
  have values := congrArg Fin.val equal
  change first.val = original + last.val at values
  exact (Nat.ne_of_lt (first.isLt.trans_le (Nat.le_add_right original last.val))) values

end CapAttachment

set_option genInjectivity false in
/-- Retain all generated faces and the proof-producing incidence result. No root trace, parent preparation, or numerical
cap request is repeated. -/
structure CapAttachment (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential) where
  /-- The cached actual original exterior component words. -/ words : List (List (Stokes.OrientedEdge
    lifted.vertices.count))
  /-- The cached words are exactly those read from the retained prepared surface components. -/ words_eq : words =
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.componentWords prepared.components
  /-- The cached oppositely oriented fan triangles on the actual retained component words. -/ caps : List
    (Stokes.OrientedTriangle (lifted.vertices.count + words.length))
  /-- The cap triangles are exactly the original fan construction with one retained new apex per component. -/ caps_eq :
    caps = BoundaryCaps.fans
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex words
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.apex
  /-- The cached original surface triangles followed by the actual attached fan triangles. -/ triangles : List
    (Stokes.OrientedTriangle (lifted.vertices.count + words.length))
  /-- The complete triangle cache is exactly the original face embedding followed by the retained caps. -/ triangles_eq
    : triangles = (List.ofFn lifted.mesh.triangulation.faces).map (OrientedTriangle.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex) ++ caps
  /-- The cached original physical branch-hole boundary edges in the extended vertex set. -/ holes : List
    (Stokes.OrientedEdge (lifted.vertices.count + words.length))
  /-- The hole cache is exactly the embedded flattening of the original retained branch-hole boundaries. -/ holes_eq :
    holes = ((base.faces.holes.map (fun hole => hole.liftedBoundary lifted.vertices lifted.edges)).flatten).map
    (OrientedEdge.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex)
  /-- The checked finite indexing of these exact retained surface and cap triangles. -/ indexed : BoundaryCaps.Indexed
    triangles

constructive_injectivity CapAttachment

namespace CapAttachment

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}

/-- Cache the actual exterior words, original faces, attached fans and retained hole boundaries with their finite
triangle indexing. -/
@[expose] def build (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared :=
  let words := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.componentWords
    prepared.components
  let caps := BoundaryCaps.fans
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex words
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.apex (original :=
    lifted.vertices.count))
  let triangles := (List.ofFn lifted.mesh.triangulation.faces).map (OrientedTriangle.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex) ++ caps
  let holes := ((base.faces.holes.map (fun hole => hole.liftedBoundary lifted.vertices lifted.edges)).flatten).map
    (OrientedEdge.map
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex (components :=
      words.length)))
  ⟨words, rfl, caps, rfl, triangles, rfl, holes, rfl, Indexed.build triangles⟩

/-- The cached component words flatten to exactly the original retained exterior boundary list. -/
theorem words_flatten (attached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared) :
  attached.words.flatten = lifted.exteriorBoundaries.flatten := by
  rw [attached.words_eq,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.componentWords_flatten, ←
    prepared.occurrences_eq]
  exact prepared.indexed_eq

/-- Every cached actual component word closes on an original surface vertex. -/
theorem words_closed (attached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared) : ∀ word ∈
  attached.words,
    ∃ anchor, PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor := by
  rw [attached.words_eq]
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.componentWords_closed
    prepared.components

/-- The area of flattened retained words equals the sum of their actual individual edge-list areas. -/
private theorem flatten_area (points : Fin count → Stokes.PrimitivePoint) (words : List (List (Stokes.OrientedEdge
  count))) :
    Stokes.edgeListArea points words.flatten = CellBoundary.sumValues (Stokes.edgeListArea points) words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      rw [List.flatten_cons, Stokes.edgeListArea_append, ih]
      rfl

/-- The actual attached fan area is the negative original two-sheet exterior area. -/
theorem caps_area (attached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
    (points : Fin (lifted.vertices.count + attached.words.length) → Stokes.PrimitivePoint) :
    BoundaryCaps.area points attached.caps =
      -lifted.edges.twoSheetArea lifted.vertices (fun index => points
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex index))
        base.bank.exterior := by
  rw [attached.caps_eq, BoundaryCaps.fans_area
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex points
    attached.words Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.apex
    attached.words_closed,
    attached.words_flatten,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.flatten_area,
      lifted.exteriorBoundaries_area]

/-- Cancellation of the fixed exterior in the actual surface face sum. The branch-hole contribution remains explicit. -/
theorem area_eq_holes (attached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
    (points : Fin (lifted.vertices.count + attached.words.length) → Stokes.PrimitivePoint) :
    BoundaryCaps.area points attached.triangles =
      CellBoundary.sumValues (fun hole => lifted.edges.twoSheetArea lifted.vertices (fun index => points
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex index))
        hole.inwardBoundary)
        base.faces.holes := by
  rw [attached.triangles_eq, BoundaryCaps.area_append, BoundaryCaps.area_map, attached.caps_area]
  have surface := lifted.wedge_eq_exterior_and_holes (fun index => points
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex index))
  rw [Stokes.triangleWedgeSum_eq_edgeListArea] at surface
  change BoundaryCaps.area (fun index => points
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex index))
    (List.ofFn lifted.mesh.triangulation.faces) = _ at surface
  rw [surface]
  ring1

/-- The boundary area of the actual attached triangulation equals the retained original branch-hole area. -/
theorem boundary_eq_holes (attached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
    (points : Fin (lifted.vertices.count + attached.words.length) → Stokes.PrimitivePoint) :
    Stokes.edgeListArea points attached.indexed.triangulation.boundary =
      CellBoundary.sumValues (fun hole => lifted.edges.twoSheetArea lifted.vertices (fun index => points
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex index))
        hole.inwardBoundary)
        base.faces.holes :=
  (attached.indexed.boundary_area points).trans (attached.area_eq_holes points)

/-- The cached embedded hole word reads exactly the original summed branch-hole area. -/
theorem holes_area (attached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
    (points : Fin (lifted.vertices.count + attached.words.length) → Stokes.PrimitivePoint) :
    Stokes.edgeListArea points attached.holes =
      CellBoundary.sumValues (fun hole => lifted.edges.twoSheetArea lifted.vertices (fun index => points
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.vertex index))
        hole.inwardBoundary)
        base.faces.holes := by
  rw [attached.holes_eq, BoundaryCaps.edgeArea_map,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.flatten_area,
    CellBoundary.sumValues_map]
  exact CellBoundary.sumValues_congr _ _ _ (fun hole _ => hole.liftedBoundary_area lifted.vertices lifted.edges _)

/-- Every oriented edge has exactly the signed multiplicity of the retained hole tours. This also cancels all new radial
edges, for arbitrary edge values. -/
theorem boundary_coefficients (attached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
    (selected : Stokes.OrientedEdge (lifted.vertices.count + attached.words.length)) :
    AreaChainTests.coefficient selected attached.indexed.triangulation.boundary =
      AreaChainTests.coefficient selected attached.holes :=
  AreaChainTests.coefficient_eq (fun points => (attached.boundary_eq_holes points).trans (attached.holes_area
    points).symm) selected

/-- Every antisymmetric valuation reads the same value on the actual attached boundary and retained original hole word.
-/
theorem boundary_chain (attached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
    (value : Stokes.OrientedEdge (lifted.vertices.count + attached.words.length) → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value attached.indexed.triangulation.boundary = SewingRetraction.wordValue value
      attached.holes :=
  AreaChainTests.wordValue_eq (fun points => (attached.boundary_eq_holes points).trans (attached.holes_area
    points).symm) value anti

end CapAttachment
end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
