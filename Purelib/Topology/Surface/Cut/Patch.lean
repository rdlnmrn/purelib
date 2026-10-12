module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
public import Purelib.Data.List.Map
public import Purelib.Data.List.Nodup
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

public import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Indexed cut patches with independent vertex occurrences

Original labels are a projection, not vertex equality.  Faces and seams are
materialized in the cut bank, where only selected seam endpoints are glued.
Exact finite Stokes therefore applies to arbitrary cut-vertex primitives,
including primitives with different values over the same original vertex.
-/

namespace Purelib.Topology.Surface.Cut.Patch

open Purelib

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Mesh.EdgeCancellation
open _root_.Purelib.Topology.Mesh renaming EdgeCancellation -> EdgeCancellation

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge OrientedTriangle PrimitivePoint edgeListArea
  edgeListArea_append edgeListArea_reordering pairedEdgeOccurrences pairedEdgeOccurrences_area_zero)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit sew_ordering sew_closed)
open Purelib.Topology.Surface.Sewing.VertexSewing (pairedEdgeOccurrences_map)
open Purelib.Topology.Surface.Sewing.SewingProjection (pathEndpoints_map edgeList_map_comp triangleList_map_comp
  triangleBoundaries_map nonloop_map edgeStarts_map)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

set_option genInjectivity false in
/-- A finite cut-vertex realization of specified original faces and boundary.

The retained triangles, boundary and seams carry exact projection and incidence certificates; the cut boundary is a
simple closed nonloop path. -/
structure CutPatch {vertexCount faceCount : Nat} (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount)
    (indices : List (Fin faceCount)) (originalBoundary : List (Stokes.OrientedEdge vertexCount)) where
  /-- Number of slots in the retained cut-vertex bank. -/ count : Nat
  /-- Original surface-vertex label of each retained cut vertex. -/ vertexLabels : Data.Vector (Fin
    vertexCount) count
  /-- Ordered triangles on the retained cut-vertex bank. -/ triangles : List (Stokes.OrientedTriangle count)
  /-- Projecting the retained triangles recovers the specified original face occurrences. -/ triangles_eq :
    triangles.map (OrientedTriangle.map vertexLabels) = indices.map faces
  /-- Ordered exposed boundary on the retained cut vertices. -/ boundary : List (Stokes.OrientedEdge count)
  /-- Projecting the retained boundary recovers the specified original boundary list. -/ boundary_eq : boundary.map
    (OrientedEdge.map vertexLabels) = originalBoundary
  /-- Retained cut edges whose opposite occurrences account for internal sewing. -/ seams : List (Stokes.OrientedEdge
    count)
  /-- Triangle-edge occurrences reorder into the boundary and both orientations of every seam. -/ incidence :
    Stokes.EdgeReordering (triangles.flatMap OrientedTriangle.boundary) (boundary ++ Stokes.pairedEdgeOccurrences seams)
  /-- Retained cut vertex anchoring the closed boundary path. -/ anchor : Fin count
  /-- The original cut boundary starts and finishes at the retained anchor. -/ closed : PathBoundary.PathEndpoints
    OrientedEdge.start OrientedEdge.finish boundary anchor anchor
  /-- Every retained boundary edge has distinct cut endpoints. -/ nonloop : ∀ edge ∈ boundary, edge.start ≠ edge.finish
  /-- Boundary edge starts are distinct in the retained cut-vertex bank. -/ simple : (boundary.map
    OrientedEdge.start).Nodup

constructive_injectivity CutPatch

namespace CutPatch

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

open Purelib.Topology.Surface.Cut in
/-- Build the three-vertex cut realization of one original triangle with its complete boundary.

The three original coordinate labels occupy three distinct cut slots. Its same ordered triangle and complete boundary
retain exact projection, incidence and closed-path certificates independently of coincident original labels. -/
@[expose] def triangle (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (index : Fin faceCount) :
    CutPatch faces [index] (faces index).boundary :=
  { count := 3
    vertexLabels := .cons (faces index).first (.cons (faces index).second (.cons (faces index).third .nil))
    triangles := [⟨0, 1, 2⟩]
    triangles_eq := rfl
    boundary := (⟨0, 1, 2⟩ : Stokes.OrientedTriangle 3).boundary
    boundary_eq := rfl
    seams := []
    incidence := EdgeReordering.refl _
    anchor := 0
    closed := .cons (.cons (.cons (.nil _)))
    nonloop := by
      intro edge member
      rcases Membership.mem_cons.mp member with equal | member
      · cases equal; decide
      · rcases Membership.mem_cons.mp member with equal | member
        · cases equal; decide
        · rcases Membership.mem_cons.mp member with equal | member
          · cases equal; decide
          · exact (List.not_mem_nil member).elim
    simple := by decide }

/-- Flattening paired edge occurrences commutes with concatenation of seam lists. -/
private theorem paired_append {count : Nat} (left right : List (Stokes.OrientedEdge count)) :
    Stokes.pairedEdgeOccurrences (left ++ right) = Stokes.pairedEdgeOccurrences left ++ Stokes.pairedEdgeOccurrences
      right := by
  induction left with
  | nil => rfl
  | cons edge tail ih => exact congrArg (List.cons edge) (congrArg (List.cons edge.reverse) ih)

open Purelib.Topology.Surface.Cut.Patch in
/-- Combine the two original incidence certificates across the selected opposite seam edges.

The two original triangle-edge reorderings and the selected opposite boundary occurrences supply the new incidence
certificate. Their same ordered rest boundaries and seam lists retain every internal occurrence and both orientations of
the selected seam. -/
private theorem sew_incidence {count : Nat} {firstFaces secondFaces firstBoundary secondBoundary firstSeams secondSeams
  : List (Stokes.OrientedEdge count)}
    (first : Stokes.EdgeReordering firstFaces (firstBoundary ++ Stokes.pairedEdgeOccurrences firstSeams))
    (second : Stokes.EdgeReordering secondFaces (secondBoundary ++ Stokes.pairedEdgeOccurrences secondSeams))
    (firstSplit : PolygonStokes.BoundarySplit firstBoundary) (secondSplit : PolygonStokes.BoundarySplit secondBoundary)
    (opposite : secondSplit.edge = firstSplit.edge.reverse) :
    Stokes.EdgeReordering (firstFaces ++ secondFaces)
      ((firstSplit.rest ++ secondSplit.rest) ++ Stokes.pairedEdgeOccurrences (firstSplit.edge :: (firstSeams ++
        secondSeams))) := by
  have assembled := (EdgeReordering.append_right first secondFaces).trans (EdgeReordering.append_left (firstBoundary ++
    Stokes.pairedEdgeOccurrences firstSeams) second)
  have interleaved : Stokes.EdgeReordering
      ((firstBoundary ++ Stokes.pairedEdgeOccurrences firstSeams) ++ (secondBoundary ++ Stokes.pairedEdgeOccurrences
        secondSeams))
      ((firstBoundary ++ secondBoundary) ++ (Stokes.pairedEdgeOccurrences firstSeams ++ Stokes.pairedEdgeOccurrences
        secondSeams)) := by
    simpa only [Append.append_assoc] using EdgeReordering.append_left firstBoundary
      (EdgeReordering.append_swap (Stokes.pairedEdgeOccurrences firstSeams) secondBoundary (Stokes.pairedEdgeOccurrences
        secondSeams))
  have sewn := (EdgeReordering.append_right (PolygonStokes.sew_ordering firstSplit secondSplit opposite)
    (Stokes.pairedEdgeOccurrences firstSeams ++ Stokes.pairedEdgeOccurrences secondSeams))
  simpa only [Stokes.pairedEdgeOccurrences, paired_append, Append.append_assoc, List.cons_append,
    List.nil_append]
    using assembled.trans (interleaved.trans sewn)

open Purelib.Topology.Surface.Cut in
set_option genInjectivity false in
/-- Cache the two actual cut occurrences once. Later primitive requests use these same endpoints without replaying a
boundary-prefix lookup.

The two original boundary splits remain indexed by their own retained patches. Each cached lift identifies the selected
cut occurrence and its exact original projected boundary occurrence. -/
structure Seam {firstIndices secondIndices : List (Fin faceCount)}
    {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
    (first : CutPatch faces firstIndices firstBoundary) (second : CutPatch faces secondIndices
      secondBoundary)
    (firstBase : PolygonStokes.BoundarySplit firstBoundary) (secondBase : PolygonStokes.BoundarySplit secondBoundary)
      where
  /-- Exact lift of the first selected original boundary occurrence. -/ firstLift : BoundarySplit.Lift
    first.vertexLabels firstBase first.boundary
  /-- Exact lift of the second selected original boundary occurrence. -/ secondLift : BoundarySplit.Lift
    second.vertexLabels secondBase second.boundary

constructive_injectivity Seam

section
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.Patch
/-- Lift the two selected original boundary occurrences into their respective retained cut boundaries.

Each original patch boundary equation transports the selected original occurrence into that retained cut boundary. Both
resulting lifts are cached once with their original patch and boundary-split indices. -/
@[expose] def Seam.build {firstIndices secondIndices : List (Fin faceCount)}
    {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
    (first : CutPatch faces firstIndices firstBoundary) (second : CutPatch faces secondIndices
      secondBoundary)
    (firstBase : PolygonStokes.BoundarySplit firstBoundary) (secondBase : PolygonStokes.BoundarySplit secondBoundary) :
    Seam first second firstBase secondBase :=
  ⟨BoundarySplit.lift first.vertexLabels firstBase first.boundary first.boundary_eq,
    BoundarySplit.lift second.vertexLabels secondBase second.boundary second.boundary_eq⟩

/-- Sewing uses cached occurrence lookup and the endpoint-only injections. A coincident surface label elsewhere cannot
identify any further cut vertices.

The two cached seam occurrences supply the exact endpoint-only injections and projected labels. The original triangle,
exposed-boundary and seam orders are retained; equal labels at other slots do not cause additional identifications. -/
@[expose] def sew {firstIndices secondIndices : List (Fin faceCount)} {firstBoundary secondBoundary : List
  (Stokes.OrientedEdge vertexCount)}
    (first : CutPatch faces firstIndices firstBoundary) (second : CutPatch faces secondIndices
      secondBoundary)
    (firstBase : PolygonStokes.BoundarySplit firstBoundary) (secondBase : PolygonStokes.BoundarySplit secondBoundary)
    (opposite : secondBase.edge = firstBase.edge.reverse) (seam : Seam first second firstBase secondBase) :
    CutPatch faces (firstIndices ++ secondIndices) (firstBase.rest ++ secondBase.rest) :=
  let firstLift := seam.firstLift
  let secondLift := seam.secondLift
  let firstSplit := firstLift.split
  let secondSplit := secondLift.split
  let firstDistinct := first.nonloop firstSplit.edge firstSplit.edge_mem
  let secondDistinct := second.nonloop secondSplit.edge secondSplit.edge_mem
  let left : Fin first.count → Fin (first.count + second.count) := EndpointGluing.left
  let right := EndpointGluing.right firstSplit.edge secondSplit.edge
  let labels := Data.Vector.Basic.vectorOfFn (EndpointGluing.project first.vertexLabels second.vertexLabels)
  have matched : OrientedEdge.map second.vertexLabels secondSplit.edge = (OrientedEdge.map first.vertexLabels
    firstSplit.edge).reverse :=
    secondLift.edge_eq.trans (opposite.trans (congrArg OrientedEdge.reverse firstLift.edge_eq.symm))
  have labelsLeft : ∀ index, labels (left index) = first.vertexLabels index := by
    intro index
    rw [Data.Vector.Basic.vectorOfFn_apply]
    exact EndpointGluing.project_left _ _ index
  have labelsRight : ∀ index, labels (right index) = second.vertexLabels index := by
    intro index
    rw [Data.Vector.Basic.vectorOfFn_apply]
    exact EndpointGluing.project_right _ _ _ _ matched index
  let leftSplit := BoundarySplit.map left firstSplit
  let rightSplit := BoundarySplit.map right secondSplit
  have cutOpposite : rightSplit.edge = leftSplit.edge.reverse := EndpointGluing.opposite _ _ secondDistinct
  { count := first.count + second.count
    vertexLabels := labels
    triangles := first.triangles.map (OrientedTriangle.map left) ++ second.triangles.map (OrientedTriangle.map right)
    triangles_eq := by
      rw [Map.map_append, SewingProjection.triangleList_map_comp left labels first.vertexLabels labelsLeft,
        SewingProjection.triangleList_map_comp right labels second.vertexLabels labelsRight, first.triangles_eq,
          second.triangles_eq, Map.map_append]
    boundary := leftSplit.rest ++ rightSplit.rest
    boundary_eq := by
      rw [Map.map_append, BoundarySplit.map_rest left firstSplit, BoundarySplit.map_rest right secondSplit,
        SewingProjection.edgeList_map_comp left labels first.vertexLabels labelsLeft,
        SewingProjection.edgeList_map_comp right labels second.vertexLabels labelsRight, firstLift.rest_eq,
          secondLift.rest_eq]
    seams := leftSplit.edge :: (first.seams.map (OrientedEdge.map left) ++ second.seams.map (OrientedEdge.map right))
    incidence := by
      rw [Flatten.flatMap_append, SewingProjection.triangleBoundaries_map, SewingProjection.triangleBoundaries_map]
      apply sew_incidence (firstSplit := leftSplit) (secondSplit := rightSplit) (opposite := cutOpposite)
      · simpa only [Map.map_append, VertexSewing.pairedEdgeOccurrences_map] using EdgeReordering.map left
          first.incidence
      · simpa only [Map.map_append, VertexSewing.pairedEdgeOccurrences_map] using EdgeReordering.map right
          second.incidence
    anchor := leftSplit.edge.finish
    closed := PolygonStokes.sew_closed leftSplit rightSplit cutOpposite (SewingProjection.pathEndpoints_map left
      first.closed) (SewingProjection.pathEndpoints_map right second.closed)
    nonloop := by
      intro edge member
      rcases Membership.mem_append.mp member with onLeft | onRight
      · rw [BoundarySplit.map_rest left firstSplit] at onLeft
        exact SewingProjection.nonloop_map left EndpointGluing.left_injective
          (fun original member => first.nonloop original (BoundarySplit.rest_mem firstSplit member)) edge onLeft
      · rw [BoundarySplit.map_rest right secondSplit] at onRight
        exact SewingProjection.nonloop_map right (EndpointGluing.right_injective _ _ firstDistinct secondDistinct)
          (fun original member => second.nonloop original (BoundarySplit.rest_mem secondSplit member)) edge onRight
    simple := by
      rw [Map.map_append, BoundarySplit.map_rest left firstSplit, BoundarySplit.map_rest right secondSplit,
        SewingProjection.edgeStarts_map, SewingProjection.edgeStarts_map]
      have firstSimple := BoundarySplit.rest_simple firstSplit first.simple
      have secondSimple := BoundarySplit.rest_simple secondSplit second.simple
      apply Nodup.nodup_append
        (Data.List.Nodup.nodup_map_of_injective EndpointGluing.left_injective firstSimple.1)
        (Data.List.Nodup.nodup_map_of_injective (EndpointGluing.right_injective _ _ firstDistinct secondDistinct)
          secondSimple.1)
      intro leftVertex leftMember rightVertex rightMember equal
      rcases Map.mem_map.mp leftMember with ⟨i, iMember, iEqual⟩
      rcases Map.mem_map.mp rightMember with ⟨j, jMember, jEqual⟩
      rcases Map.mem_map.mp iMember with ⟨leftEdge, leftEdgeMember, leftEdgeEqual⟩
      rcases Map.mem_map.mp jMember with ⟨rightEdge, rightEdgeMember, rightEdgeEqual⟩
      have crossed : left i = right j := iEqual.trans (equal.trans jEqual.symm)
      rcases (EndpointGluing.left_eq_right_iff _ _ secondDistinct i j).mp crossed with matchedStart | matchedFinish
      · exact secondSimple.2 rightEdge rightEdgeMember (rightEdgeEqual.trans matchedStart.2)
      · exact firstSimple.2 leftEdge leftEdgeMember (leftEdgeEqual.trans matchedFinish.1) }

end

open Purelib.Topology.Surface.Cut in
open Purelib.Topology.Surface.Cut.Patch in
set_option genInjectivity false in
/-- Executable evidence of the actual cut-vertex assembly, not only of its projected boundary word. Every join retains
the already selected seam.

Every leaf retains the original single-triangle patch, and every join retains both original assembled inputs with the
same cached seam. Its dependent patch index records the exact constructed cut vertices and boundary order. -/
inductive Assembly (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) :
    {indices : List (Fin faceCount)} → {boundary : List (Stokes.OrientedEdge vertexCount)} →
      CutPatch faces indices boundary → Type where
  /-- Start an assembly with the canonical cut realization of one original triangle. -/ | triangle (index : Fin
    faceCount) : Assembly faces (CutPatch.triangle faces index)
  /-- Extend an assembly by sewing the two retained patches along their certified selected seam. -/ | sew {firstIndices
    secondIndices : List (Fin faceCount)}
      {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
      {first : CutPatch faces firstIndices firstBoundary} {second : CutPatch faces secondIndices
        secondBoundary}
      (left : Assembly faces first) (right :
        Assembly faces second)
      (firstBase : PolygonStokes.BoundarySplit firstBoundary) (secondBase : PolygonStokes.BoundarySplit secondBoundary)
      (opposite : secondBase.edge = firstBase.edge.reverse) (seam : Seam first second firstBase secondBase) :
      Assembly faces (first.sew second firstBase secondBase opposite seam)

constructive_injectivity Assembly

open Purelib.Topology.Surface.Cut
/-- The cut triangle list has exactly as many entries as the original face-index list.

The retained triangle projection equals the selected original face-index list. Mapping preserves both displayed list
lengths, so the exact cache has the original selected face count. -/
theorem triangles_length {indices : List (Fin faceCount)} {originalBoundary : List (Stokes.OrientedEdge vertexCount)}
    (patch : CutPatch faces indices originalBoundary) : patch.triangles.length = indices.length := by
  have equal := congrArg List.length patch.triangles_eq
  simpa only [Map.length_map] using equal

/-- Projection preserves the length of the retained cut boundary.

The retained boundary projection equals the specified original boundary list. Mapping preserves the displayed length
without identifying different cut vertices carrying the same original label. -/
theorem boundary_length {indices : List (Fin faceCount)} {originalBoundary : List (Stokes.OrientedEdge vertexCount)}
    (patch : CutPatch faces indices originalBoundary) : patch.boundary.length = originalBoundary.length := by
  have equal := congrArg List.length patch.boundary_eq
  simpa only [Map.length_map] using equal

/-- Unlike a primitive on original vertices, this assignment may distinguish different occurrences of one surface
vertex. Only actual sewn seams cancel. -/
theorem boundary_area {indices : List (Fin faceCount)} {originalBoundary : List (Stokes.OrientedEdge vertexCount)}
    (patch : CutPatch faces indices originalBoundary) (primitive : Fin patch.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive patch.boundary = Stokes.edgeListArea primitive (patch.triangles.flatMap
      OrientedTriangle.boundary) := by
  rw [Stokes.edgeListArea_reordering primitive patch.incidence, Stokes.edgeListArea_append,
    Stokes.pairedEdgeOccurrences_area_zero]
  ring1

end CutPatch

end Purelib.Topology.Surface.Cut.Patch
