module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PolygonSewing
public import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Surface.Sewing.VertexSewing
import Batteries.Logic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Checked trees of ordered triangle sewings

The tree and every boundary/seam list are retained finite data.  Its checked
history identifies exactly which cyclic occurrences were sewn.  A tree with
n triangle leaves has n-1 seams and n+2 remaining boundary occurrences; no
additional coincident endpoints or reverse edges are silently glued.
-/

namespace Purelib.Topology.Surface.Sewing

open Purelib.Topology.Chain

open Purelib.Topology.Mesh.EdgeCancellation
open _root_.Purelib.Topology.Mesh renaming EdgeCancellation -> EdgeCancellation

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Cut.Patch.CutPatch

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes

open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge OrientedTriangle PrimitivePoint edgeListArea
  edgeListArea_append edgeListArea_reordering pairedEdgeOccurrences pairedEdgeOccurrences_area_zero)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit sew_ordering sew_closed)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)

set_option genInjectivity false in
/-- A finite schedule of original triangle leaves and specified boundary-position joins.

The schedule is data awaiting checked replay; each join retains both child trees and the exact requested occurrence
positions. -/
inductive SewingTree (faceCount : Nat) where
  /-- Retain one original bounded face index as a triangle leaf. -/ | leaf (index : Fin faceCount)
  /-- Retain two original child schedules and their exact requested boundary positions. -/ | join (first second :
    SewingTree faceCount) (firstPosition secondPosition : Nat)

constructive_injectivity SewingTree

namespace SewingTree

/-- Read the original face indices in retained tree order. -/
@[expose] def leaves {faceCount : Nat} : SewingTree faceCount → List (Fin faceCount)
  | .leaf index => [index]
  | .join first second _ _ => first.leaves ++ second.leaves

/-- Every retained sewing tree has at least one original face leaf.

Every leaf contributes one face occurrence. A join concatenates both original
nonempty leaf lists, retaining all their occurrences. -/
theorem leaves_nonempty {faceCount : Nat} : (tree : SewingTree faceCount) → 0 < tree.leaves.length
  | .leaf _ => Nat.zero_lt_succ 0
  | .join first second _ _ => by
      have positive := first.leaves_nonempty
      simp only [SewingTree.leaves, Append.length_append]
      omega

end SewingTree

namespace SewingTree

/-- Checked original boundary and seam lists for a specified sewing tree.

Each join records the exact two original selected occurrences and their opposite orientation. -/
inductive SewingHistory {vertexCount faceCount : Nat} (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) :
    SewingTree faceCount → List (Stokes.OrientedEdge vertexCount) → List (Stokes.OrientedEdge vertexCount) →
      Prop
  /-- Certify the literal boundary of one original face with no seams. -/ | leaf (index : Fin faceCount) :
    SewingHistory faces (.leaf index) (faces index).boundary []
  /-- Certify the selected opposite seam join of two original checked histories. -/ | join {firstTree secondTree
    firstBoundary secondBoundary firstSeams secondSeams}
      (first : SewingHistory faces firstTree firstBoundary firstSeams)
      (second : SewingHistory faces secondTree secondBoundary secondSeams)
      (firstSplit : PolygonStokes.BoundarySplit firstBoundary) (secondSplit : PolygonStokes.BoundarySplit
        secondBoundary)
      (opposite : secondSplit.edge = firstSplit.edge.reverse) :
      SewingHistory faces (.join firstTree secondTree
        firstSplit.before.length secondSplit.before.length)
        (firstSplit.rest ++ secondSplit.rest) (firstSplit.edge :: (firstSeams ++ secondSeams))

end SewingTree

namespace SewingTree.SewingHistory

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {tree : SewingTree faceCount} {boundary seams : List (Stokes.OrientedEdge
    vertexCount)}

/-- The original retained boundary has two more edges than the tree has face leaves.

Each checked join removes exactly its two selected occurrences. The original
child history lengths and retained split lengths supply the count equation. -/
theorem boundary_length (history : SewingHistory faces tree boundary seams) : boundary.length =
  tree.leaves.length + 2 := by
  induction history with
  | leaf => rfl
  | join first second firstSplit secondSplit opposite ihFirst ihSecond =>
      have firstLength := firstSplit.rest_length
      have secondLength := secondSplit.rest_length
      simp only [leaves, Append.length_append]
      omega

/-- The retained seam count is one less than the original tree's face count.

Every join retains one new seam together with both original child seam lists.
Their checked counts sum to the length of the same ordered face-leaf list. -/
theorem seams_length (history : SewingHistory faces tree boundary seams) : seams.length + 1 =
  tree.leaves.length := by
  induction history with
  | leaf => rfl
  | join first second firstSplit secondSplit opposite ihFirst ihSecond =>
      simp only [List.length_cons, Append.length_append, leaves]
      omega

/-- Expanding both orientations of original seam lists preserves concatenation. -/
private theorem paired_append {count : Nat} (left right : List (Stokes.OrientedEdge count)) :
    Stokes.pairedEdgeOccurrences (left ++ right) = Stokes.pairedEdgeOccurrences left ++ Stokes.pairedEdgeOccurrences
      right := by
  induction left with
  | nil => rfl
  | cons edge tail ih => exact congrArg (List.cons edge) (congrArg (List.cons edge.reverse) ih)

/-- Original leaf-face incidences reorder into the retained boundary and both orientations of every seam.

Each checked join reorders the same original child boundary lists. Its selected
opposite occurrences remain in the paired seam bank, preserving each incidence. -/
theorem incidence (history : SewingHistory faces tree boundary seams) :
    Stokes.EdgeReordering (tree.leaves.flatMap fun index => (faces index).boundary) (boundary ++
      Stokes.pairedEdgeOccurrences seams) := by
  induction history with
  | leaf index =>
      change EdgeReordering ((faces index).boundary ++ [])
        ((faces index).boundary ++ [])
      exact EdgeReordering.refl _
  | @join firstTree secondTree firstBoundary secondBoundary firstSeams secondSeams first second firstSplit secondSplit
    opposite ihFirst ihSecond =>
      have assembled := (EdgeReordering.append_right ihFirst (secondTree.leaves.flatMap fun index => (faces
        index).boundary)).trans
        (EdgeReordering.append_left (firstBoundary ++ Stokes.pairedEdgeOccurrences firstSeams) ihSecond)
      have interleaved : Stokes.EdgeReordering
          ((firstBoundary ++ Stokes.pairedEdgeOccurrences firstSeams) ++ (secondBoundary ++ Stokes.pairedEdgeOccurrences
            secondSeams))
          ((firstBoundary ++ secondBoundary) ++ (Stokes.pairedEdgeOccurrences firstSeams ++ Stokes.pairedEdgeOccurrences
            secondSeams)) := by
        simpa only [Append.append_assoc] using EdgeReordering.append_left firstBoundary
          (EdgeReordering.append_swap (Stokes.pairedEdgeOccurrences firstSeams) secondBoundary
            (Stokes.pairedEdgeOccurrences secondSeams))
      have sewn := EdgeReordering.append_right (PolygonStokes.sew_ordering firstSplit secondSplit opposite)
        (Stokes.pairedEdgeOccurrences firstSeams ++ Stokes.pairedEdgeOccurrences secondSeams)
      simpa only [leaves, Flatten.flatMap_append, Stokes.pairedEdgeOccurrences,
        paired_append,
        Append.append_assoc, List.cons_append, List.nil_append] using assembled.trans (interleaved.trans sewn)

end SewingTree.SewingHistory

namespace SewingTree

set_option genInjectivity false in
/-- A materialized cut patch with both its original surface labels and its separate cut-vertex bank. Primitive values on
`cut` need not descend through the projection to the original surface. -/
structure SewnPatch {vertexCount faceCount : Nat} (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) where
  /-- Original retained schedule of face leaves and specified occurrence joins. -/ tree : SewingTree
    faceCount
  /-- Cached original face occurrences in tree order. -/ faceIndices : List (Fin faceCount)
  /-- The face-index cache is exactly the retained tree's leaf list. -/ faceIndices_eq : faceIndices = tree.leaves
  /-- Cached original surface-labelled boundary after the specified joins. -/ boundary : List (Stokes.OrientedEdge
    vertexCount)
  /-- Cached original seam edges selected by the joins. -/ seams : List (Stokes.OrientedEdge vertexCount)
  /-- Checked provenance of the exact retained tree, boundary and seam list. -/ history : SewingHistory faces
    tree boundary seams
  /-- Original surface vertex anchoring the retained boundary path. -/ anchor : Fin vertexCount
  /-- The retained original boundary starts and finishes at its anchor. -/ closed : PathBoundary.PathEndpoints
    OrientedEdge.start OrientedEdge.finish boundary anchor anchor
  /-- Cached cut-vertex realization retaining the original face and boundary projections. -/ cut : Patch.CutPatch faces
    faceIndices boundary
  /-- Checked construction history of that exact original cut patch. -/ assembly : CutPatch.Assembly faces cut

constructive_injectivity SewnPatch

end SewingTree

namespace SewingTree.SewnPatch

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

/-- Materialize one original face as a checked triangle patch and cut assembly. -/
@[expose] def triangle (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (index : Fin faceCount) :
  SewnPatch faces :=
  ⟨.leaf index, [index], rfl, (faces index).boundary, [], .leaf index, (faces index).first,
    .cons (.cons (.cons (.nil _))), CutPatch.triangle faces index, .triangle index⟩

/-- Materialize the exact selected seam join of the two retained original patches.

The result caches the new tree, boundary, seam list and cut assembly while preserving every unglued occurrence. -/
@[expose] def sew (first second : SewnPatch faces) (firstSplit : PolygonStokes.BoundarySplit first.boundary)
  (secondSplit : PolygonStokes.BoundarySplit second.boundary)
    (opposite : secondSplit.edge = firstSplit.edge.reverse) : SewnPatch faces :=
  let seam := Seam.build first.cut second.cut firstSplit secondSplit
  { tree := .join first.tree second.tree firstSplit.before.length secondSplit.before.length
    faceIndices := first.faceIndices ++ second.faceIndices
    faceIndices_eq := congrArg₂ List.append first.faceIndices_eq second.faceIndices_eq
    boundary := firstSplit.rest ++ secondSplit.rest
    seams := firstSplit.edge :: (first.seams ++ second.seams)
    history := .join first.history second.history firstSplit secondSplit opposite
    anchor := firstSplit.edge.finish
    closed := PolygonStokes.sew_closed firstSplit secondSplit opposite first.closed second.closed
    cut := first.cut.sew second.cut firstSplit secondSplit opposite seam
    assembly := .sew first.assembly second.assembly firstSplit secondSplit opposite seam }

/-- The retained patch boundary has two more edges than its original face-index list. -/
theorem boundary_length (patch : SewnPatch faces) : patch.boundary.length = patch.faceIndices.length + 2 :=
  by
  rw [patch.faceIndices_eq]
  exact patch.history.boundary_length

/-- The retained patch has one fewer seam than original face occurrences. -/
theorem seams_length (patch : SewnPatch faces) : patch.seams.length + 1 = patch.faceIndices.length := by
  rw [patch.faceIndices_eq]
  exact patch.history.seams_length

/-- The complete original face-edge list reorders into the retained boundary and paired seams. -/
theorem incidence (patch : SewnPatch faces) :
    Stokes.EdgeReordering (patch.faceIndices.flatMap fun index => (faces index).boundary) (patch.boundary ++
      Stokes.pairedEdgeOccurrences patch.seams) := by
  rw [patch.faceIndices_eq]
  exact patch.history.incidence

/-- Every original surface primitive reads the same area on the retained boundary and included face incidences. -/
theorem boundary_area (patch : SewnPatch faces) (primitive : Fin vertexCount → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive patch.boundary = Stokes.edgeListArea primitive (patch.faceIndices.flatMap fun index =>
      (faces index).boundary) := by
  rw [Stokes.edgeListArea_reordering primitive patch.incidence, Stokes.edgeListArea_append,
    Stokes.pairedEdgeOccurrences_area_zero]
  ring1

set_option genInjectivity false in
/-- Replay retains its materialized patch and identifies the exact supplied tree, including every requested boundary
position. -/
structure Replayed (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (tree : SewingTree
  faceCount) where
  /-- Cached checked patch produced from the supplied original tree. -/ patch : SewnPatch faces
  /-- The cached patch retains exactly the requested original schedule. -/ tree_eq : patch.tree = tree

constructive_injectivity Replayed

set_option genInjectivity false in
/-- Invalidity concerns the requested seam, not every possible sewing of the two patches. Successful position scans are
retained for orientation errors. -/
inductive InvalidSeam (first second : SewnPatch faces) (firstPosition secondPosition : Nat) where
  /-- Certify that the requested first occurrence position is out of bounds. -/ | firstPosition (invalid :
    BoundarySplit.InvalidPosition first.boundary firstPosition)
  /-- Retain the checked first selection and certify the invalid second position. -/ | secondPosition (firstAt :
    BoundarySplit.Positioned first.boundary firstPosition)
      (invalid : BoundarySplit.InvalidPosition second.boundary secondPosition)
  /-- Retain both original selected occurrences and prove that they are not opposite. -/ | orientation (firstAt :
    BoundarySplit.Positioned first.boundary firstPosition)
      (secondAt : BoundarySplit.Positioned second.boundary secondPosition)
      (notOpposite : secondAt.split.edge ≠ firstAt.split.edge.reverse)

constructive_injectivity InvalidSeam

/-- Check just the specified seam, returning a proof of its precise failure or the exact requested join. No repair or
second position scan is performed. -/
@[expose] def checkSew (first second : SewnPatch faces) (firstPosition secondPosition : Nat) :
    Except (InvalidSeam first second firstPosition secondPosition)
      (Replayed faces (.join first.tree second.tree firstPosition secondPosition)) :=
  match BoundarySplit.checkAt first.boundary firstPosition with
  | .error invalid => .error (.firstPosition invalid)
  | .ok firstAt =>
      match BoundarySplit.checkAt second.boundary secondPosition with
      | .error invalid => .error (.secondPosition firstAt invalid)
      | .ok secondAt =>
          if opposite : secondAt.split.edge = firstAt.split.edge.reverse then
            .ok ⟨sew first second firstAt.split secondAt.split opposite, by
              change join first.tree second.tree
                firstAt.split.before.length secondAt.split.before.length = _
              rw [firstAt.position_eq, secondAt.position_eq]⟩
          else .error (.orientation firstAt secondAt opposite)

set_option genInjectivity false in
/-- A failed node, with its path through the original tree and the cached successful children needed to justify its
local seam failure. -/
inductive InvalidReplay (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) : SewingTree faceCount
  → Type where
  /-- Locate failure in the original first child schedule. -/ | first {first second : SewingTree faceCount}
    (firstPosition secondPosition : Nat)
      (invalid : InvalidReplay faces first) :
        InvalidReplay faces (.join first second firstPosition
        secondPosition)
  /-- Retain the checked first child and locate failure in the original second child. -/ | second {first second :
    SewingTree faceCount} (firstPosition secondPosition : Nat)
      (checkedFirst : Replayed faces first) (invalid :
        InvalidReplay faces second) :
      InvalidReplay faces (.join first second firstPosition
        secondPosition)
  /-- Retain both checked children and the precise failure of their requested original seam. -/ | seam {first second :
    SewingTree faceCount} (firstPosition secondPosition : Nat)
      (checkedFirst : Replayed faces first) (checkedSecond : Replayed faces second)
      (invalid : InvalidSeam checkedFirst.patch checkedSecond.patch firstPosition secondPosition) :
      InvalidReplay faces (.join first second firstPosition
        secondPosition)

constructive_injectivity InvalidReplay

namespace InvalidReplay

/-- Zero selects the first child, one the second; the empty path locates a failed seam at the current node. This reads
the retained report only. -/
@[expose] def nodePath {tree : SewingTree faceCount} : InvalidReplay faces tree →
  List Nat
  | .first _ _ invalid => 0 :: invalid.nodePath
  | .second _ _ _ invalid => 1 :: invalid.nodePath
  | .seam .. => []

end InvalidReplay

/-- An external script supplies only the tree and its integer positions. Every branch returns evidence about that
supplied tree, never an unexplained failure or a global impossibility claim about the underlying surface. -/
@[expose] def replay (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) : (tree : SewingTree
  faceCount) →
    Except (InvalidReplay faces tree) (Replayed faces tree)
  | .leaf index => .ok ⟨triangle faces index, rfl⟩
  | .join first second firstPosition secondPosition =>
      match replay faces first with
      | .error invalid => .error (.first firstPosition secondPosition invalid)
      | .ok checkedFirst =>
          match replay faces second with
          | .error invalid => .error (.second firstPosition secondPosition checkedFirst invalid)
          | .ok checkedSecond =>
              match checkSew checkedFirst.patch checkedSecond.patch firstPosition secondPosition with
              | .error invalid => .error (.seam firstPosition secondPosition checkedFirst checkedSecond invalid)
              | .ok checked => .ok ⟨checked.patch, checked.tree_eq.trans
                  (congrArg₂ (fun left right => join left right
                    firstPosition secondPosition)
                    checkedFirst.tree_eq checkedSecond.tree_eq)⟩

end SewingTree.SewnPatch

end Purelib.Topology.Surface.Sewing
