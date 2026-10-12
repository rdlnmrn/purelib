module
meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingForest

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-!
# Finite walks between adjacent oriented triangles

A step retains the actual shared edge and its two opposite occurrences.
These are walks of faces, not paths between vertices.  Their executable
finite witnesses are the connectivity data needed by the cut-polygon proof.
-/

namespace Purelib.Topology.Mesh.DualWalks

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

set_option genInjectivity false in
/-- A finite walk between triangle indices using actual shared oriented edges.

Every step retains an edge in the first face boundary and its reversal in the next, together with the remaining walk. -/
inductive DualWalk {vertexCount faceCount : Nat} (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) :
    Fin faceCount → Fin faceCount → Type
  /-- The empty walk at a retained face index. -/ | nil (index : Fin faceCount) :
    Purelib.Topology.Mesh.DualWalks.DualWalk faces index index
  /-- Prepend one shared-edge step with its two boundary occurrence proofs. -/ | cons {first next last : Fin faceCount}
    (edge : Stokes.OrientedEdge vertexCount)
      (firstMember : edge ∈ (faces first).boundary) (nextMember : edge.reverse ∈ (faces next).boundary)
      (tail : Purelib.Topology.Mesh.DualWalks.DualWalk faces next last) : Purelib.Topology.Mesh.DualWalks.DualWalk faces
        first last

constructive_injectivity DualWalk

namespace DualWalk

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

open Purelib.Topology.Mesh
/-- Concatenate dual face walks at their common retained endpoint. -/
def append : {first middle last : Fin faceCount} → DualWalks.DualWalk faces first middle → DualWalks.DualWalk faces
  middle last → DualWalks.DualWalk faces first last
  | _, _, _, .nil _, second => second
  | _, _, _, .cons edge firstMember nextMember tail, second => .cons edge firstMember nextMember (tail.append second)

/-- Reverse a finite dual walk and both orientations of every shared-edge step. -/
def reverse : {first last : Fin faceCount} → DualWalks.DualWalk faces first last → DualWalks.DualWalk faces last first
  | _, _, .nil index => .nil index
  | _, _, .cons edge firstMember nextMember tail =>
      tail.reverse.append (.cons edge.reverse nextMember (by rw [OrientedEdge.reverse_reverse]; exact firstMember) (.nil
        _))

/-- List the visited face indices, including both endpoints. -/
def faceIndices : {first last : Fin faceCount} → DualWalks.DualWalk faces first last → List (Fin faceCount)
  | _, last, .nil _ => [last]
  | first, _, .cons _ _ _ tail => first :: tail.faceIndices

/-- A finite face walk preserves any predicate closed under actual shared edge steps. No decidable equality of
proof-bearing faces is needed. -/
theorem preserves (predicate : Fin faceCount → Prop)
    (step : ∀ {first next}, ∀ edge ∈ (faces first).boundary, edge.reverse ∈ (faces next).boundary → predicate first →
      predicate next) :
    {first last : Fin faceCount} → DualWalks.DualWalk faces first last → predicate first → predicate last
  | _, _, .nil _, initial => initial
  | _, _, .cons edge firstMember nextMember tail, initial =>
      tail.preserves predicate step (step edge firstMember nextMember initial)

end DualWalk

open Purelib.Topology.Mesh in
set_option genInjectivity false in
/-- One retained root and finite root-to-face walks suffice; arbitrary face-to-face walks concatenate a reversed root
walk with another root walk. -/
structure DualConnection {vertexCount faceCount : Nat} (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount)
  where
  /-- The retained base face for the connected face bank. -/ root : Fin faceCount
  /-- A retained dual walk from the base face to every face index. -/ paths : (index : Fin faceCount) →
    DualWalks.DualWalk faces root index

constructive_injectivity DualConnection

open Purelib.Topology.Mesh in
/-- Connect two face indices through the retained common root.

Reverse the first root walk and append the second root walk, reusing their actual edge witnesses. -/
def DualConnection.connect {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
    (connection : DualWalks.DualConnection faces) (first last : Fin faceCount) : DualWalks.DualWalk faces first last :=
  (connection.paths first).reverse.append (connection.paths last)

end Purelib.Topology.Mesh.DualWalks
