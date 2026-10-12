module

public import Purelib.Topology.Surface.Sewing.PolygonSewing
public import Purelib.Topology.Surface.Word.Selection
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Word.Vertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Data.Vector.Basic
import Purelib.Data.List.Membership

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Word

public section

/-! Changing the cyclic start preserves the exact finite vertex presentation. -/

namespace Purelib.Topology.Surface.Word.VertexRotation

open Purelib.Data.List

open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.Selection (WordRotation)
open Purelib.Topology.Surface.Word.Vertices (WordVertexRealization WordVertexModel)

open Purelib.Topology.Surface.Word.Vertices

open Purelib.Topology.Surface.Word.Vertices.WordVertexPath (endpoint Path)

variable {count size : Nat} {source target : List (SignedWord.SignedGenerator count)}

namespace WordRotation

/-- Reverse a retained cyclic rotation by exchanging its two original segments. -/
@[expose] def symm (rotation : Selection.WordRotation source target) : Selection.WordRotation target source :=
  ⟨rotation.last, rotation.first, rotation.target_eq, rotation.source_eq⟩

/-- Cyclic rotation preserves membership of every original signed letter.

Exchanging the two retained segments changes their order while preserving each signed-letter occurrence. -/
theorem mem_iff (rotation : Selection.WordRotation source target) (letter : SignedWord.SignedGenerator count) :
    letter ∈ target ↔ letter ∈ source := by
  rcases rotation with ⟨first, last, rfl, rfl⟩
  constructor <;> intro member
  · rcases Membership.mem_append.mp member with member | member
    · exact Membership.mem_append.mpr (.inr member)
    · exact Membership.mem_append.mpr (.inl member)
  · rcases Membership.mem_append.mp member with member | member
    · exact Membership.mem_append.mpr (.inr member)
    · exact Membership.mem_append.mpr (.inl member)

end WordRotation

namespace WordVertexRealization

/-- Rotate a realization by retaining its edges and moving the anchor to the original prefix endpoint.

The two retained segments exchange their order, while the same closed path certifies the new anchor and endpoint
agreement. -/
@[expose] def rotate (model : Vertices.WordVertexRealization source size) (rotation : Selection.WordRotation source
  target) :
    Vertices.WordVertexRealization target size where
  edges := model.edges
  anchor := WordVertexPath.endpoint model.edges rotation.first model.anchor
  closed := by
    have path := WordVertexPath.castWord rotation.source_eq model.closed
    obtain ⟨initial, final⟩ := WordVertexPath.split rotation.first rotation.last path
    exact WordVertexPath.castWord rotation.target_eq.symm (PathEndpoints.append final initial)

/-- Traversing the remaining segment from the rotated anchor returns to the original anchor. -/
theorem rotate_return (model : Vertices.WordVertexRealization source size) (rotation : Selection.WordRotation source
  target) :
    WordVertexPath.endpoint model.edges rotation.last (WordVertexRealization.rotate model rotation).anchor =
      model.anchor := by
  have path := WordVertexPath.castWord rotation.source_eq model.closed
  exact WordVertexPath.endpoint_eq (WordVertexPath.split rotation.first rotation.last path).2

/-- Rotating a realization preserves coverage of its exact finite vertex bank.

Every vertex remains either the retained anchor or an endpoint of an original signed-letter occurrence; cyclic rotation
preserves that occurrence. -/
theorem rotate_covered (model : Vertices.WordVertexRealization source size) (rotation : Selection.WordRotation source
  target)
    (covered : ∀ vertex, model.Supported vertex) : ∀ vertex, (WordVertexRealization.rotate model rotation).Supported
      vertex := by
  intro vertex
  rcases covered vertex with same | ⟨letter, member, same⟩
  · rw [same, ← WordVertexRealization.rotate_return model rotation]
    exact (WordVertexRealization.rotate model rotation).supported_endpoint rotation.last
      (fun letter member => by rw [rotation.target_eq]; exact Membership.mem_append.mpr (.inl member)) (.inl rfl)
  · exact .inr ⟨letter, (VertexRotation.WordRotation.mem_iff rotation letter).mpr member, same⟩

end WordVertexRealization

/-- Transport a universal vertex model through an exact cyclic word rotation.

The original vertex bank and edge readings are retained; prefix endpoint identities transport the anchor and universal
factorization. -/
@[expose] def WordVertexModel.rotate (model : Vertices.WordVertexModel source size) (rotation : Selection.WordRotation
  source target) :
    Vertices.WordVertexModel target size where
  toWordVertexRealization := VertexRotation.WordVertexRealization.rotate model.toWordVertexRealization rotation
  covered := VertexRotation.WordVertexRealization.rotate_covered model.toWordVertexRealization rotation model.covered
  lift := fun other =>
    let returned := VertexRotation.WordVertexRealization.rotate other (VertexRotation.WordRotation.symm rotation)
    let factor := model.lift returned
    { vertices := factor.vertices
      anchor_eq := by
        have readback := WordVertexPath.endpoint_respects model.edges returned.edges factor.vertices rotation.first
          (fun letter member => factor.edge_eq letter (by
            rw [rotation.source_eq]; exact Membership.mem_append.mpr (.inl member))) model.anchor
        rw [factor.anchor_eq] at readback
        exact readback.trans (VertexRotation.WordVertexRealization.rotate_return other (VertexRotation.WordRotation.symm
          rotation))
      edge_eq := fun letter member => factor.edge_eq letter ((VertexRotation.WordRotation.mem_iff rotation letter).mp
        member) }

end Purelib.Topology.Surface.Word.VertexRotation
