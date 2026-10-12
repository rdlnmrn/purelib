module
import Purelib.Data.Fin
import Purelib.Data.List.Membership
import Purelib.Data.List.Filter
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Word.Vertices
public import Purelib.Topology.Surface.Word.PairedWord

public section

namespace Purelib.Topology.Surface.Cut.ContractedWord

open Purelib

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Chain.PathBoundary

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

/-!
# Realize the paired cut word after contracting physical edges

The original occurrence path is transported using its stored generator
provenance. Exactly the one-sided generators are deleted, and each deletion
is justified by equality of its contracted endpoints. The resulting closed
path therefore uses the existing paired word with its original labels.
-/

open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutAlphabet CutWordEntry)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.Vertices (WordVertexModel)

open Purelib.Topology.Surface.Word.Vertices
open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

namespace CutAlphabet

variable {source target : Nat} {labels : Fin source → Fin target}

/-- Every one-sided generator of the constructed alphabet is an original physical boundary edge. -/
theorem ofLists_oneSided : ∀ (boundary : List (Stokes.OrientedEdge source)) (pairs : List
  (ProjectedEdgePairs.ProjectedEdgePair labels))
    (index : Fin (CutAlphabet.ofLists boundary pairs).count),
    (CutAlphabet.ofLists boundary pairs).oneSided index = true → (CutAlphabet.ofLists boundary pairs).generators index ∈
      boundary := by
  intro boundary
  induction boundary with
  | nil =>
      intro pairs
      induction pairs with
      | nil => exact fun index => Fin.elim0 index
      | cons pair pairs ih =>
          intro index
          refine Data.Fin.cases_induction ?_ (fun index => ?_) index
          · intro impossible
            change false = true at impossible
            cases impossible
          · exact ih index
  | cons edge boundary ih =>
      intro pairs index
      refine Data.Fin.cases_induction ?_ (fun index => ?_) index
      · exact fun _ => List.mem_cons_self
      · exact fun oneSided => List.mem_cons_of_mem _ (ih pairs index oneSided)

end CutAlphabet

namespace WordVertexPath

variable {count size : Nat}

/-- Removing a zero-length edge preserves the displayed endpoints. This does not assert that a physical edge was zero
before contraction. -/
theorem retain {edges : Fin count → Stokes.OrientedEdge size} {word : List (SignedWord.SignedGenerator count)}
    {first last : Fin size} (path : WordVertexPath.Path edges word first last) (keep : Fin count → Bool)
    (collapsed : ∀ letter ∈ word, keep letter.index = false →
      (SignedGenerator.vertexEdge edges letter).start = (SignedGenerator.vertexEdge edges letter).finish) :
    WordVertexPath.Path edges (SignedGenerator.retain keep word) first last := by
  induction path with
  | nil => exact .nil _
  | @cons letter word last path ih =>
      have tail := ih (fun entry member => collapsed entry (List.mem_cons_of_mem _ member))
      cases kept : keep letter.index
      · rw [SignedGenerator.retain, Data.List.Filter.filter_cons, kept]
        exact tail.castStart (collapsed letter List.mem_cons_self kept).symm
      · rw [SignedGenerator.retain, Data.List.Filter.filter_cons, kept]
        exact .cons tail

/-- A signed letter starts at one of its underlying generator's two endpoints. -/
private theorem letter_start (edges : Fin count → Stokes.OrientedEdge size) (letter : SignedWord.SignedGenerator count)
  :
    (SignedGenerator.vertexEdge edges letter).start = (edges letter.index).start ∨
      (SignedGenerator.vertexEdge edges letter).start = (edges letter.index).finish := by
  cases letter with
  | mk index reversed => cases reversed
                         · exact .inl rfl
                         · exact .inr rfl

open Purelib.Topology.Surface.Cut.ContractedWord
/-- A path starts at its final anchor or at an endpoint of a retained letter. -/
private theorem start_supported {edges : Fin count → Stokes.OrientedEdge size} {word : List (SignedWord.SignedGenerator
  count)}
    {first last : Fin size} (path : WordVertexPath.Path edges word first last) :
    first = last ∨ ∃ letter ∈ word, first = (edges letter.index).start ∨ first = (edges letter.index).finish := by
  cases path with
  | nil => exact .inl rfl
  | @cons letter tail last path => exact .inr ⟨letter, List.mem_cons_self, WordVertexPath.letter_start edges letter⟩

/-- Every original source survives as a retained letter endpoint or the final anchor, even across an arbitrarily long
run of deleted physical edges. -/
theorem retain_sources {edges : Fin count → Stokes.OrientedEdge size} {word : List (SignedWord.SignedGenerator count)}
    {first last : Fin size} (path : WordVertexPath.Path edges word first last) (keep : Fin count → Bool)
    (collapsed : ∀ letter ∈ word, keep letter.index = false →
      (SignedGenerator.vertexEdge edges letter).start = (SignedGenerator.vertexEdge edges letter).finish)
    (entry : SignedWord.SignedGenerator count) (member : entry ∈ word) :
    (SignedGenerator.vertexEdge edges entry).start = last ∨ ∃ letter ∈ SignedGenerator.retain keep word,
      (SignedGenerator.vertexEdge edges entry).start = (edges letter.index).start ∨
        (SignedGenerator.vertexEdge edges entry).start = (edges letter.index).finish := by
  induction path with
  | nil => exact (List.not_mem_nil member).elim
  | @cons head tail last path ih =>
      have tailCollapsed := fun letter member => collapsed letter (List.mem_cons_of_mem _ member)
      rcases Data.List.Membership.mem_cons.mp member with rfl | inTail
      · cases kept : keep entry.index
        · rw [collapsed entry List.mem_cons_self kept, SignedGenerator.retain, Data.List.Filter.filter_cons, kept]
          exact WordVertexPath.start_supported (WordVertexPath.retain path keep tailCollapsed)
        · exact .inr ⟨entry, Data.List.Filter.mem_filter.mpr ⟨List.mem_cons_self, kept⟩, WordVertexPath.letter_start
            edges entry⟩
      · rcases ih tailCollapsed inTail with same | ⟨letter, member, same⟩
        · exact .inl same
        · exact .inr ⟨letter, Data.List.Filter.mem_filter.mpr ⟨List.mem_cons_of_mem _ (Data.List.Filter.mem_filter.mp
            member).1,
            (Data.List.Filter.mem_filter.mp member).2⟩, same⟩

end WordVertexPath

namespace CutWordEntry

variable {source target count result : Nat} {labels : Fin source → Fin target}
  {generators : Data.Vector (Stokes.OrientedEdge source) count}

/-- Contracting a retained cut occurrence agrees with reading its signed generator edge. -/
theorem contracted_edge (entry : BoundaryWord.CutWordEntry labels generators) (vertices : Fin target → Fin result) :
    (SignedGenerator.vertexEdge (fun index => OrientedEdge.map (fun vertex => vertices (labels vertex)) (generators
      index)) entry.letter) =
      OrientedEdge.map (fun vertex => vertices (labels vertex)) entry.edge := by
  have projected := congrArg (OrientedEdge.map vertices) entry.projected_eq
  cases reversed : entry.letter.reversed with
  | false =>
      dsimp only [SignedGenerator.vertexEdge]
      rw [reversed, if_neg (show ¬ (false = true) from fun impossible => nomatch impossible)]
      rw [reversed, if_neg (show ¬ (false = true) from fun impossible => nomatch impossible)] at projected
      simpa only [OrientedEdge.map_comp] using projected.symm
  | true =>
      dsimp only [SignedGenerator.vertexEdge]
      rw [reversed, if_pos rfl]
      rw [reversed, if_pos rfl] at projected
      simpa only [OrientedEdge.map_comp, OrientedEdge.map_reverse] using projected.symm

open Purelib.Topology.Surface.Cut.ContractedWord in
/-- Transport an original occurrence path to the exact signed-generator path after vertex contraction. -/
theorem contracted_path (vertices : Fin target → Fin result)
    (entries : List (BoundaryWord.CutWordEntry labels generators)) {first last : Fin source}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (entries.map CutWordEntry.edge) first
      last) :
    WordVertexPath.Path (fun index => OrientedEdge.map (fun vertex => vertices (labels vertex)) (generators index))
      (entries.map CutWordEntry.letter) (vertices (labels first)) (vertices (labels last)) := by
  induction entries generalizing first with
  | nil => cases path; exact .nil _
  | cons entry entries ih =>
      cases path with
      | cons tail =>
          have edgeEq := CutWordEntry.contracted_edge entry vertices
          apply PathEndpoints.castStart (congrArg OrientedEdge.start edgeEq)
          exact .cons ((ih tail).castStart (congrArg OrientedEdge.finish edgeEq).symm)

end CutWordEntry

namespace ProjectedEdgePairing

variable {source target result : Nat} {labels : Fin source → Fin target} {boundary : List (Stokes.OrientedEdge source)}

open Purelib.Topology.Surface.Cut.ContractedWord
/-- Every deleted one-sided generator becomes a loop when physical edge endpoints are contracted. -/
private theorem contracted_letter_loop (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels boundary) (vertices :
  Fin target → Fin result)
    (collapsed : ∀ edge ∈ pairing.boundary, vertices (labels edge.start) = vertices (labels edge.finish))
    (letter : SignedWord.SignedGenerator (ProjectedEdgePairing.boundaryWord pairing).alphabet.count)
    (dropped : (!(ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided letter.index) = false) :
    ((SignedGenerator.vertexEdge (fun index => OrientedEdge.map
      (fun vertex => vertices (labels vertex)) ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators index))
        letter)).start =
    ((SignedGenerator.vertexEdge (fun index => OrientedEdge.map
      (fun vertex => vertices (labels vertex)) ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators index))
        letter)).finish := by
  have oneSided : (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided letter.index = true := by
    cases side : (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided letter.index
    · rw [side] at dropped; cases dropped
    · rfl
  have same := collapsed _ (CutAlphabet.ofLists_oneSided pairing.boundary pairing.pairs letter.index oneSided)
  cases reversed : letter.reversed with
  | false =>
      dsimp only [SignedGenerator.vertexEdge]
      rw [reversed, if_neg (show ¬ (false = true) from fun impossible => nomatch impossible)]
      exact same
  | true =>
      dsimp only [SignedGenerator.vertexEdge]
      rw [reversed, if_pos rfl]
      exact same.symm

/-- A contracted physical boundary supplies a literal realization of the actual paired word. It does not supply a
guessed handle basis. -/
@[expose] def contractedWord (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels boundary) (vertices : Fin target
  → Fin result)
    (collapsed : ∀ edge ∈ pairing.boundary, vertices (labels edge.start) = vertices (labels edge.finish))
    (anchor : Fin source) (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor
      anchor) :
    Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters (ProjectedEdgePairing.boundaryWord pairing)) result
      where
  edges := Data.Vector.Basic.vectorOfFn fun index => OrientedEdge.map (fun vertex => vertices (labels vertex))
    ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators index)
  anchor := vertices (labels anchor)
  closed := by
    have input := CutWordEntry.contracted_path vertices (ProjectedEdgePairing.boundaryWord pairing).alphabet.entries
      ((ProjectedEdgePairing.boundaryWord pairing).alphabet.edges_eq.symm ▸ closed)
    have erased : ∀ letter ∈ (ProjectedEdgePairing.boundaryWord pairing).alphabet.entries.map CutWordEntry.letter,
        (!(ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided letter.index) = false →
        ((SignedGenerator.vertexEdge (fun index => OrientedEdge.map
          (fun vertex => vertices (labels vertex)) ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators
            index)) letter)).start =
        ((SignedGenerator.vertexEdge (fun index => OrientedEdge.map
          (fun vertex => vertices (labels vertex)) ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators
            index)) letter)).finish := by
      exact fun letter _ dropped => ProjectedEdgePairing.contracted_letter_loop pairing vertices collapsed letter
        dropped
    apply WordVertexPath.congr (WordVertexPath.retain input (fun index => !(ProjectedEdgePairing.boundaryWord
      pairing).alphabet.oneSided index) erased)
    exact fun letter _ => (Data.Vector.Basic.vectorOfFn_apply
      (fun index => OrientedEdge.map (fun vertex => vertices (labels vertex)) ((ProjectedEdgePairing.boundaryWord
        pairing).alphabet.generators index)) letter.index).symm

/-- Every original boundary source survives in the contracted paired word's endpoint support. -/
theorem contractedWord_supported (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels boundary) (vertices : Fin
  target → Fin result)
    (collapsed : ∀ edge ∈ pairing.boundary, vertices (labels edge.start) = vertices (labels edge.finish))
    (anchor : Fin source) (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor
      anchor)
    {vertex : Fin source} (member : vertex ∈ boundary.map OrientedEdge.start) :
    (ProjectedEdgePairing.contractedWord pairing vertices collapsed anchor closed).Supported (vertices (labels vertex))
      := by
  obtain ⟨edge, edgeMember, vertexEq⟩ := Map.mem_map.mp member
  rw [← (ProjectedEdgePairing.boundaryWord pairing).alphabet.edges_eq] at edgeMember
  obtain ⟨entry, entryMember, edgeEq⟩ := Map.mem_map.mp edgeMember
  have input := CutWordEntry.contracted_path vertices (ProjectedEdgePairing.boundaryWord pairing).alphabet.entries
    ((ProjectedEdgePairing.boundaryWord pairing).alphabet.edges_eq.symm ▸ closed)
  have supported := WordVertexPath.retain_sources input (fun index => !(ProjectedEdgePairing.boundaryWord
    pairing).alphabet.oneSided index)
    (fun letter _ dropped => ProjectedEdgePairing.contracted_letter_loop pairing vertices collapsed letter dropped)
    entry.letter (Map.mem_map_of_mem entryMember)
  have startEq := congrArg OrientedEdge.start (CutWordEntry.contracted_edge entry vertices)
  change _ = vertices (labels entry.edge.start) at startEq
  rw [edgeEq, vertexEq] at startEq
  rw [startEq] at supported
  rcases supported with same | ⟨letter, letterMember, same⟩
  · exact .inl same
  · refine .inr ⟨letter, letterMember, ?_⟩
    simpa only [ProjectedEdgePairing.contractedWord, Data.Vector.Basic.vectorOfFn_apply] using same

end ProjectedEdgePairing

/-- A factor reaches every vertex of a covered realization. The witnesses are its anchor or the corresponding displayed
generator endpoints. -/
theorem WordVertexRealization.Factor.surjective {count size target : Nat} {word : List (SignedWord.SignedGenerator
  count)}
    {first : Vertices.WordVertexRealization word size} {last : Vertices.WordVertexRealization word target}
    (factor : first.Factor last) (covered : ∀ vertex, last.Supported vertex) : Function.Surjective factor.vertices := by
  intro vertex
  rcases covered vertex with same | ⟨letter, member, same | same⟩
  · exact ⟨first.anchor, factor.anchor_eq.trans same.symm⟩
  · exact ⟨(first.edges letter.index).start, (congrArg OrientedEdge.start (factor.edge_eq letter member)).trans
      same.symm⟩
  · exact ⟨(first.edges letter.index).finish, (congrArg OrientedEdge.finish (factor.edge_eq letter member)).trans
      same.symm⟩

end Purelib.Topology.Surface.Cut.ContractedWord
