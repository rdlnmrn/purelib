module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Filter
import Purelib.Data.List.Map
public import Purelib.Data.List.Membership
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Word.Vertices
public import Purelib.Topology.Surface.Boundary.BoundaryStateReading
import Purelib.Topology.Surface.Cut.ContractedWord
import Purelib.Topology.Surface.Cut.AlphabetWitnesses
public import Purelib.Topology.Surface.Cut.VertexGluing
meta import Mathlib.Tactic.Linter.Lint

/-!
# Read an arbitrary paired-word realization on the original cut vertices

Physical letters keep the current vertex; paired letters follow the given
realization. Literal occurrence witnesses prove that both ends of every cut
pair agree. No equality of projected labels is used to invent a gluing.
-/

public section

namespace Purelib.Topology.Surface.Cut.VertexReading

open Purelib
open Purelib.Data.List
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Boundary
open Purelib.Topology.Surface.Boundary.BoundaryStateReading.PolygonStokes
open _root_.Purelib.Topology.Surface.Boundary.BoundaryStateReading renaming PolygonStokes -> BoundaryStateReading
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.AlphabetWitnesses
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.PairedWord
open Purelib.Topology.Surface.Word.Vertices

open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord CutWordEntry)
open Purelib.Topology.Surface.Word.Vertices (WordVertexRealization)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.VertexGluing (PairVertexJoin)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

variable {source target size : Nat} {labels : Fin source → Fin target} {boundary : List (Stokes.OrientedEdge source)}

set_option genInjectivity false in
/-- Read a paired-word realization on the original cut-vertex bank.

Retained paired letters follow their exact realized edges, while physical letters have equal endpoint readings and leave
the state unchanged. -/
structure CutVertexReading (word : BoundaryWord.CutBoundaryWord labels boundary)
    (other : Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters word) size) (anchor : Fin source) where
  /-- Cached target vertex for every original cut vertex. -/ values : Data.Vector (Fin size) source
  /-- The cut anchor reads as the supplied realization's original anchor. -/ anchor_eq : values anchor = other.anchor
  /-- Each paired cut entry maps to its exact signed edge in the supplied realization. -/ kept : ∀ entry ∈
    word.alphabet.entries, word.alphabet.oneSided entry.letter.index = false →
    OrientedEdge.map values entry.edge = SignedGenerator.vertexEdge other.edges entry.letter
  /-- Each physical cut entry has equal endpoint readings. -/ dropped : ∀ entry ∈ word.alphabet.entries,
    word.alphabet.oneSided entry.letter.index = true →
    values entry.edge.start = values entry.edge.finish

constructive_injectivity CutVertexReading

namespace CutVertexReading

variable {word : BoundaryWord.CutBoundaryWord labels boundary} {other : Vertices.WordVertexRealization
  (CutBoundaryWord.pairedLetters word) size} {anchor : Fin source}

/-- Advance along a retained paired letter, leaving the current vertex unchanged for a physical letter. -/
@[expose] def step (word : BoundaryWord.CutBoundaryWord labels boundary) (other : Vertices.WordVertexRealization
  (CutBoundaryWord.pairedLetters word) size)
    (entry : BoundaryWord.CutWordEntry labels word.alphabet.generators) (current : Fin size) : Fin size :=
  if word.alphabet.oneSided entry.letter.index then current else (SignedGenerator.vertexEdge other.edges
    entry.letter).finish

section
open Purelib.Topology.Surface.Cut.VertexReading
/-- Advancing through cut entries agrees with the endpoint of the retained paired-letter word.

The same retained entry list drives both advances. Rejected letters preserve the current state; accepted letters use the
realized edge endpoint. -/
private theorem advance_eq (word : BoundaryWord.CutBoundaryWord labels boundary) (other : Vertices.WordVertexRealization
  (CutBoundaryWord.pairedLetters word) size)
    (entries : List (BoundaryWord.CutWordEntry labels word.alphabet.generators)) (current : Fin size) :
    BoundaryStateReading.advance (step word other) entries current =
      WordVertexPath.endpoint other.edges (SignedGenerator.retain (fun index => !word.alphabet.oneSided index)
        (entries.map CutWordEntry.letter)) current := by
  induction entries generalizing current with
  | nil => rfl
  | cons entry entries ih =>
      rw [BoundaryStateReading.advance, ih, step, List.map_cons]
      simp only [SignedGenerator.retain, Filter.filter_cons]
      cases word.alphabet.oneSided entry.letter.index <;> rfl

/-- The state before each retained paired letter is that realized edge's start vertex.

The retained split identifies the actual occurrence in the original word. Its accepted generator determines the matching
realized edge without selecting a new occurrence. -/
private theorem prefix_kept (word : BoundaryWord.CutBoundaryWord labels boundary) (other :
  Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters word) size)
    (before : List (BoundaryWord.CutWordEntry labels word.alphabet.generators)) (entry : BoundaryWord.CutWordEntry
      labels word.alphabet.generators)
    (after : List (BoundaryWord.CutWordEntry labels word.alphabet.generators))
    (equation : word.alphabet.entries = before ++ entry :: after) (kept : word.alphabet.oneSided entry.letter.index =
      false) :
    BoundaryStateReading.advance (step word other) before other.anchor = (SignedGenerator.vertexEdge
      other.edges entry.letter).start := by
  have path := other.closed
  change WordVertexPath.Path other.edges
    (SignedGenerator.retain (fun index => !word.alphabet.oneSided index) word.letters) other.anchor other.anchor at path
  rw [word.letters_eq, equation, Map.map_append, List.map_cons, SignedGenerator.retain, Filter.filter_append,
    Filter.filter_cons, kept] at path
  have rest := (WordVertexPath.split _ _ path).2
  have head_start {first last : Fin size} {tail : List (SignedWord.SignedGenerator word.alphabet.count)}
      (path : WordVertexPath.Path other.edges (entry.letter :: tail) first last) :
      first = (SignedGenerator.vertexEdge other.edges entry.letter).start := by cases path; rfl
  rw [advance_eq]
  exact head_start rest

end

open Purelib.Topology.Surface.Cut in
open Purelib.Topology.Surface.Cut.VertexReading in
/-- Cache the cut-vertex reading induced by the original simple closed boundary and supplied paired-word realization. -/
@[expose] def build (word : BoundaryWord.CutBoundaryWord labels boundary) (other : Vertices.WordVertexRealization
  (CutBoundaryWord.pairedLetters word) size)
    (anchor : Fin source) (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor
      anchor)
    (simple : (boundary.map OrientedEdge.start).Nodup) : CutVertexReading word other anchor :=
  let states := BoundaryStateReading.build CutWordEntry.edge (step word other) word.alphabet.entries
    anchor other.anchor
    (word.alphabet.edges_eq.symm ▸ closed) (word.alphabet.edges_eq.symm ▸ simple)
    (by rw [advance_eq, ← word.letters_eq]; exact WordVertexPath.endpoint_eq other.closed)
  { values := states.values
    anchor_eq := states.anchor_eq
    kept := fun entry member kept => by
      obtain ⟨before, after, equation⟩ := Membership.split_of_mem member
      change OrientedEdge.mk _ _ = _
      rw [states.start_eq before entry after equation, states.finish_eq before entry after equation,
        prefix_kept word other before entry after equation kept, step, kept]
      rfl
    dropped := fun entry member dropped => by
      obtain ⟨before, after, equation⟩ := Membership.split_of_mem member
      rw [states.start_eq before entry after equation, states.finish_eq before entry after equation,
        step, dropped]
      rfl }

open Purelib.Topology.Surface.Cut
/-- Both aligned endpoints of every original cut pair have equal retained vertex readings. -/
theorem pair_endpoints {pairing : ProjectedEdgePairs.ProjectedEdgePairing labels boundary}
    {other : Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters (ProjectedEdgePairing.boundaryWord pairing))
      size}
    (reading : CutVertexReading (ProjectedEdgePairing.boundaryWord pairing) other anchor)
    (pair : ProjectedEdgePairs.ProjectedEdgePair labels) (member : pair ∈ pairing.pairs) :
    reading.values pair.first.start = reading.values pair.second.finish ∧
      reading.values pair.first.finish = reading.values pair.second.start := by
  obtain ⟨index, side, first, last⟩ := ProjectedEdgePairing.boundaryWord_pair pairing pair member
  obtain ⟨first, firstMember, firstEdge, firstLetter⟩ := first
  obtain ⟨last, lastMember, lastEdge, lastLetter⟩ := last
  have firstKept := reading.kept first firstMember (by rw [firstLetter]; exact side)
  have lastKept := reading.kept last lastMember (by rw [lastLetter]; exact side)
  rw [firstEdge, firstLetter] at firstKept
  rw [lastEdge, lastLetter] at lastKept
  exact ⟨(congrArg OrientedEdge.start firstKept).trans (congrArg OrientedEdge.finish lastKept).symm,
    (congrArg OrientedEdge.finish firstKept).trans (congrArg OrientedEdge.start lastKept).symm⟩

/-- Every original physical boundary edge has equal retained endpoint readings. -/
theorem physical_endpoints {pairing : ProjectedEdgePairs.ProjectedEdgePairing labels boundary}
    {other : Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters (ProjectedEdgePairing.boundaryWord pairing))
      size}
    (reading : CutVertexReading (ProjectedEdgePairing.boundaryWord pairing) other anchor)
    (edge : Stokes.OrientedEdge source) (member : edge ∈ pairing.boundary) : reading.values edge.start = reading.values
      edge.finish := by
  obtain ⟨index, side, entry, entryMember, edgeEq, letterEq⟩ := ProjectedEdgePairing.boundaryWord_physical pairing edge
    member
  have same := reading.dropped entry entryMember (by rw [letterEq]; exact side)
  rw [edgeEq] at same
  exact same

/-- Vertex identifications generated by original cut pairs preserve the retained reading. -/
theorem joined_eq {pairing : ProjectedEdgePairs.ProjectedEdgePairing labels boundary}
    {other : Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters (ProjectedEdgePairing.boundaryWord pairing))
      size}
    (reading : CutVertexReading (ProjectedEdgePairing.boundaryWord pairing) other anchor) {first last :
      Fin source}
    (joined : VertexGluing.PairVertexJoin pairing.pairs first last) : reading.values first = reading.values last := by
  induction joined with
  | refl => rfl
  | start pair member => exact (reading.pair_endpoints pair member).1
  | finish pair member => exact (reading.pair_endpoints pair member).2
  | symm previous ih => exact ih.symm
  | trans first last ihFirst ihLast => exact ihFirst.trans ihLast

end CutVertexReading
end Purelib.Topology.Surface.Cut.VertexReading

end
