module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Selection
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Word.Surgery
public import Purelib.Topology.Surface.Word.Vertices
import Purelib.Topology.Surface.Word.VertexRotation
import Purelib.Topology.Chain.PathBoundary

section

open Purelib

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.Selection

open Purelib.Topology.Surface.Word.SignedWord

open Purelib.Topology.Surface.Word.Surgery

public section

/-!
# Handle surgery preserves the exact finite vertex presentation

The paths in `p U q V (-p) W (-q) X` reconnect as `U X W V`.
Conversely their four cached junctions reconstruct the two removed edges.
Universal factorization, not just a closed drawing, certifies that this
operation preserves all and only the vertex identifications.
-/

namespace Purelib.Topology.Surface.Word.VertexSurgery

open Purelib.Topology.Surface.Word.VertexRotation
open Purelib.Topology.Surface.Word.Surgery (InterlacedWord)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.Vertices (WordVertexRealization WordVertexModel)
open Purelib.Topology.Surface.Word.Vertices

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Topology.Surface.Word.Vertices.WordVertexPath (Path endpoint)

namespace InterlacedWord

variable {count size : Nat}

/-- Every nonpivot signed occurrence belongs to the shorter word exactly when it belongs to the original word. -/
theorem mem_after_iff (cut : Surgery.InterlacedWord count) (letter : SignedWord.SignedGenerator count)
    (notFirst : letter.index ≠ cut.first) (notLast : letter.index ≠ cut.last) :
    letter ∈ cut.after ↔ letter ∈ cut.before := by
  have same := cut.occurrences_before letter
  rw [if_neg notFirst, if_neg notLast, Nat.add_zero, ← cut.occurrences_after] at same
  constructor <;> intro member
  · exact (SignedGenerator.locate letter cut.before (same.symm ▸ SignedGenerator.occurrences_positive letter cut.after
      member)).member
  · exact (SignedGenerator.locate letter cut.after (same ▸ SignedGenerator.occurrences_positive letter cut.before
      member)).member

/-- Signed uniqueness excludes both removed pivot generators from the shorter word. -/
theorem after_avoids (cut : Surgery.InterlacedWord count)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (letter : SignedWord.SignedGenerator count) (member : letter ∈ cut.after) :
    letter.index ≠ cut.first ∧ letter.index ≠ cut.last := by
  have positive := SignedGenerator.occurrences_positive letter cut.after member
  rw [cut.occurrences_after] at positive
  exact cut.tail_avoids unique letter (SignedGenerator.locate letter cut.tail positive).member

/-- A nonempty signed path starts at the first oriented generator endpoint. -/
private theorem head_start {edges : Fin count → Stokes.OrientedEdge size} {head : SignedWord.SignedGenerator count}
    {tail : List (SignedWord.SignedGenerator count)} {first last : Fin size} (path : WordVertexPath.Path edges (head ::
      tail) first last) :
    first = (SignedGenerator.vertexEdge edges head).start := by cases path; rfl

/-- The four original segment paths with their exact endpoints at the two pivot edges. -/
structure BeforePaths (cut : Surgery.InterlacedWord count) (edges : Fin count → Stokes.OrientedEdge size) : Prop where
  /-- Path from the first pivot finish to the last pivot start through segment U. -/ u : WordVertexPath.Path edges cut.u
    (edges cut.first).finish (edges cut.last).start
  /-- Path from the last pivot finish to the first pivot finish through segment V. -/ v : WordVertexPath.Path edges
    cut.v (edges cut.last).finish (edges cut.first).finish
  /-- Path from the first pivot start to the last pivot finish through segment W. -/ w : WordVertexPath.Path edges cut.w
    (edges cut.first).start (edges cut.last).finish
  /-- Path from the last pivot start to the first pivot start through segment X. -/ x : WordVertexPath.Path edges cut.x
    (edges cut.last).start (edges cut.first).start

/-- Split an original interlaced realization into its four retained segment paths. -/
theorem before_paths (cut : Surgery.InterlacedWord count) (model : Vertices.WordVertexRealization cut.before size) :
    InterlacedWord.BeforePaths cut model.edges := by
  have atStart : model.anchor = (model.edges cut.first).start := InterlacedWord.head_start model.closed
  have path := (model.closed.castStart atStart).castFinish atStart
  change WordVertexPath.Path model.edges (SignedGenerator.mk cut.first false :: _) _ _ at path
  cases path with
  | cons tail =>
      obtain ⟨c, u, rest⟩ := PathEndpoints.split_append cut.u _ tail
      cases rest with
      | cons tail =>
          obtain ⟨b, v, rest⟩ := PathEndpoints.split_append cut.v _ tail
          cases rest with
          | cons tail =>
              obtain ⟨d, w, rest⟩ := PathEndpoints.split_append cut.w _ tail
              cases rest with
              | cons x => exact ⟨u, v, w, x⟩

/-- The original interlaced realization is anchored at the first pivot start. -/
theorem before_anchor (cut : Surgery.InterlacedWord count) (model : Vertices.WordVertexRealization cut.before size) :
    model.anchor = (model.edges cut.first).start := InterlacedWord.head_start model.closed

/-- Realize the reconnected word on the same vertex bank using the four original segment paths. -/
@[expose] def removeVertices (cut : Surgery.InterlacedWord count) (model : Vertices.WordVertexRealization cut.before
  size) :
    Vertices.WordVertexRealization cut.after size where
  edges := model.edges
  anchor := (model.edges cut.first).finish
  closed :=
    let paths := InterlacedWord.before_paths cut model
    PathEndpoints.append
      (PathEndpoints.append
        (PathEndpoints.append paths.u paths.x) paths.w) paths.v

set_option genInjectivity false in
/-- All junctions are stored once and tied to their actual prefix paths. -/
structure VertexCorners (cut : Surgery.InterlacedWord count) (model : Vertices.WordVertexRealization cut.after size)
  where
  /-- Cached junction after segment U in the shorter word. -/ c : Fin size
  /-- Cached junction after segment X in the shorter word. -/ a : Fin size
  /-- Cached junction after segment W in the shorter word. -/ d : Fin size
  /-- Original U path from the shorter-word anchor to junction c. -/ u : WordVertexPath.Path model.edges cut.u
    model.anchor c
  /-- Original X path from junction c to junction a. -/ x : WordVertexPath.Path model.edges cut.x c a
  /-- Original W path from junction a to junction d. -/ w : WordVertexPath.Path model.edges cut.w a d
  /-- Original V path returning from junction d to the shorter-word anchor. -/ v : WordVertexPath.Path model.edges cut.v
    d model.anchor

constructive_injectivity VertexCorners

/-- Cache the three successive junctions of the shorter word with their exact prefix-path certificates. -/
@[expose] def vertexCorners (cut : Surgery.InterlacedWord count) (model : Vertices.WordVertexRealization cut.after size)
  : InterlacedWord.VertexCorners cut model :=
  let c := WordVertexPath.endpoint model.edges cut.u model.anchor
  let a := WordVertexPath.endpoint model.edges cut.x c
  let d := WordVertexPath.endpoint model.edges cut.w a
  have path : WordVertexPath.Path model.edges (cut.u ++ (cut.x ++ (cut.w ++ cut.v))) model.anchor model.anchor := by
    simpa only [InterlacedWord.after, Purelib.Data.List.Append.append_assoc] using model.closed
  let first := WordVertexPath.split cut.u _ path
  let second := WordVertexPath.split cut.x _ first.2
  let third := WordVertexPath.split cut.w cut.v second.2
  ⟨c, a, d, first.1, second.1, third.1, third.2⟩

namespace VertexCorners

variable {cut : Surgery.InterlacedWord count} {model : Vertices.WordVertexRealization cut.after size}

/-- Reconstruct the two removed pivot edges from the cached shorter-word junctions. -/
@[expose] def edges (corners : InterlacedWord.VertexCorners cut model) : Data.Vector (Stokes.OrientedEdge
  size) count :=
  Data.Vector.Basic.vectorOfFn fun index => if index = cut.first then ⟨corners.a, model.anchor⟩
    else if index = cut.last then ⟨corners.c, corners.d⟩ else model.edges index

section
open Purelib.Topology.Surface.Word.VertexSurgery.InterlacedWord.VertexCorners
/-- The first restored pivot joins junction a to the shorter-word anchor. -/
theorem edges_first (corners : InterlacedWord.VertexCorners cut model) : corners.edges cut.first = ⟨corners.a,
  model.anchor⟩ := by
  rw [edges, Data.Vector.Basic.vectorOfFn_apply, if_pos rfl]

/-- The last restored pivot joins junction c to junction d. -/
theorem edges_last (corners : InterlacedWord.VertexCorners cut model) : corners.edges cut.last = ⟨corners.c, corners.d⟩
  := by
  rw [edges, Data.Vector.Basic.vectorOfFn_apply, if_neg (Ne.symm cut.distinct), if_pos rfl]

/-- Every nonpivot generator retains its original shorter-word edge. -/
theorem edges_other (corners : InterlacedWord.VertexCorners cut model) (index : Fin count)
    (first : index ≠ cut.first) (last : index ≠ cut.last) : corners.edges index = model.edges index := by
  rw [edges, Data.Vector.Basic.vectorOfFn_apply, if_neg first, if_neg last]

end

/-- All actual shorter-word occurrences retain their original edges after restoration. -/
theorem edges_on_after (corners : InterlacedWord.VertexCorners cut model)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (letter : SignedWord.SignedGenerator count) (member : letter ∈ cut.after) : corners.edges letter.index = model.edges
      letter.index :=
  corners.edges_other letter.index (InterlacedWord.after_avoids cut unique letter member).1 (InterlacedWord.after_avoids
    cut unique letter member).2

/-- Reconstruct a closed realization of the original interlaced word from the retained junctions. -/
@[expose] def restore (corners : InterlacedWord.VertexCorners cut model)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1) :
    Vertices.WordVertexRealization cut.before size where
  edges := corners.edges
  anchor := corners.a
  closed := by
    have sameU (letter : SignedWord.SignedGenerator count) (member : letter ∈ cut.u) :
        model.edges letter.index = corners.edges letter.index :=
      (corners.edges_on_after unique letter (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        member)))).symm
    have sameX (letter : SignedWord.SignedGenerator count) (member : letter ∈ cut.x) :
        model.edges letter.index = corners.edges letter.index :=
      (corners.edges_on_after unique letter (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        member)))).symm
    have sameW (letter : SignedWord.SignedGenerator count) (member : letter ∈ cut.w) :
        model.edges letter.index = corners.edges letter.index :=
      (corners.edges_on_after unique letter (List.mem_append_left _ (List.mem_append_right _ member))).symm
    have sameV (letter : SignedWord.SignedGenerator count) (member : letter ∈ cut.v) :
        model.edges letter.index = corners.edges letter.index :=
      (corners.edges_on_after unique letter (List.mem_append_right _ member)).symm
    have u := WordVertexPath.congr corners.u sameU
    have x := WordVertexPath.congr corners.x sameX
    have w := WordVertexPath.congr corners.w sameW
    have v := WordVertexPath.congr corners.v sameV
    have first : SignedGenerator.vertexEdge corners.edges ⟨cut.first, false⟩ = ⟨corners.a, model.anchor⟩ :=
      corners.edges_first
    have last : SignedGenerator.vertexEdge corners.edges ⟨cut.last, false⟩ = ⟨corners.c, corners.d⟩ :=
      corners.edges_last
    have firstReverse : SignedGenerator.vertexEdge corners.edges ⟨cut.first, true⟩ = ⟨model.anchor, corners.a⟩ :=
      congrArg OrientedEdge.reverse corners.edges_first
    have lastReverse : SignedGenerator.vertexEdge corners.edges ⟨cut.last, true⟩ = ⟨corners.d, corners.c⟩ :=
      congrArg OrientedEdge.reverse corners.edges_last
    unfold InterlacedWord.before
    have one : WordVertexPath.Path corners.edges [⟨cut.first, false⟩] corners.a model.anchor := by
      simpa only [first] using WordVertexPath.single corners.edges ⟨cut.first, false⟩
    have two : WordVertexPath.Path corners.edges [⟨cut.last, false⟩] corners.c corners.d := by
      simpa only [last] using WordVertexPath.single corners.edges ⟨cut.last, false⟩
    have three : WordVertexPath.Path corners.edges [⟨cut.first, true⟩] model.anchor corners.a := by
      simpa only [firstReverse] using WordVertexPath.single corners.edges ⟨cut.first, true⟩
    have four : WordVertexPath.Path corners.edges [⟨cut.last, true⟩] corners.d corners.c := by
      simpa only [lastReverse] using WordVertexPath.single corners.edges ⟨cut.last, true⟩
    exact PathEndpoints.append one
      (PathEndpoints.append u
        (PathEndpoints.append two
          (PathEndpoints.append v
            (PathEndpoints.append three
              (PathEndpoints.append w
                (PathEndpoints.append four x))))))

/-- Restoring the two pivot edges preserves coverage of the original finite vertex bank. -/
theorem restore_covered (corners : InterlacedWord.VertexCorners cut model)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (covered : ∀ vertex, model.Supported vertex) : ∀ vertex, (corners.restore unique).Supported vertex := by
  intro vertex
  rcases covered vertex with same | ⟨letter, member, same⟩
  · refine .inr ⟨⟨cut.first, false⟩, List.mem_cons_self, .inr ?_⟩
    change vertex = (corners.edges cut.first).finish
    rw [corners.edges_first]
    exact same
  · have clear := InterlacedWord.after_avoids cut unique letter member
    refine .inr ⟨letter, (InterlacedWord.mem_after_iff cut letter clear.1 clear.2).mp member, ?_⟩
    change vertex = (corners.edges letter.index).start ∨ vertex = (corners.edges letter.index).finish
    rw [corners.edges_other letter.index clear.1 clear.2]
    exact same

/-- Extend a factor map from the shorter word to the restored original interlaced word.

The exact prefix paths identify the images of the three cached junctions and both reconstructed pivots. -/
@[expose] def restoreFactor {target : Nat} (corners : InterlacedWord.VertexCorners cut model)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (other : Vertices.WordVertexRealization cut.before target) (factor : model.Factor (InterlacedWord.removeVertices cut
      other)) :
    (corners.restore unique).Factor other :=
  have paths := InterlacedWord.before_paths cut other
  have cEq : factor.vertices corners.c = (other.edges cut.last).start := by
    have natural := WordVertexPath.endpoint_respects model.edges other.edges factor.vertices cut.u
      (fun letter member => factor.edge_eq letter
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))) model.anchor
    rw [WordVertexPath.endpoint_eq corners.u, factor.anchor_eq] at natural
    exact natural.trans (WordVertexPath.endpoint_eq paths.u)
  have aEq : factor.vertices corners.a = (other.edges cut.first).start := by
    have natural := WordVertexPath.endpoint_respects model.edges other.edges factor.vertices cut.x
      (fun letter member => factor.edge_eq letter
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))) corners.c
    rw [WordVertexPath.endpoint_eq corners.x, cEq] at natural
    exact natural.trans (WordVertexPath.endpoint_eq paths.x)
  have dEq : factor.vertices corners.d = (other.edges cut.last).finish := by
    have natural := WordVertexPath.endpoint_respects model.edges other.edges factor.vertices cut.w
      (fun letter member => factor.edge_eq letter (List.mem_append_left _ (List.mem_append_right _ member))) corners.a
    rw [WordVertexPath.endpoint_eq corners.w, aEq] at natural
    exact natural.trans (WordVertexPath.endpoint_eq paths.w)
  { vertices := factor.vertices
    anchor_eq := aEq.trans (InterlacedWord.before_anchor cut other).symm
    edge_eq := fun letter member => by
      change OrientedEdge.map factor.vertices (corners.edges letter.index) = other.edges letter.index
      by_cases first : letter.index = cut.first
      · rw [first, corners.edges_first]
        change OrientedEdge.mk (factor.vertices corners.a) (factor.vertices model.anchor) = _
        rw [aEq, factor.anchor_eq]
        rfl
      · by_cases last : letter.index = cut.last
        · rw [last, corners.edges_last]
          change OrientedEdge.mk (factor.vertices corners.c) (factor.vertices corners.d) = _
          rw [cEq, dEq]
        · rw [corners.edges_other letter.index first last]
          exact factor.edge_eq letter ((InterlacedWord.mem_after_iff cut letter first last).mpr member) }

end VertexCorners

/-- Restore the original interlaced word's universal vertex model on the same finite bank. -/
@[expose] def restoreVertexModel (cut : Surgery.InterlacedWord count) (model : Vertices.WordVertexModel cut.after size)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1) :
    Vertices.WordVertexModel cut.before size :=
  let corners := InterlacedWord.vertexCorners cut model.toWordVertexRealization
  { toWordVertexRealization := corners.restore unique
    covered := corners.restore_covered unique model.covered
    lift := fun other => corners.restoreFactor unique other (model.lift (InterlacedWord.removeVertices cut other)) }

end InterlacedWord
end Purelib.Topology.Surface.Word.VertexSurgery

end
