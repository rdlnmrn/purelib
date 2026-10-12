module
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Nodup
import Purelib.Data.Vector.Basic
public import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PolygonSewing
public import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Selection
import Purelib.Tactic.QuotientFreeOmega

section

open Purelib

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Chain.PathBoundary

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

public section

/-!
# Finite vertex realizations of a signed polygon word

A generator has two displayed endpoints; its negative occurrence uses the
same endpoints in reverse order. A universal realization supplies an actual
factor map to every other finite realization. Together with coverage this
rules out both extra identifications and unused vertex slots. The empty
word retains its single base vertex.
-/

namespace Purelib.Topology.Surface.Word.Vertices

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

namespace SignedGenerator

/-- Read a generator edge in the signed letter's retained orientation. -/
@[expose] def vertexEdge {count size : Nat} (edges : Fin count → Stokes.OrientedEdge size)
    (letter : SignedWord.SignedGenerator count) : Stokes.OrientedEdge size :=
  if letter.reversed then (edges letter.index).reverse else edges letter.index

/-- Vertex mapping commutes with reading a signed generator edge. -/
theorem vertexEdge_map {count source target : Nat} (edges : Fin count → Stokes.OrientedEdge source)
    (map : Fin source → Fin target) (letter : SignedWord.SignedGenerator count) :
    SignedGenerator.vertexEdge (fun index => OrientedEdge.map map (edges index)) letter = OrientedEdge.map map
      (SignedGenerator.vertexEdge edges letter) := by
  cases letter with
  | mk index reversed => cases reversed <;> rfl

/-- Equal original generator edges give equal readings for the same signed letter. -/
theorem vertexEdge_congr {count size : Nat} {first last : Fin count → Stokes.OrientedEdge size}
    (letter : SignedWord.SignedGenerator count) (same : first letter.index = last letter.index) :
    SignedGenerator.vertexEdge first letter = SignedGenerator.vertexEdge last letter := by
  unfold SignedGenerator.vertexEdge
  rw [same]

end SignedGenerator

namespace WordVertexPath

variable {count size : Nat}

/-- An oriented endpoint path following the actual signed generator occurrences. -/
abbrev Path (edges : Fin count → Stokes.OrientedEdge size) (word : List (SignedWord.SignedGenerator count))
    (first last : Fin size) : Prop :=
  PathBoundary.PathEndpoints (fun letter => (Vertices.SignedGenerator.vertexEdge edges letter).start)
    (fun letter => (Vertices.SignedGenerator.vertexEdge edges letter).finish) word first last

/-- Transport a path across an equality of its original signed word. -/
theorem castWord {edges : Fin count → Stokes.OrientedEdge size} {first last : List (SignedWord.SignedGenerator count)}
    {start finish : Fin size} (same : first = last) (path : WordVertexPath.Path edges first start finish) :
      WordVertexPath.Path edges last start finish := by
  cases same
  exact path

/-- A single signed occurrence connects its actual oriented endpoints. -/
theorem single (edges : Fin count → Stokes.OrientedEdge size) (letter : SignedWord.SignedGenerator count) :
    WordVertexPath.Path edges [letter] (Vertices.SignedGenerator.vertexEdge edges letter).start
      (Vertices.SignedGenerator.vertexEdge edges letter).finish := .cons (.nil _)

/-- Read a prefix endpoint directly from its stored edges, not from a proof or a search for an existential path split.
-/
@[expose] def endpoint (edges : Fin count → Stokes.OrientedEdge size) : List (SignedWord.SignedGenerator count) → Fin
  size → Fin size
  | [], first => first
  | letter :: tail, _ => Purelib.Topology.Surface.Word.Vertices.WordVertexPath.endpoint edges tail
    (Vertices.SignedGenerator.vertexEdge edges letter).finish

/-- Executable endpoint readback agrees with the path's certified final vertex. -/
theorem endpoint_eq {edges : Fin count → Stokes.OrientedEdge size} {word : List (SignedWord.SignedGenerator count)}
    {first last : Fin size} (path : WordVertexPath.Path edges word first last) : WordVertexPath.endpoint edges word
      first = last := by
  induction path with
  | nil => rfl
  | cons _ ih => exact ih

/-- Split a concatenated path at its executable original-prefix endpoint. -/
theorem split {edges : Fin count → Stokes.OrientedEdge size} (first last : List (SignedWord.SignedGenerator count))
    {start finish : Fin size} (path : WordVertexPath.Path edges (first ++ last) start finish) :
    WordVertexPath.Path edges first start (WordVertexPath.endpoint edges first start) ∧ WordVertexPath.Path edges last
      (WordVertexPath.endpoint edges first start) finish := by
  obtain ⟨middle, initial, final⟩ := PathEndpoints.split_append first last path
  rw [WordVertexPath.endpoint_eq initial]
  exact ⟨initial, final⟩

/-- Transport a path between edge assignments agreeing on every original occurrence. -/
theorem congr {first last : Fin count → Stokes.OrientedEdge size} {word : List (SignedWord.SignedGenerator count)}
    {start finish : Fin size} (path : WordVertexPath.Path first word start finish)
    (same : ∀ letter ∈ word, first letter.index = last letter.index) : WordVertexPath.Path last word start finish := by
  induction path with
  | nil => exact .nil _
  | @cons letter tail finish path ih =>
      have head := Vertices.SignedGenerator.vertexEdge_congr letter (same letter List.mem_cons_self)
      have rest := ih (fun entry member => same entry (List.mem_cons_of_mem _ member))
      apply PathEndpoints.castStart (congrArg OrientedEdge.start head).symm
      exact .cons (rest.castStart (congrArg OrientedEdge.finish head))

section
open Purelib.Topology.Surface.Word.Vertices.WordVertexPath
/-- Map a signed endpoint path through a finite vertex map. -/
theorem map {target : Nat} {edges : Fin count → Stokes.OrientedEdge size} {word : List (SignedWord.SignedGenerator
  count)}
    {first last : Fin size} (path : WordVertexPath.Path edges word first last) (map : Fin size → Fin target) :
    WordVertexPath.Path (fun index => OrientedEdge.map map (edges index)) word (map first) (map last) := by
  induction path with
  | nil => exact .nil _
  | @cons letter tail finish path ih =>
      have same := Vertices.SignedGenerator.vertexEdge_map edges map letter
      apply PathEndpoints.castStart (congrArg OrientedEdge.start same)
      exact .cons (ih.castStart (congrArg OrientedEdge.finish same).symm)

/-- Executable endpoint readback commutes with mapping the original vertex bank. -/
theorem endpoint_map {target : Nat} (edges : Fin count → Stokes.OrientedEdge size) (map : Fin size → Fin target)
    (word : List (SignedWord.SignedGenerator count)) (first : Fin size) :
    WordVertexPath.endpoint (fun index => OrientedEdge.map map (edges index)) word (map first) = map
      (WordVertexPath.endpoint edges word first) := by
  induction word generalizing first with
  | nil => rfl
  | cons letter tail ih =>
      rw [WordVertexPath.endpoint, WordVertexPath.endpoint, Vertices.SignedGenerator.vertexEdge_map]
      exact ih _

end

/-- Edge assignments agreeing on the original word have equal endpoint readbacks. -/
theorem endpoint_congr {first last : Fin count → Stokes.OrientedEdge size} (word : List (SignedWord.SignedGenerator
  count))
    (same : ∀ letter ∈ word, first letter.index = last letter.index) (start : Fin size) :
    WordVertexPath.endpoint first word start = WordVertexPath.endpoint last word start := by
  induction word generalizing start with
  | nil => rfl
  | cons letter tail ih =>
      rw [WordVertexPath.endpoint, WordVertexPath.endpoint, Vertices.SignedGenerator.vertexEdge_congr letter (same
        letter List.mem_cons_self)]
      exact ih (fun entry member => same entry (List.mem_cons_of_mem _ member)) _

open Purelib.Topology.Surface.Word.Vertices.WordVertexPath in
/-- An occurrence-preserving vertex map transports the exact endpoint of the original word. -/
theorem endpoint_respects {target : Nat} (first : Fin count → Stokes.OrientedEdge size)
    (last : Fin count → Stokes.OrientedEdge target) (map : Fin size → Fin target) (word : List
      (SignedWord.SignedGenerator count))
    (same : ∀ letter ∈ word, OrientedEdge.map map (first letter.index) = last letter.index) (start : Fin size) :
    map (WordVertexPath.endpoint first word start) = WordVertexPath.endpoint last word (map start) :=
  (WordVertexPath.endpoint_map first map word start).symm.trans (WordVertexPath.endpoint_congr word same _)

/-- Every endpoint encountered in a prefix is either its initial vertex or a displayed generator endpoint. This includes
empty segments. -/
theorem endpoint_supported (edges : Fin count → Stokes.OrientedEdge size) (word : List (SignedWord.SignedGenerator
  count)) (first : Fin size) :
    WordVertexPath.endpoint edges word first = first ∨
      ∃ letter ∈ word, WordVertexPath.endpoint edges word first = (edges letter.index).start ∨
        WordVertexPath.endpoint edges word first = (edges letter.index).finish := by
  induction word generalizing first with
  | nil => exact .inl rfl
  | cons letter tail ih =>
      rcases ih (Vertices.SignedGenerator.vertexEdge edges letter).finish with same | present
      · apply Or.inr
        refine ⟨letter, List.mem_cons_self, ?_⟩
        change WordVertexPath.endpoint edges tail (Vertices.SignedGenerator.vertexEdge edges letter).finish = _ ∨
          WordVertexPath.endpoint edges tail (Vertices.SignedGenerator.vertexEdge edges letter).finish = _
        rw [same]
        cases letter with
        | mk index reversed => cases reversed
                               · exact .inr rfl
                               · exact .inl rfl
      · rcases present with ⟨entry, member, endpointEq⟩
        exact .inr ⟨entry, List.mem_cons_of_mem _ member, endpointEq⟩

end WordVertexPath

variable {count : Nat}

set_option genInjectivity false in
/-- A finite endpoint assignment realizing the signed word as a closed anchored path. -/
structure WordVertexRealization (word : List (SignedWord.SignedGenerator count)) (size : Nat) where
  /-- Cached oriented generator edges on the original finite vertex bank. -/ edges : Data.Vector
    (Stokes.OrientedEdge size) count
  /-- Retained starting and finishing vertex of the closed signed word. -/ anchor : Fin size
  /-- The actual signed word follows the retained edges back to its anchor. -/ closed : Vertices.WordVertexPath.Path
    edges word anchor anchor

constructive_injectivity WordVertexRealization

namespace WordVertexRealization

variable {word : List (SignedWord.SignedGenerator count)} {size target : Nat}

/-- Map a realization to another finite vertex bank while retaining its exact closed word. -/
@[expose] def map (model : Vertices.WordVertexRealization word size) (vertices : Fin size → Fin target) :
  Vertices.WordVertexRealization word target where
  edges := Data.Vector.Basic.vectorOfFn fun index => OrientedEdge.map vertices (model.edges index)
  anchor := vertices model.anchor
  closed := Vertices.WordVertexPath.congr (Vertices.WordVertexPath.map model.closed vertices)
    (fun letter _ => (Data.Vector.Basic.vectorOfFn_apply (fun index => OrientedEdge.map vertices (model.edges index))
      letter.index).symm)

/-- A vertex is the retained anchor or an endpoint of an actual word occurrence. -/
@[expose] def Supported (model : Vertices.WordVertexRealization word size) (vertex : Fin size) : Prop :=
  vertex = model.anchor ∨ ∃ letter ∈ word,
    vertex = (model.edges letter.index).start ∨ vertex = (model.edges letter.index).finish

/-- Traversing a retained subword from a supported vertex ends at a supported vertex. -/
theorem supported_endpoint (model : Vertices.WordVertexRealization word size) (part : List (SignedWord.SignedGenerator
  count))
    (included : ∀ letter ∈ part, letter ∈ word) {first : Fin size} (supported : model.Supported first) :
    model.Supported (Vertices.WordVertexPath.endpoint model.edges part first) := by
  rcases Vertices.WordVertexPath.endpoint_supported model.edges part first with same | ⟨letter, member, same⟩
  · rw [same]; exact supported
  · exact .inr ⟨letter, included letter member, same⟩

set_option genInjectivity false in
/-- Pointwise edge readback avoids any function-extensionality axiom. -/
structure Factor (model : Vertices.WordVertexRealization word size) (other : Vertices.WordVertexRealization word target)
  where
  /-- Executable map between the two original finite vertex banks. -/ vertices : Fin size → Fin target
  /-- The factor sends the retained original anchor to the target anchor. -/ anchor_eq : vertices model.anchor =
    other.anchor
  /-- Each original signed occurrence retains its generator edge under the factor map. -/ edge_eq : ∀ letter ∈ word,
    OrientedEdge.map vertices (model.edges letter.index) = other.edges letter.index

constructive_injectivity Factor

/-- The identity vertex map factors a realization through itself. -/
@[expose] def Factor.identity (model : Vertices.WordVertexRealization word size) : model.Factor model where
  vertices := fun vertex => vertex
  anchor_eq := rfl
  edge_eq := fun _ _ => rfl

/-- Compose two original-word factor maps with their anchor and occurrence readbacks. -/
@[expose] def Factor.comp {third : Nat} {first : Vertices.WordVertexRealization word size} {middle :
  Vertices.WordVertexRealization word target}
    {last : Vertices.WordVertexRealization word third} (left : first.Factor middle) (right : middle.Factor last) :
      first.Factor last where
  vertices := fun vertex => right.vertices (left.vertices vertex)
  anchor_eq := by rw [left.anchor_eq, right.anchor_eq]
  edge_eq := fun letter member => by
    rw [← OrientedEdge.map_comp, left.edge_eq letter member, right.edge_eq letter member]

/-- Coverage makes any two factor maps agree pointwise on the complete vertex bank. -/
theorem Factor.unique {model : Vertices.WordVertexRealization word size} {other : Vertices.WordVertexRealization word
  target}
    (covered : ∀ vertex, model.Supported vertex) (first last : model.Factor other) (vertex : Fin size) :
    first.vertices vertex = last.vertices vertex := by
  rcases covered vertex with same | ⟨letter, member, same | same⟩
  · rw [same, first.anchor_eq, last.anchor_eq]
  · rw [same]
    exact (congrArg OrientedEdge.start (first.edge_eq letter member)).trans
      (congrArg OrientedEdge.start (last.edge_eq letter member)).symm
  · rw [same]
    exact (congrArg OrientedEdge.finish (first.edge_eq letter member)).trans
      (congrArg OrientedEdge.finish (last.edge_eq letter member)).symm

end WordVertexRealization

set_option genInjectivity false in
/-- The finite vertex presentation of a polygon word. `lift` is executable factorization, not an assumed count or a
choice-derived quotient. -/
structure WordVertexModel (word : List (SignedWord.SignedGenerator count)) (size : Nat)
    extends Vertices.WordVertexRealization word size where
  /-- Every vertex is the anchor or an endpoint used by the original signed word. -/ covered : ∀ vertex,
    toWordVertexRealization.Supported vertex
  /-- Executable factorization into any other finite realization of this exact word. -/ lift : ∀ {target : Nat} (other :
    Vertices.WordVertexRealization word target), toWordVertexRealization.Factor other

constructive_injectivity WordVertexModel

namespace WordVertexModel

/-- The universal empty-word realization with its single retained anchor vertex. -/
@[expose] def empty : Vertices.WordVertexModel ([] : List (SignedWord.SignedGenerator count)) 1 where
  edges := Data.Vector.Basic.vectorOfFn fun _ => ⟨0, 0⟩
  anchor := 0
  closed := .nil _
  covered := fun vertex => .inl (Fin.ext (by omega))
  lift := fun other =>
    { vertices := fun _ => other.anchor
      anchor_eq := rfl
      edge_eq := fun _ member => nomatch member }

/-- Universal factorization between two covered models is injective on their original vertex banks. -/
theorem lift_injective {word : List (SignedWord.SignedGenerator count)} {size target : Nat}
    (model : Vertices.WordVertexModel word size) (other : Vertices.WordVertexModel word target) :
    Function.Injective (model.lift other.toWordVertexRealization).vertices := by
  let forward := model.lift other.toWordVertexRealization
  let backward := other.lift model.toWordVertexRealization
  have inverse (vertex : Fin size) := (forward.comp backward).unique model.covered
    (.identity model.toWordVertexRealization) vertex
  intro first last same
  exact (inverse first).symm.trans ((congrArg backward.vertices same).trans (inverse last))

/-- An injective finite vertex map has a duplicate-free executable value table. -/
private theorem finTable_nodup {size target : Nat} (map : Fin size → Fin target)
    (injective : Function.Injective map) : (List.ofFn map).Nodup := by
  induction size with
  | zero => exact List.nodup_nil
  | succ size ih =>
      rw [OfFn.Basic.ofFn_succ]
      apply List.pairwise_cons.mpr
      constructor
      · intro other member same
        obtain ⟨index, equal⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
        have impossible := congrArg Fin.val (injective (same.trans equal.symm))
        change 0 = index.val + 1 at impossible
        omega
      · exact ih (fun index => map index.succ) (fun _ _ equal =>
          Fin.ext (Nat.succ.inj (congrArg Fin.val (injective equal))))

/-- An injective map between explicit finite vertex banks bounds their sizes. -/
private theorem size_le_of_injective {size target : Nat} (map : Fin size → Fin target)
    (injective : Function.Injective map) : size ≤ target := by
  have bound := Nodup.nodup_length_le_of_mem (WordVertexModel.finTable_nodup map injective)
    (WordVertexModel.finTable_nodup (fun index : Fin target => index) (fun _ _ same => same))
    (fun index _ => Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩)
  simpa only [OfFn.Basic.length_ofFn] using bound

/-- Mutual executable factorization proves the exact number of vertices. Coverage is essential: without it, arbitrary
unused slots could be added. -/
theorem size_eq {word : List (SignedWord.SignedGenerator count)} {size target : Nat}
    (model : Vertices.WordVertexModel word size) (other : Vertices.WordVertexModel word target) : size = target :=
  Nat.le_antisymm (WordVertexModel.size_le_of_injective _ (model.lift_injective other))
    (WordVertexModel.size_le_of_injective _ (other.lift_injective model))

/-- Transport a universal vertex model across an exact word equality. -/
@[expose] def castWord {first last : List (SignedWord.SignedGenerator count)} {size : Nat} (same : first = last)
    (model : Vertices.WordVertexModel first size) : Vertices.WordVertexModel last size := by
  cases same
  exact model

end WordVertexModel
end Purelib.Topology.Surface.Word.Vertices

end
