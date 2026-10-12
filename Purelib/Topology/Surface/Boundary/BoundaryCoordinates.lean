module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Topology.Surface.Cut.BoundaryWord
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.Cast.Defs
import Batteries.Logic
import Purelib.Tactic.Ring

/-!
# Integer coordinates of actual projected boundary walks

Every signed letter is selected from the retained cut alphabet and checked
against the original directed surface edge. The complete ordered word and
its integer totals are cached. One-sided physical-boundary generators stay
in the coordinate vector; no closedness or vanishing claim removes them.
-/

namespace Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib
open Purelib.Topology.Surface.Boundary
open Purelib.Algebra
open Purelib.Data
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.SignedWord

public section

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero sumFin_add sumFin_ite_eq)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutWordEntry CutAlphabet)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)

variable {source target count : Nat} {labels : Fin source → Fin target}
  {boundary : List (Stokes.OrientedEdge source)}

set_option genInjectivity false in
/-- One retained cut-word occurrence realizing a projected edge in either orientation.

Membership ties the occurrence to the original list, and the orientation flag records its exact projected-edge equation.
-/
structure Selected (generators : Data.Vector (Stokes.OrientedEdge source) count)
    (entries : List (BoundaryWord.CutWordEntry labels generators)) (edge : Stokes.OrientedEdge target) where
  /-- Retained original cut-word occurrence realizing the requested edge. -/ entry : BoundaryWord.CutWordEntry labels
    generators
  /-- The selected occurrence belongs to the original entry list. -/ member : entry ∈ entries
  /-- Whether the projected occurrence is traversed in reverse orientation. -/ backwards : Bool
  /-- The selected oriented projection is exactly the requested edge. -/ equation : edge = if backwards then
    (OrientedEdge.map labels entry.edge).reverse else OrientedEdge.map labels entry.edge

constructive_injectivity Selected

/-- Read the selected signed generator, reversing its sign when the projection is traversed backwards. -/
@[expose] def Selected.letter {generators : Data.Vector (Stokes.OrientedEdge source) count}
    {entries : List (BoundaryWord.CutWordEntry labels generators)} {edge : Stokes.OrientedEdge target}
    (selected : BoundaryCoordinates.Selected generators entries edge) : SignedWord.SignedGenerator count :=
  ⟨selected.entry.letter.index,
    if selected.backwards then !selected.entry.letter.reversed else selected.entry.letter.reversed⟩

/-- Read the projected generator edge in the orientation of a signed letter. -/
@[expose] def letterEdge (bank : BoundaryWord.CutAlphabet labels boundary) (letter : SignedWord.SignedGenerator
  bank.count) : Stokes.OrientedEdge target :=
  if letter.reversed then (OrientedEdge.map labels (bank.generators letter.index)).reverse else OrientedEdge.map labels
    (bank.generators letter.index)

/-- The selected signed letter projects to the original requested edge.

The retained orientation flags and the entry projection equation determine the same directed edge for all four flag
combinations. -/
theorem Selected.projected (bank : BoundaryWord.CutAlphabet labels boundary) {edge : Stokes.OrientedEdge target}
    (selected : BoundaryCoordinates.Selected bank.generators bank.entries edge) : edge = BoundaryCoordinates.letterEdge
      bank selected.letter := by
  cases selected with
  | mk entry member backwards equation =>
    refine equation.trans ?_
    rewrite [entry.projected_eq]
    cases backwards <;> cases reversed : entry.letter.reversed
    all_goals dsimp only [Selected.letter, letterEdge]
    all_goals try rewrite [reversed]
    all_goals exact Eq.refl _

/-- Select the first retained cut occurrence realizing an edge or its reverse.

The supplied support witness makes the finite search total and preserves the original occurrence identity. -/
@[expose] def selectProjected (generators : Data.Vector (Stokes.OrientedEdge source) count)
    (edge : Stokes.OrientedEdge target) : (entries : List (BoundaryWord.CutWordEntry labels generators)) →
    (edge ∈ entries.map (fun entry => OrientedEdge.map labels entry.edge) ∨
      edge.reverse ∈ entries.map (fun entry => OrientedEdge.map labels entry.edge)) → BoundaryCoordinates.Selected
        generators entries edge
  | [], member => (member.elim List.not_mem_nil List.not_mem_nil).elim
  | first :: rest, member =>
      if same : edge = OrientedEdge.map labels first.edge then ⟨first, List.mem_cons_self, false, same⟩
      else if backwards : edge = (OrientedEdge.map labels first.edge).reverse then ⟨first, List.mem_cons_self, true,
        backwards⟩
      else
        let remaining : edge ∈ rest.map (fun entry => OrientedEdge.map labels entry.edge) ∨
            edge.reverse ∈ rest.map (fun entry => OrientedEdge.map labels entry.edge) := by
          rcases member with forward | reverse
          · exact Or.inl ((Data.List.Membership.mem_cons.mp forward).resolve_left same)
          · apply Or.inr ((Data.List.Membership.mem_cons.mp reverse).resolve_left ?_)
            intro equal
            apply backwards
            have reversed := congrArg OrientedEdge.reverse equal
            simpa only [OrientedEdge.reverse_reverse] using reversed
        let tail := Purelib.Topology.Surface.Boundary.BoundaryCoordinates.selectProjected generators edge rest remaining
        ⟨tail.entry, List.mem_cons_of_mem _ tail.member, tail.backwards, tail.equation⟩

set_option genInjectivity false in
/-- Exact source-word provenance and its retained integer row. Unlike an area signature, this constructor does not
compute a new quadratic matrix.

The original projected path is recovered from the ordered signed letters, and every cached integral coordinate is
certified against their coefficients. -/
structure WordCoordinates (bank : BoundaryWord.CutAlphabet labels boundary) (path : List (Stokes.OrientedEdge target))
  where
  /-- Cached ordered signed generator word for the projected path. -/ letters : List (SignedWord.SignedGenerator
    bank.count)
  /-- Projecting the cached signed letters recovers the original edge path exactly. -/ projected_eq : letters.map
    (BoundaryCoordinates.letterEdge bank) = path
  /-- Retained integral generator totals of the signed word. -/ totals : Data.Vector Int bank.count
  /-- Each cached total equals the finite sum of the corresponding signed coefficients. -/ totals_eq : ∀ index, totals
    index = Pairing.totalAt (letters.map SignedGenerator.coefficients) index

constructive_injectivity WordCoordinates

namespace WordCoordinates

variable {bank : BoundaryWord.CutAlphabet labels boundary} {path : List (Stokes.OrientedEdge target)}

/-- Reuse already selected cut occurrences, retaining their generator identities instead of searching again after
projection. -/
@[expose] def ofEntries (bank : BoundaryWord.CutAlphabet labels boundary) : (entries : List (BoundaryWord.CutWordEntry
  labels bank.generators)) →
    BoundaryCoordinates.WordCoordinates bank (entries.map (fun entry => OrientedEdge.map labels entry.edge))
  | [] => ⟨[], rfl, Data.Vector.Basic.vectorOfFn fun _ => 0, fun index => Data.Vector.Basic.vectorOfFn_apply _ index⟩
  | entry :: rest =>
      let tail := Purelib.Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.ofEntries bank rest
      ⟨entry.letter :: tail.letters, congrArg₂ List.cons entry.projected_eq.symm tail.projected_eq,
        Data.Vector.Basic.vectorOfFn fun index => entry.letter.coefficients index + tail.totals index,
        fun index => by rw [Data.Vector.Basic.vectorOfFn_apply, tail.totals_eq]; rfl⟩

/-- Reusing retained cut entries preserves their signed generator word exactly. -/
theorem ofEntries_letters (bank : BoundaryWord.CutAlphabet labels boundary) : (entries : List (BoundaryWord.CutWordEntry
  labels bank.generators)) →
    (WordCoordinates.ofEntries bank entries).letters = entries.map CutWordEntry.letter
  | [] => rfl
  | entry :: rest => congrArg (List.cons entry.letter)
    (Purelib.Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.ofEntries_letters bank rest)

/-- Cache signed generator coordinates for a supported projected edge path.

Each edge is matched to an original cut occurrence, while the ordered signed word and its integral totals are retained
together. -/
@[expose] def build (bank : BoundaryWord.CutAlphabet labels boundary) : (path : List (Stokes.OrientedEdge target)) →
    CutPath.Supported (boundary.map (OrientedEdge.map labels)) path → BoundaryCoordinates.WordCoordinates bank path
  | [], _ => ⟨[], rfl, Data.Vector.Basic.vectorOfFn fun _ => 0, fun index => Data.Vector.Basic.vectorOfFn_apply _ index⟩
  | edge :: rest, supported =>
      let first := BoundaryCoordinates.selectProjected bank.generators edge bank.entries (by
        have member := supported edge List.mem_cons_self
        have projectedEntries : bank.entries.map (fun entry => OrientedEdge.map labels entry.edge) = boundary.map
          (OrientedEdge.map labels) := by
          exact (Data.List.Map.map_map (OrientedEdge.map labels) CutWordEntry.edge bank.entries).symm.trans (congrArg
            (List.map (OrientedEdge.map labels)) bank.edges_eq)
        rewrite [projectedEntries]
        exact member)
      let tail := Purelib.Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.build bank rest (fun next member
        => supported next (List.mem_cons_of_mem _ member))
      ⟨first.letter :: tail.letters, congrArg₂ List.cons (first.projected bank).symm tail.projected_eq,
        Data.Vector.Basic.vectorOfFn fun index => first.letter.coefficients index + tail.totals index,
        fun index => by rw [Data.Vector.Basic.vectorOfFn_apply, tail.totals_eq]; rfl⟩

/-- Evaluate a finite integral coefficient row on Gaussian rational generator values. -/
@[expose] def combine {count : Nat} (coefficients : Fin count → Int) (values : Fin count → Gaussian.Basic.Canonical) :
  Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin fun index => (coefficients index : Gaussian.Basic.Canonical) * values index

/-- Adding integral coefficient rows adds their Gaussian rational evaluations.

The finite sum is transported pointwise through the retained integer cast, and distributivity combines its two scalar
evaluations. -/
private theorem combine_add {count : Nat} (first last : Fin count → Int) (values : Fin count → Gaussian.Basic.Canonical)
  :
    WordCoordinates.combine (fun index => first index + last index) values = WordCoordinates.combine first values +
      WordCoordinates.combine last values := by
  exact (FiniteSum.Fin.sumFin_congr (fun index => by rewrite [Algebra.Ring.IntCast.add]; ring1)).trans
    (FiniteSum.Fin.sumFin_add _ _)

/-- A signed generator coefficient row evaluates to its corresponding signed value.

Only the original generator index has a nonzero coefficient. Its retained reversal flag determines the sign of that
scalar value. -/
private theorem combine_letter {count : Nat} (letter : SignedWord.SignedGenerator count) (values : Fin count →
  Gaussian.Basic.Canonical) :
    WordCoordinates.combine letter.coefficients values = if letter.reversed then -values letter.index else values
      letter.index := by
  have expanded : WordCoordinates.combine letter.coefficients values =
      FiniteSum.Fin.sumFin (fun index => if index = letter.index then
        (if letter.reversed then -values index else values index) else 0) := by
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rewrite [SignedGenerator.coefficients, Data.Vector.Basic.vectorOfFn_apply]
    by_cases same : index = letter.index
    · rewrite [if_pos same, if_pos same]
      cases letter.reversed
      · change (1 : Gaussian.Basic.Canonical) * values index = values index
        ring1
      · change (-1 : Gaussian.Basic.Canonical) * values index = -values index
        ring1
    · rewrite [if_neg same, if_neg same]
      change (0 : Gaussian.Basic.Canonical) * values index = 0
      ring1
  exact expanded.trans (FiniteSum.Fin.sumFin_ite_eq letter.index _)

/-- Evaluate a signed generator word by its integral totals and the original projected generators.

Structural induction retains the original word order while adding each signed coefficient to the cached integral totals.
-/
private theorem word_value (bank : BoundaryWord.CutAlphabet labels boundary) (value : Stokes.OrientedEdge target →
  Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) (letters : List (SignedWord.SignedGenerator bank.count)) :
    SewingRetraction.wordValue value (letters.map (BoundaryCoordinates.letterEdge bank)) =
      WordCoordinates.combine (Pairing.totalAt (letters.map SignedGenerator.coefficients))
        (fun index => value (OrientedEdge.map labels (bank.generators index))) := by
  induction letters with
  | nil =>
      change 0 = FiniteSum.Fin.sumFin (fun _ => (0 : Gaussian.Basic.Canonical) * _)
      exact ((FiniteSum.Fin.sumFin_congr (fun _ => zero_mul _)).trans FiniteSum.Fin.sumFin_zero).symm
  | cons letter rest ih =>
      rewrite [List.map_cons, SewingRetraction.wordValue, ih]
      change _ = WordCoordinates.combine (fun index => letter.coefficients index + Pairing.totalAt (rest.map
        SignedGenerator.coefficients) index) _
      rewrite [WordCoordinates.combine_add, WordCoordinates.combine_letter]
      unfold BoundaryCoordinates.letterEdge
      cases letter.reversed
      · exact Eq.refl _
      · exact congrArg (fun head => head + _) (anti _)

/-- Actual edge evaluation equals the stored integer row evaluated on the original projected generators, including all
physical-boundary entries. -/
theorem value_eq (coordinates : BoundaryCoordinates.WordCoordinates bank path) (value : Stokes.OrientedEdge target →
  Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value path = WordCoordinates.combine coordinates.totals (fun index => value
      (OrientedEdge.map labels (bank.generators index))) := by
  refine (congrArg (SewingRetraction.wordValue value) coordinates.projected_eq).symm.trans
    ((WordCoordinates.word_value bank value anti coordinates.letters).trans ?_)
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [coordinates.totals_eq]

open Purelib.Topology.Chain.PathBoundary (PathEndpoints vertexIndicator edgeBoundaryAt wordBoundaryAt)

/-- The boundary operator acts on the cached integer row and the actual projected endpoints, not on abstract generator
names. -/
@[expose] def boundaryAt (coordinates : BoundaryCoordinates.WordCoordinates bank path) (vertex : Fin target) : Int :=
  FiniteSum.Fin.sumFin fun index => coordinates.totals index *
    PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels (bank.generators index))
      vertex

/-- A signed letter's vertex boundary equals its coefficient row applied to generator boundaries.

The single nonzero coordinate keeps the original generator endpoints; reversing the letter reverses the signed incidence
reading. -/
private theorem letter_boundary (bank : BoundaryWord.CutAlphabet labels boundary) (letter : SignedWord.SignedGenerator
  bank.count)
    (vertex : Fin target) :
    PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (BoundaryCoordinates.letterEdge bank letter)
      vertex =
      FiniteSum.Fin.sumFin (fun index => letter.coefficients index *
        PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels (bank.generators
          index)) vertex) := by
  have single : (FiniteSum.Fin.sumFin (fun index => letter.coefficients index *
        PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels (bank.generators
          index)) vertex)) =
      (if letter.reversed then -1 else 1) *
        PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels (bank.generators
          letter.index)) vertex := by
    refine (FiniteSum.Fin.sumFin_congr (fun index => ?_)).trans (FiniteSum.Fin.sumFin_ite_eq letter.index
      (fun index => (if letter.reversed then -1 else 1) *
        PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels (bank.generators
          index)) vertex))
    rewrite [SignedGenerator.coefficients, Data.Vector.Basic.vectorOfFn_apply]
    by_cases same : index = letter.index
    · rewrite [if_pos same, if_pos same]
      exact Eq.refl _
    · rewrite [if_neg same, if_neg same]
      exact zero_mul _
  rewrite [single]
  unfold BoundaryCoordinates.letterEdge
  cases letter.reversed
  · exact (one_mul _).symm
  · change (PathBoundary.vertexIndicator (labels (bank.generators letter.index).start) vertex -
      PathBoundary.vertexIndicator (labels (bank.generators letter.index).finish) vertex) =
        -1 * (PathBoundary.vertexIndicator (labels (bank.generators letter.index).finish) vertex -
          PathBoundary.vertexIndicator (labels (bank.generators letter.index).start) vertex)
    ring1

/-- A signed word's vertex boundary equals its total coefficient row applied to generator boundaries. -/
private theorem word_boundary (bank : BoundaryWord.CutAlphabet labels boundary) (letters : List
  (SignedWord.SignedGenerator bank.count))
    (vertex : Fin target) :
    PathBoundary.wordBoundaryAt OrientedEdge.start OrientedEdge.finish (letters.map (BoundaryCoordinates.letterEdge
      bank)) vertex =
      FiniteSum.Fin.sumFin (fun index => Pairing.totalAt (letters.map SignedGenerator.coefficients) index *
        PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels (bank.generators
          index)) vertex) := by
  induction letters with
  | nil =>
      change 0 = FiniteSum.Fin.sumFin (fun _ => (0 : Int) * _)
      exact ((FiniteSum.Fin.sumFin_congr (fun _ => zero_mul _)).trans FiniteSum.Fin.sumFin_zero).symm
  | cons letter rest ih =>
      rw [List.map_cons, PathBoundary.wordBoundaryAt, WordCoordinates.letter_boundary, ih]
      exact ((FiniteSum.Fin.sumFin_congr (fun index => add_mul _ _ _)).trans (FiniteSum.Fin.sumFin_add _ _)).symm

/-- The cached integral boundary reading equals the original projected path boundary. -/
theorem boundary_eq (coordinates : BoundaryCoordinates.WordCoordinates bank path) (vertex : Fin target) :
    coordinates.boundaryAt vertex = PathBoundary.wordBoundaryAt OrientedEdge.start OrientedEdge.finish path vertex := by
  refine (FiniteSum.Fin.sumFin_congr (fun index => congrArg (· *
    PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels (bank.generators index))
      vertex)
      (coordinates.totals_eq index))).trans ?_
  exact (WordCoordinates.word_boundary bank coordinates.letters vertex).symm.trans
    (congrArg (fun edges => PathBoundary.wordBoundaryAt OrientedEdge.start OrientedEdge.finish edges vertex)
      coordinates.projected_eq)

/-- Every closed actual path yields an integer cycle in the projected incidence matrix. Physical-boundary coordinates
remain in this equation. -/
theorem boundary_zero (coordinates : BoundaryCoordinates.WordCoordinates bank path) {anchor : Fin target}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish path anchor anchor) (vertex : Fin
      target) :
    coordinates.boundaryAt vertex = 0 := by
  rw [coordinates.boundary_eq, PathBoundary.wordBoundaryAt_eq_endpoints closed, sub_self]

end WordCoordinates
end

end Purelib.Topology.Surface.Boundary.BoundaryCoordinates
