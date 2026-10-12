module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append

import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.List.Map
import Purelib.Polynomial.Dense.Gaussian.Split.Lattice
public import Purelib.Topology.Knot.Braid.Polynomial.Exact.Elementary
import Purelib.Topology.Knot.Braid.Polynomial.Exact.Vertices
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Fin

open Purelib.Data.List

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Polynomial.Dense.Gaussian.Split

open Purelib.Polynomial.Dense.Gaussian.Split.Lattice

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid.Polynomial.Exact

section
public section

/-!
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

namespace Purelib.Topology.Knot.Braid.Polynomial.Exact.Word

/-! ## Exact realization of arbitrary finite words -/

/-- The four noninitial vertices contributed by one generator excursion. -/
@[expose] def excursionVertices {strands : Nat}
    (generator : Braid.Generator strands) : List (Lattice.Vertex strands) :=
  [Vertices.approachVertex generator, Vertices.crossingVertex generator,
    Vertices.approachVertex generator.reverse, Vertices.baseVertex strands]

/-- Concatenate the exact coefficient excursions for a displayed word. -/
@[expose] def wordVertices {strands : Nat} (word : Braid.Word
  strands) :
    List (Lattice.Vertex strands) :=
  Vertices.baseVertex strands :: word.flatMap excursionVertices

/-- Concatenate the explicit persistent-owner tracks, omitting the repeated base point at each join. -/
@[expose] def wordOwnerTrack {strands : Nat} :
    Braid.Word strands → Fin strands → List GaussianInt.LatticePoint
  | [], startPosition => [Vertices.baseRoot startPosition]
  | generator :: remaining, startPosition =>
      (Elementary.ownerTrack generator startPosition).dropLast ++
        wordOwnerTrack remaining
          (generator.permutation.forward startPosition)

/-- The empty original braid word retains only the owner's initial base root. -/
@[simp] theorem wordOwnerTrack_nil {strands : Nat}
    (startPosition : Fin strands) :
    wordOwnerTrack [] startPosition = [Vertices.baseRoot
      startPosition] := rfl

/-- One original elementary track contributes four points after omitting its final join point. -/
@[simp] theorem ownerTrack_dropLast_length {strands : Nat}
    (generator : Braid.Generator strands) (startPosition : Fin strands) :
    (Elementary.ownerTrack generator startPosition).dropLast.length = 4 := rfl

/-- The original owner track has four points per generator plus its retained endpoint. -/
@[simp] theorem wordOwnerTrack_length {strands : Nat}
    (word : Braid.Word strands) (startPosition : Fin strands) :
    (wordOwnerTrack word startPosition).length = 4 * word.length + 1
      := by
  induction word generalizing startPosition with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      rw [wordOwnerTrack, List.Append.length_append, ownerTrack_dropLast_length,
        inductionHypothesis]
      simp only [List.length_cons, -eq_self, -iff_self]
      omega

/-- Every original word owner track contains its initial point. -/
theorem wordOwnerTrack_nonempty {strands : Nat}
    (word : Braid.Word strands) (startPosition : Fin strands) :
    wordOwnerTrack word startPosition ≠ [] := by
  intro empty
  have lengthPositive : 0 < (wordOwnerTrack word startPosition).length := by
    rw [wordOwnerTrack_length]
    omega
  rw [empty] at lengthPositive
  exact (Nat.lt_irrefl 0 lengthPositive).elim

/-- The original word owner track starts at its supplied base root. -/
@[simp] theorem wordOwnerTrack_head {strands : Nat}
    (word : Braid.Word strands) (startPosition : Fin strands) :
    (wordOwnerTrack word startPosition).head? =
      some (Vertices.baseRoot startPosition) := by
  cases word with
  | nil => rfl
  | cons generator remaining => rfl

/-- The original word owner track finishes at the base root selected by the executable word permutation. -/
@[simp] theorem wordOwnerTrack_finish {strands : Nat}
    (word : Braid.Word strands) (startPosition : Fin strands) :
    (wordOwnerTrack word startPosition).getLast? =
      some (Vertices.baseRoot (word.permutation.forward startPosition)) := by
  induction word generalizing startPosition with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      rw [wordOwnerTrack,
        List.Append.getLast_append_nonempty
          (Elementary.ownerTrack generator startPosition).dropLast
          (wordOwnerTrack_nonempty remaining
            (generator.permutation.forward startPosition)),
        inductionHypothesis]
      rfl

set_option genInjectivity false in
/-- A completely explicit rational polynomial loop realizing a finite Artin word. Every coefficient row is computed from
a pairwise-distinct root table, and the persistent owner transport is executable.

The displayed word determines the original excursion order, coefficient list and endpoint permutation. Defaults retain
those computed tables and persistent owner tracks rather than substituting another realization. -/
structure RealizedLoop {strands : Nat} (word : Braid.Word
  strands) where
  /-- Retained exact lattice vertices, defaulting to the original computed word excursions. -/ vertices : List
    (Lattice.Vertex strands) := wordVertices word
  /-- Retained coefficient list, defaulting to the polynomial reading of those lattice vertices. -/ coefficientVertices
    : List ExactPolynomialLoops.GaussianPolynomial :=
    vertices.map Vertex.polynomial
  /-- Retained executable owner transport, defaulting to the original word permutation. -/ ownerTransport :
    Data.Fin.Bijection strands strands :=
    word.permutation
  /-- Retained persistent-owner lattice tracks, defaulting to the original computed word tracks. -/ ownerTracks : Fin
    strands → List GaussianInt.LatticePoint := wordOwnerTrack
    word
  /-- Retained extracted signed word, defaulting to the original input word. -/ extractedWord : Braid.Word strands :=
    word

constructive_injectivity RealizedLoop

/-- Build the canonical exact coefficient loop and owner tracks for the supplied original finite word. -/
@[expose] def realizeWord {strands : Nat} (word : Braid.Word
  strands) : RealizedLoop word := {}

/-- The canonical realization retains the original computed vertex excursions. -/
@[simp] theorem realizeWord_vertices {strands : Nat} (word :
  Braid.Word strands) :
    (realizeWord word).vertices =
      wordVertices word := rfl

/-- Its coefficient list is the polynomial reading of the original computed lattice vertices. -/
@[simp] theorem realizeWord_coefficients {strands : Nat}
    (word : Braid.Word strands) :
    (realizeWord word).coefficientVertices =
      (wordVertices word).map Vertex.polynomial := rfl

/-- The canonical loop extracts the exact original supplied word. -/
@[simp] theorem realizeWord_extractedWord {strands : Nat}
    (word : Braid.Word strands) : (realizeWord word).extractedWord =
      word := rfl

/-- The canonical loop's owner transport is the original executable word permutation. -/
@[simp] theorem realizeWord_ownerTransport {strands : Nat}
    (word : Braid.Word strands) :
    (realizeWord word).ownerTransport = word.permutation := rfl

/-- Each canonical owner track ends at its original retained transported base root. -/
@[simp] theorem realizeWord_ownerTrack_finish {strands : Nat}
    (word : Braid.Word strands) (startPosition : Fin strands) :
    ((realizeWord word).ownerTracks startPosition).getLast? =
      some (Vertices.baseRoot
        ((realizeWord word).ownerTransport.forward startPosition)) :=
  wordOwnerTrack_finish word startPosition

/-- One original generator contributes exactly four noninitial lattice vertices. -/
@[simp] theorem excursionVertices_length {strands : Nat}
    (generator : Braid.Generator strands) :
    (excursionVertices generator).length = 4 := rfl

/-- The original vertex list has four vertices per generator plus its common base point. -/
@[simp] theorem wordVertices_length {strands : Nat} (word :
  Braid.Word strands) :
    (wordVertices word).length = 4 * word.length + 1 := by
  induction word with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      change
        (Vertices.baseVertex strands ::
          (excursionVertices generator ++
            remaining.flatMap excursionVertices)).length =
          4 * (generator :: remaining).length + 1
      change
        (Vertices.baseVertex strands ::
          remaining.flatMap excursionVertices).length =
          4 * remaining.length + 1 at inductionHypothesis
      simp only [List.length_cons, -eq_self, -iff_self] at inductionHypothesis
      simp only [List.length_cons, List.Append.length_append,
        excursionVertices_length, -eq_self, -iff_self]
      omega

/-- The canonical original coefficient loop has four vertices per generator plus one. -/
@[simp] theorem realizeWord_coefficientCount {strands : Nat}
    (word : Braid.Word strands) :
    (realizeWord word).coefficientVertices.length = 4 * word.length +
      1 := by
  change ((wordVertices word).map Vertex.polynomial).length = 4 * word.length + 1
  exact (List.Map.length_map Vertex.polynomial (wordVertices word)).trans (wordVertices_length word)

/-- Every original realized coefficient vertex is monic of the retained strand degree.

Each displayed coefficient comes from an original lattice vertex and its retained finite root table. The exact
split-product certificates give degree equal to the strand count and leading coefficient one. -/
theorem realizeWord_vertices_monic {strands : Nat} (word :
  Braid.Word strands) :
    ∀ polynomial ∈ (realizeWord word).coefficientVertices,
      polynomial.natDegree = strands ∧ polynomial.leadingCoeff = 1 := by
  intro polynomial membership
  rw [realizeWord_coefficients] at membership
  have membership := Map.mem_map.mp membership
  obtain ⟨vertex, vertexMembership, rfl⟩ := membership
  exact ⟨Vertex.polynomial_natDegree vertex,
    Vertex.polynomial_leadingCoeff vertex⟩

/-- The original word vertex list begins at the canonical base vertex. -/
@[simp] theorem wordVertices_head {strands : Nat} (word :
  Braid.Word strands) :
    (wordVertices word).head? = some (Vertices.baseVertex strands) :=
      rfl

/-- Each original generator excursion returns to the canonical base vertex. -/
theorem excursionVertices_getLast {strands : Nat}
    (generator : Braid.Generator strands) :
    (excursionVertices generator).getLast? = some (Vertices.baseVertex
      strands) := rfl

/-- A nonempty original excursion list ends at the canonical base vertex. -/
theorem flatMap_excursions_getLast {strands : Nat}
    (word : Braid.Word strands) (nonempty : word ≠ []) :
    (word.flatMap excursionVertices).getLast? = some
      (Vertices.baseVertex strands) := by
  induction word with
  | nil => exact (nonempty rfl).elim
  | cons generator remaining inductionHypothesis =>
      by_cases remainingEmpty : remaining = []
      · subst remaining
        rfl
      · rw [List.Flatten.flatMap_cons,
          List.Append.getLast_append_nonempty (excursionVertices generator)]
        · exact inductionHypothesis remainingEmpty
        · cases remaining with
          | nil => contradiction
          | cons head tail =>
              intro empty
              change (_ :: _) = [] at empty
              cases empty

/-- The complete original word vertex list ends at the canonical base vertex. -/
@[simp] theorem wordVertices_getLast {strands : Nat} (word :
  Braid.Word strands) :
    (wordVertices word).getLast? = some (Vertices.baseVertex strands)
      := by
  by_cases empty : word = []
  · subst word
    rfl
  · unfold wordVertices
    change ([Vertices.baseVertex strands] ++ word.flatMap excursionVertices).getLast? =
      some (Vertices.baseVertex strands)
    rw [List.Append.getLast_append_nonempty [Vertices.baseVertex strands]]
    · exact flatMap_excursions_getLast word empty
    · intro flattenedEmpty
      have last := flatMap_excursions_getLast word empty
      rw [flattenedEmpty] at last
      contradiction

/-- The canonical original coefficient loop begins and ends at the same polynomial.

The first coefficient is the original base polynomial. Every finite generator excursion ends at that same polynomial,
including the empty word whose coefficient list contains only the base. -/
theorem realizeWord_closed {strands : Nat} (word : Braid.Word
  strands) :
    (realizeWord word).coefficientVertices.head? =
      (realizeWord word).coefficientVertices.getLast? := by
  have lastCoefficient : ∀ (retained : Braid.Word strands), retained ≠ [] →
      ((retained.flatMap excursionVertices).map Vertex.polynomial).getLast? =
        some (Vertices.baseVertex strands).polynomial := by
    intro retained nonempty
    induction retained with
    | nil => exact False.elim (nonempty rfl)
    | cons generator remaining ih =>
        change ((excursionVertices generator ++ remaining.flatMap excursionVertices).map
          Vertex.polynomial).getLast? = _
        rw [List.Map.map_append]
        cases remaining with
        | nil => rfl
        | cons next tail =>
            rw [List.Append.getLast_append_nonempty _ (by
              change (_ :: _) ≠ []
              intro impossible
              cases impossible)]
            exact ih (by intro impossible; cases impossible)
  cases word with
  | nil => rfl
  | cons generator remaining =>
      change some (Vertices.baseVertex strands).polynomial =
        ([(Vertices.baseVertex strands).polynomial] ++
          (((generator :: remaining).flatMap excursionVertices).map Vertex.polynomial)).getLast?
      rw [List.Append.getLast_append_nonempty _ (by
        change (_ :: _) ≠ []
        intro impossible
        cases impossible)]
      exact (lastCoefficient _ (by intro impossible; cases impossible)).symm

/-- Strong finite polynomial-space realization theorem: every displayed Artin word has an exact monic split rational
coefficient loop whose extracted word and persistent owner transport are the requested ones. -/
theorem everyWord_realized {strands : Nat} (word : Braid.Word
  strands) :
    ∃ loop : RealizedLoop word,
      loop.extractedWord = word ∧
      loop.ownerTransport = word.permutation ∧
      loop.coefficientVertices.length = 4 * word.length + 1 ∧
      ∀ startPosition : Fin strands,
        (loop.ownerTracks startPosition).getLast? =
          some (Vertices.baseRoot (loop.ownerTransport.forward startPosition)) :=
  ⟨realizeWord word, rfl, rfl, realizeWord_coefficientCount word,
    realizeWord_ownerTrack_finish word⟩

end Purelib.Topology.Knot.Braid.Polynomial.Exact.Word

end
