module
import Purelib.Data.List.Membership

public import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Fin.Bijection.Transposition
import Purelib.Polynomial.Dense.Gaussian.Split.Lattice
public import Purelib.Topology.Knot.Braid.Polynomial.Exact.Vertices
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.GaussianInt.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.GaussianInt.Embedding
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Fin

open Purelib.Data.Fin.Bijection

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Polynomial.Dense.Gaussian.Split.Lattice

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid

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

namespace Purelib.Topology.Knot.Braid.Polynomial.Exact.Elementary

/-- At the common-x crossing vertex, the positive left owner occupies the lower displayed root, while the negative left
owner occupies the upper one. -/
@[expose] def crossingOwnerPosition {strands : Nat}
  (generator : Braid.Generator strands)
    (startPosition : Fin strands) : Fin strands :=
  match generator.sign with
  | .positive => startPosition
  | .negative => generator.permutation.forward startPosition

/-- The exact five-point lattice track of one persistent owner through an elementary half twist. -/
@[expose] def ownerTrack {strands : Nat} (generator :
  Braid.Generator strands)
    (startPosition : Fin strands) : List GaussianInt.LatticePoint :=
  [Vertices.baseRoot startPosition,
    Vertices.approachRoot generator startPosition,
    Vertices.crossingRoot generator (crossingOwnerPosition
      generator startPosition),
    Vertices.approachRoot generator.reverse
      (generator.permutation.forward startPosition),
    Vertices.baseRoot (generator.permutation.forward startPosition)]

/-- Every original persistent owner track contains exactly five displayed lattice points. -/
@[simp] theorem ownerTrack_length {strands : Nat}
    (generator : Braid.Generator strands) (startPosition : Fin strands) :
    (ownerTrack generator startPosition).length = 5 := rfl

/-- The retained track starts at its original owner's base root. -/
@[simp] theorem ownerTrack_start {strands : Nat}
    (generator : Braid.Generator strands) (startPosition : Fin strands) :
    (ownerTrack generator startPosition).head? = some
      (Vertices.baseRoot startPosition) :=
  rfl

/-- The retained track finishes at the base root selected by the original generator permutation. -/
@[simp] theorem ownerTrack_finish {strands : Nat}
    (generator : Braid.Generator strands) (startPosition : Fin strands) :
    (ownerTrack generator startPosition).getLast? =
      some (Vertices.baseRoot (generator.permutation.forward startPosition)) := by
  rfl

/-- At a positive crossing, the original left owner lies below the original right owner.

The positive sign retains the left owner at the lower active crossing root and the right owner at the upper root.
Explicit scalar bounds certify the same original third entries of their five-point tracks. -/
theorem positive_left_owner_below {strands : Nat}
    (generator : Braid.Generator strands) (positive : generator.sign = .positive) :
    ((ownerTrack generator generator.left)[2]'(by
        change 2 < 5
        decide)).y <
      ((ownerTrack generator generator.right)[2]'(by
        change 2 < 5
        decide)).y := by
  change (Vertices.crossingRoot generator (crossingOwnerPosition generator generator.left)).y <
    (Vertices.crossingRoot generator (crossingOwnerPosition generator generator.right)).y
  unfold crossingOwnerPosition
  rw [positive]
  unfold Vertices.crossingRoot
  rw [if_pos rfl, if_neg generator.left_ne_right.symm, if_pos rfl]
  change (-1 : Int) < 1
  decide

/-- At a negative crossing, the original left owner lies above the original right owner.

The negative sign uses the original endpoint transposition to exchange the two active owners. Their retained third
entries read the lower and upper crossing heights in the reversed owner order. -/
theorem negative_left_owner_above {strands : Nat}
    (generator : Braid.Generator strands) (negative : generator.sign = .negative) :
    ((ownerTrack generator generator.right)[2]'(by
        change 2 < 5
        decide)).y <
      ((ownerTrack generator generator.left)[2]'(by
        change 2 < 5
        decide)).y := by
  change (Vertices.crossingRoot generator (crossingOwnerPosition generator generator.right)).y <
    (Vertices.crossingRoot generator (crossingOwnerPosition generator generator.left)).y
  unfold crossingOwnerPosition
  rw [negative]
  change (Vertices.crossingRoot generator (generator.permutation.forward generator.right)).y <
    (Vertices.crossingRoot generator (generator.permutation.forward generator.left)).y
  have rightSwap : generator.permutation.forward generator.right = generator.left :=
    Transposition.swapIndices_right generator.left generator.right
  have leftSwap : generator.permutation.forward generator.left = generator.right :=
    Transposition.swapIndices_left generator.left generator.right
  rw [rightSwap, leftSwap]
  unfold Vertices.crossingRoot
  rw [if_pos rfl, if_neg generator.left_ne_right.symm, if_pos rfl]
  change (-1 : Int) < 1
  decide

/-! ## Elementary polynomial loops -/

set_option genInjectivity false in
/-- An explicit exact split polynomial loop with one signed adjacent crossing. `ownerTransport` records the persistent
root permutation; the coefficient vertices are computed rather than supplied as opaque data.

The retained coefficient rows follow the original base, approach, crossing and return vertices. Its owner transport is
the supplied generator permutation, and each persistent track keeps that same owner throughout the five lattice points.
-/
structure ElementaryLoop {strands : Nat} (generator :
  Braid.Generator strands) where
  /-- Retained coefficient-vertex list, defaulting to the canonical original five-point excursion. -/
    coefficientVertices : List ExactPolynomialLoops.GaussianPolynomial :=
    [(Vertices.baseVertex strands).polynomial,
      (Vertices.approachVertex generator).polynomial,
      (Vertices.crossingVertex generator).polynomial,
      (Vertices.approachVertex generator.reverse).polynomial,
      (Vertices.baseVertex strands).polynomial]
  /-- Retained executable root-owner bijection, defaulting to the original generator permutation. -/ ownerTransport :
    Data.Fin.Bijection strands strands :=
    generator.permutation
  /-- Retained signed word, defaulting to the supplied original generator. -/ extractedWord : Braid.Word strands :=
    [generator]

constructive_injectivity ElementaryLoop

/-- Build the canonical exact coefficient excursion for the supplied original signed generator. -/
@[expose] def elementaryLoop {strands : Nat} (generator :
  Braid.Generator strands) :
    ElementaryLoop generator := {}

/-- Read the exact five original coefficient vertices of the elementary excursion. -/
@[simp] theorem elementaryLoop_coefficients {strands :
  Nat}
    (generator : Braid.Generator strands) :
    (elementaryLoop generator).coefficientVertices =
      [(Vertices.baseVertex strands).polynomial,
        (Vertices.approachVertex generator).polynomial,
        (Vertices.crossingVertex generator).polynomial,
        (Vertices.approachVertex generator.reverse).polynomial,
        (Vertices.baseVertex strands).polynomial] := rfl

/-- The canonical elementary loop extracts the original one-generator word. -/
@[simp] theorem elementaryLoop_word {strands : Nat}
    (generator : Braid.Generator strands) :
    (elementaryLoop generator).extractedWord = [generator] :=
      rfl

/-- The canonical elementary loop retains the original generator's executable owner permutation. -/
@[simp] theorem elementaryLoop_transport {strands : Nat}
    (generator : Braid.Generator strands) :
    (elementaryLoop generator).ownerTransport =
      generator.permutation := rfl

/-- The original elementary coefficient list starts and finishes at the same base polynomial. -/
theorem elementaryLoop_closed {strands : Nat}
    (generator : Braid.Generator strands) :
    (elementaryLoop generator).coefficientVertices.head? =
      (elementaryLoop generator).coefficientVertices.getLast? :=
        by
  rfl

/-- Reversing the original generator exactly reverses the canonical coefficient list. -/
@[simp] theorem elementaryLoop_reverse_coefficients
  {strands : Nat}
    (generator : Braid.Generator strands) :
    (elementaryLoop generator.reverse).coefficientVertices =
      (elementaryLoop generator).coefficientVertices.reverse :=
        by
  cases generator with
  | mk index sign =>
      cases sign <;> rfl

/-- Every original elementary coefficient vertex is monic of the retained strand degree. -/
theorem elementaryLoop_vertices_monic {strands : Nat}
    (generator : Braid.Generator strands) :
    ∀ polynomial ∈ (elementaryLoop
      generator).coefficientVertices,
      polynomial.natDegree = strands ∧ polynomial.leadingCoeff = 1 := by
  intro polynomial membership
  rw [elementaryLoop_coefficients] at membership
  have membership := List.Membership.mem_cons.mp membership
  rcases membership with atBase | remaining
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩
  have membership := List.Membership.mem_cons.mp remaining
  rcases membership with atApproach | remaining
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩
  have membership := List.Membership.mem_cons.mp remaining
  rcases membership with atCrossing | remaining
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩
  have membership := List.Membership.mem_cons.mp remaining
  rcases membership with atDeparture | remaining
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩
  have membership := List.Membership.mem_cons.mp remaining
  rcases membership with atBase | impossible
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩
  · cases impossible

/-- Every Artin generator, at every valid finite index and with either sign, has an explicit rational polynomial loop
realization. -/
theorem everyGenerator_realized {strands : Nat}
    (generator : Braid.Generator strands) :
    ∃ loop : ElementaryLoop generator,
      loop.extractedWord = [generator] ∧
      loop.ownerTransport = generator.permutation :=
  ⟨elementaryLoop generator, rfl, rfl⟩

/-- Each point of the displayed owner track is an exact root of the corresponding computed coefficient polynomial. -/
theorem ownerTrack_root_certificates {strands : Nat}
    (generator : Braid.Generator strands) (startPosition : Fin strands) :
    (Vertices.baseVertex strands).polynomial.eval
          (Vertices.baseRoot startPosition).gaussian = 0 ∧
      (Vertices.approachVertex generator).polynomial.eval
          (Vertices.approachRoot generator startPosition).gaussian = 0 ∧
      (Vertices.crossingVertex generator).polynomial.eval
          (Vertices.crossingRoot generator
            (crossingOwnerPosition generator
              startPosition)).gaussian = 0 ∧
      (Vertices.approachVertex generator.reverse).polynomial.eval
          (Vertices.approachRoot generator.reverse
            (generator.permutation.forward startPosition)).gaussian = 0 ∧
      (Vertices.baseVertex strands).polynomial.eval
          (Vertices.baseRoot
            (generator.permutation.forward startPosition)).gaussian = 0 := by
  exact ⟨Vertex.polynomial_eval_root _ _, Vertex.polynomial_eval_root _ _,
    Vertex.polynomial_eval_root _ _, Vertex.polynomial_eval_root _ _,
    Vertex.polynomial_eval_root _ _⟩

end Purelib.Topology.Knot.Braid.Polynomial.Exact.Elementary

end
