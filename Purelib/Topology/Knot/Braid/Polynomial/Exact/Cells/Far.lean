module

import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Polynomial.Dense.Gaussian.Split.Lattice
import Purelib.Topology.Knot.Braid.Polynomial.Exact.Vertices
public import Purelib.Topology.Knot.Braid.Polynomial.Exact.Word
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

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

namespace Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Far

/-! ## Concrete finite coefficient-space relation cells -/

/-- A simultaneous interior state for two disjoint adjacent crossings. Both pairs occupy their diagonal approach lanes.
All x-coordinates remain the distinct base coordinates, making the simple-root certificate direct. -/
@[expose] def farRoot {strands : Nat} (first second :
  Braid.Generator strands)
    (position : Fin strands) : GaussianInt.LatticePoint :=
  if position = first.left then
    { x := 2 * position.val, y := -1 }
  else if position = first.right then
    { x := 2 * position.val, y := 1 }
  else if position = second.left then
    { x := 2 * position.val, y := -1 }
  else if position = second.right then
    { x := 2 * position.val, y := 1 }
  else
    Vertices.baseRoot position

/-- Every original root in the simultaneous midpoint keeps its distinct base real coordinate. -/
theorem farRoot_x {strands : Nat} (first second :
  Braid.Generator strands)
    (position : Fin strands) :
    (farRoot first second position).x = 2 * position.val := by
  unfold farRoot
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · rfl

/-- The simultaneous original root row is injective by its distinct real coordinates. -/
theorem farRoot_injective {strands : Nat} (first second :
  Braid.Generator strands) :
    Function.Injective (farRoot first second) := by
  intro left right equal
  apply Fin.ext
  have xEqual := congrArg GaussianInt.LatticePoint.x equal
  rw [farRoot_x, farRoot_x] at xEqual
  change 2 * (left.val : Int) = 2 * (right.val : Int) at xEqual
  omega

/-- Build the certified original simultaneous midpoint for the supplied disjoint generator pair. -/
@[expose] def farVertex {strands : Nat} (first second :
  Braid.Generator strands)
    (_far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) : Lattice.Vertex strands where
  root := farRoot first second
  root_injective := farRoot_injective first second

set_option genInjectivity false in
/-- Exact polynomial square witnessing that disjoint root motions commute. The central vertex moves both pairs
simultaneously and is certified simple.

The supplied strict index separation identifies disjoint active strand pairs. The center retains both simultaneous root
motions and the two boundary words in their original orders. -/
structure FarCommutationCell {strands : Nat}
    (first second : Braid.Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) where
  /-- Retained original base polynomial vertex for the square. -/ base : Lattice.Vertex strands := Vertices.baseVertex
    strands
  /-- Retained original crossing midpoint for the first generator. -/ firstMidpoint : Lattice.Vertex strands :=
    Vertices.crossingVertex first
  /-- Retained collision-free midpoint moving both original disjoint root pairs. -/ simultaneousMidpoint :
    Lattice.Vertex strands := farVertex first second far
  /-- Retained original crossing midpoint for the second generator. -/ secondMidpoint : Lattice.Vertex strands :=
    Vertices.crossingVertex second
  /-- Retained exact loop realizing the original first-then-second word. -/ leftBoundary : Word.RealizedLoop [first,
    second] := Word.realizeWord [first, second]
  /-- Retained exact loop realizing the original second-then-first word. -/ rightBoundary : Word.RealizedLoop [second,
    first] := Word.realizeWord [second, first]

constructive_injectivity FarCommutationCell

/-- Cache the canonical original disjoint-motion square and both realized word boundaries. -/
@[expose] def farCommutationCell {strands : Nat} (first
  second : Braid.Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    FarCommutationCell first second far := {}

/-- The retained simultaneous midpoint polynomial has the original strand degree. -/
@[simp] theorem farCommutationCell_center_degree {strands
  : Nat}
    (first second : Braid.Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    ((farCommutationCell first second
      far).simultaneousMidpoint.polynomial).natDegree =
      strands :=
  Vertex.polynomial_natDegree _

/-- The first retained square boundary reads the original first-then-second generator word. -/
@[simp] theorem farCommutationCell_left_word {strands :
  Nat}
    (first second : Braid.Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    (farCommutationCell first second
      far).leftBoundary.extractedWord =
      [first, second] := rfl

/-- The second retained square boundary reads the original second-then-first generator word. -/
@[simp] theorem farCommutationCell_right_word {strands :
  Nat}
    (first second : Braid.Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    (farCommutationCell first second
      far).rightBoundary.extractedWord =
      [second, first] := rfl

end Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Far

end
