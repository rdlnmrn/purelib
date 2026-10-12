module

import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Polynomial.Exact.Elementary
public import Purelib.Topology.Knot.Braid.Polynomial.Exact.Word
import Purelib.Polynomial.Dense.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

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

namespace Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Cancellation

/-! ### Backtracking cells and geometric rewrite chains -/

set_option genInjectivity false in
/-- The polynomial loop for a generator followed by its inverse is an exact coefficient backtrack. The second
five-vertex row is literally the reverse of the first, including the same collision-free crossing polynomial.

The original generator and its reverse determine the retained forward and backward coefficient paths. The retracing
equality and both exact boundary realizations keep the same indexed strand owners. -/
structure CancellationCell {strands : Nat}
    (generator : Braid.Generator strands) where
  /-- Retained exact elementary loop of the original signed generator. -/ forward : Elementary.ElementaryLoop generator
  /-- Retained exact elementary loop of the original reversed generator. -/ backward : Elementary.ElementaryLoop
    generator.reverse
  /-- The second retained coefficient-vertex list exactly reverses the first. -/ retraces : backward.coefficientVertices
    =
      forward.coefficientVertices.reverse
  /-- Retained polynomial realization of the original two-generator cancellation word. -/ leftBoundary :
    Word.RealizedLoop [generator, generator.reverse]
  /-- Retained polynomial realization of the original empty word. -/ rightBoundary : Word.RealizedLoop ([] : Braid.Word
    strands)

constructive_injectivity CancellationCell

/-- Cache the original elementary excursion, its exact reversed excursion and both cancellation boundaries. -/
@[expose] def cancellationCell {strands : Nat}
  (generator : Braid.Generator strands) :
    CancellationCell generator where
  forward := Elementary.elementaryLoop generator
  backward := Elementary.elementaryLoop generator.reverse
  retraces := Elementary.elementaryLoop_reverse_coefficients generator
  leftBoundary := Word.realizeWord [generator, generator.reverse]
  rightBoundary := Word.realizeWord []

/-- The canonical cancellation cell's second coefficient list is exactly the reverse of its first. -/
@[simp] theorem cancellationCell_retraces
  {strands : Nat}
    (generator : Braid.Generator strands) :
    (cancellationCell
      generator).backward.coefficientVertices =
      (cancellationCell
        generator).forward.coefficientVertices.reverse :=
  Elementary.elementaryLoop_reverse_coefficients generator

/-- The first retained cancellation boundary reads the original generator followed by its reverse. -/
@[simp] theorem cancellationCell_left_word
  {strands : Nat}
    (generator : Braid.Generator strands) :
    (cancellationCell
      generator).leftBoundary.extractedWord =
      [generator, generator.reverse] := rfl

/-- The second retained cancellation boundary reads the empty original word. -/
@[simp] theorem cancellationCell_right_word
  {strands : Nat}
    (generator : Braid.Generator strands) :
    (cancellationCell
      generator).rightBoundary.extractedWord =
      ([] : Braid.Word strands) := rfl

end Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Cancellation

end
