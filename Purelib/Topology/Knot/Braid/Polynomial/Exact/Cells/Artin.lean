module

import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Braid.Basic
public import Purelib.Data.Fin.AdjacentTriple
import Purelib.Data.GaussianInt.Basic
import Purelib.Polynomial.Dense.Gaussian.Split.Lattice
public import Purelib.Topology.Knot.Braid.Artin
import Purelib.Topology.Knot.Braid.Polynomial.Exact.Vertices
public import Purelib.Topology.Knot.Braid.Polynomial.Exact.Word
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Fin

open Purelib.Polynomial.Dense.Gaussian.Split

open Purelib.Polynomial.Dense.Gaussian.Split.Lattice

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid.Artin

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

namespace Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Artin

/-- The valid triple-projection vertex used to pass between the two generic resolutions of the Reidemeister-III/Artin
event. Three roots share one projection coordinate but remain separated at heights `-2`, `0`, and `2`. -/
@[expose] def tripleRoot {strands : Nat} (index : Fin
  (strands - 2))
    (position : Fin strands) : GaussianInt.LatticePoint :=
  if position = AdjacentTriple.tripleLeft index then
    { x := 2 * index.val + 1, y := -2 }
  else if position = AdjacentTriple.tripleMiddle index then
    { x := 2 * index.val + 1, y := 0 }
  else if position = AdjacentTriple.tripleRight index then
    { x := 2 * index.val + 1, y := 2 }
  else
    Vertices.baseRoot position

/-- The original left triple root has the shared odd real coordinate and height minus two. -/
@[simp] theorem tripleRoot_left {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleRoot index (AdjacentTriple.tripleLeft index) =
      { x := 2 * index.val + 1, y := -2 } := by
  unfold tripleRoot
  rw [if_pos rfl]

/-- The original middle triple root has the shared odd real coordinate and height zero. -/
@[simp] theorem tripleRoot_middle {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleRoot index (AdjacentTriple.tripleMiddle index) =
      { x := 2 * index.val + 1, y := 0 } := by
  unfold tripleRoot
  rw [if_neg (AdjacentTriple.tripleLeft_ne_middle index).symm, if_pos rfl]

/-- The original right triple root has the shared odd real coordinate and height two. -/
@[simp] theorem tripleRoot_right {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleRoot index (AdjacentTriple.tripleRight index) =
      { x := 2 * index.val + 1, y := 2 } := by
  unfold tripleRoot
  rw [if_neg (AdjacentTriple.tripleLeft_ne_right index).symm,
    if_neg (AdjacentTriple.tripleMiddle_ne_right index).symm, if_pos rfl]

/-- Every inactive original root remains at its canonical base lattice position. -/
theorem tripleRoot_other {strands : Nat}
    (index : Fin (strands - 2)) (position : Fin strands)
    (notLeft : position ≠ AdjacentTriple.tripleLeft index)
    (notMiddle : position ≠ AdjacentTriple.tripleMiddle index)
    (notRight : position ≠ AdjacentTriple.tripleRight index) :
    tripleRoot index position = Vertices.baseRoot position :=
      by
  unfold tripleRoot
  rw [if_neg notLeft, if_neg notMiddle, if_neg notRight]

/-- The original triple-projection lattice row has pairwise distinct roots.

The three active roots are separated at heights minus two, zero and two. All inactive roots retain their distinct even
real coordinates, separate from the shared odd active coordinate. -/
theorem tripleRoot_injective {strands : Nat}
    (index : Fin (strands - 2)) :
    Function.Injective (tripleRoot index) := by
  intro left right equal
  by_cases leftAtLeft : left = AdjacentTriple.tripleLeft index
  · subst left
    by_cases rightAtLeft : right = AdjacentTriple.tripleLeft index
    · exact rightAtLeft.symm
    · by_cases rightAtMiddle : right = AdjacentTriple.tripleMiddle index
      · subst right
        have yEqual := congrArg GaussianInt.LatticePoint.y equal
        rw [tripleRoot_left, tripleRoot_middle] at yEqual
        exact False.elim ((by decide : (-2 : Int) ≠ 0) yEqual)
      · by_cases rightAtRight : right = AdjacentTriple.tripleRight index
        · subst right
          have yEqual := congrArg GaussianInt.LatticePoint.y equal
          rw [tripleRoot_left, tripleRoot_right] at yEqual
          exact False.elim ((by decide : (-2 : Int) ≠ 2) yEqual)
        · have xEqual := congrArg GaussianInt.LatticePoint.x equal
          rw [tripleRoot_left,
            tripleRoot_other index right rightAtLeft rightAtMiddle rightAtRight]
            at xEqual
          change 2 * (index.val : Int) + 1 = 2 * (right.val : Int) at xEqual
          omega
  · by_cases leftAtMiddle : left = AdjacentTriple.tripleMiddle index
    · subst left
      by_cases rightAtLeft : right = AdjacentTriple.tripleLeft index
      · subst right
        have yEqual := congrArg GaussianInt.LatticePoint.y equal
        rw [tripleRoot_middle, tripleRoot_left] at yEqual
        exact False.elim ((by decide : (0 : Int) ≠ -2) yEqual)
      · by_cases rightAtMiddle : right = AdjacentTriple.tripleMiddle index
        · exact rightAtMiddle.symm
        · by_cases rightAtRight : right = AdjacentTriple.tripleRight index
          · subst right
            have yEqual := congrArg GaussianInt.LatticePoint.y equal
            rw [tripleRoot_middle, tripleRoot_right] at yEqual
            exact False.elim ((by decide : (0 : Int) ≠ 2) yEqual)
          · have xEqual := congrArg GaussianInt.LatticePoint.x equal
            rw [tripleRoot_middle,
              tripleRoot_other index right rightAtLeft rightAtMiddle
                rightAtRight] at xEqual
            change 2 * (index.val : Int) + 1 =
              2 * (right.val : Int) at xEqual
            omega
    · by_cases leftAtRight : left = AdjacentTriple.tripleRight index
      · subst left
        by_cases rightAtLeft : right = AdjacentTriple.tripleLeft index
        · subst right
          have yEqual := congrArg GaussianInt.LatticePoint.y equal
          rw [tripleRoot_right, tripleRoot_left] at yEqual
          exact False.elim ((by decide : (2 : Int) ≠ -2) yEqual)
        · by_cases rightAtMiddle : right = AdjacentTriple.tripleMiddle index
          · subst right
            have yEqual := congrArg GaussianInt.LatticePoint.y equal
            rw [tripleRoot_right, tripleRoot_middle] at yEqual
            exact False.elim ((by decide : (2 : Int) ≠ 0) yEqual)
          · by_cases rightAtRight : right = AdjacentTriple.tripleRight index
            · exact rightAtRight.symm
            · have xEqual := congrArg GaussianInt.LatticePoint.x equal
              rw [tripleRoot_right,
                tripleRoot_other index right rightAtLeft rightAtMiddle
                  rightAtRight] at xEqual
              change 2 * (index.val : Int) + 1 =
                2 * (right.val : Int) at xEqual
              omega
      · by_cases rightAtLeft : right = AdjacentTriple.tripleLeft index
        · subst right
          have xEqual := congrArg GaussianInt.LatticePoint.x equal
          rw [tripleRoot_other index left leftAtLeft leftAtMiddle leftAtRight,
            tripleRoot_left] at xEqual
          change 2 * (left.val : Int) = 2 * (index.val : Int) + 1 at xEqual
          omega
        · by_cases rightAtMiddle : right = AdjacentTriple.tripleMiddle index
          · subst right
            have xEqual := congrArg GaussianInt.LatticePoint.x equal
            rw [tripleRoot_other index left leftAtLeft leftAtMiddle leftAtRight,
              tripleRoot_middle] at xEqual
            change 2 * (left.val : Int) =
              2 * (index.val : Int) + 1 at xEqual
            omega
          · by_cases rightAtRight : right = AdjacentTriple.tripleRight index
            · subst right
              have xEqual := congrArg GaussianInt.LatticePoint.x equal
              rw [tripleRoot_other index left leftAtLeft leftAtMiddle
                leftAtRight, tripleRoot_right] at xEqual
              change 2 * (left.val : Int) =
                2 * (index.val : Int) + 1 at xEqual
              omega
            · apply Vertices.baseRoot_injective
              rw [← tripleRoot_other index left leftAtLeft leftAtMiddle
                leftAtRight,
                ← tripleRoot_other index right rightAtLeft rightAtMiddle
                  rightAtRight]
              exact equal

/-- Build the exact split-polynomial vertex from the original certified triple-projection roots. -/
@[expose] def tripleVertex {strands : Nat} (index : Fin
  (strands - 2)) :
    Lattice.Vertex strands where
  root := tripleRoot index
  root_injective := tripleRoot_injective index

set_option genInjectivity false in
/-- Concrete collision-free coefficient cell for the Artin relation. Both boundary loops are explicit split-polynomial
loops; `centralVertex` is the valid triple-projection row through which one finite resolution changes into the other.

Both boundary words share the original three aligned strand positions and crossing sign. The cached center separates the
three roots by height, while each boundary retains its exact word realization. -/
structure ArtinCell {strands : Nat} (index : Fin
  (strands - 2))
    (sign : Braid.CrossingSign) where
  /-- Retained collision-free vertex with the original three aligned projection coordinates. -/ centralVertex :
    Lattice.Vertex strands := tripleVertex index
  /-- Retained exact polynomial-loop realization of the original lower-upper-lower word. -/ leftBoundary :
    Word.RealizedLoop
      [Generator.lower index sign,
        Generator.upper index sign,
        Generator.lower index sign] :=
    Word.realizeWord _
  /-- Retained exact polynomial-loop realization of the original upper-lower-upper word. -/ rightBoundary :
    Word.RealizedLoop
      [Generator.upper index sign,
        Generator.lower index sign,
        Generator.upper index sign] :=
    Word.realizeWord _

constructive_injectivity ArtinCell

/-- Build the canonical original Artin coefficient cell and its two realized word boundaries. -/
@[expose] def artinCell {strands : Nat} (index : Fin
  (strands - 2))
    (sign : Braid.CrossingSign) : ArtinCell index sign := {}

/-- The original Artin cell's central polynomial has degree equal to the strand count. -/
@[simp] theorem artinCell_center_degree {strands : Nat}
    (index : Fin (strands - 2)) (sign : Braid.CrossingSign) :
    ((artinCell index sign).centralVertex.polynomial).natDegree
      = strands :=
  Vertex.polynomial_natDegree _

/-- The original Artin cell's central polynomial is monic. -/
@[simp] theorem artinCell_center_monic {strands : Nat}
    (index : Fin (strands - 2)) (sign : Braid.CrossingSign) :
    ((artinCell index
      sign).centralVertex.polynomial).leadingCoeff = 1 :=
  Vertex.polynomial_leadingCoeff _

/-- The cell's first realized boundary reads the original lower-upper-lower word. -/
@[simp] theorem artinCell_left_word {strands : Nat}
    (index : Fin (strands - 2)) (sign : Braid.CrossingSign) :
    (artinCell index sign).leftBoundary.extractedWord =
      [Generator.lower index sign,
        Generator.upper index sign,
        Generator.lower index sign] := rfl

/-- The cell's second realized boundary reads the original upper-lower-upper word. -/
@[simp] theorem artinCell_right_word {strands : Nat}
    (index : Fin (strands - 2)) (sign : Braid.CrossingSign) :
    (artinCell index sign).rightBoundary.extractedWord =
      [Generator.upper index sign,
        Generator.lower index sign,
        Generator.upper index sign] := rfl

end Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Artin

end
