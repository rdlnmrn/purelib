module
public import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.GaussianInt.Basic
public import Purelib.Polynomial.Dense.Gaussian.Split.Lattice
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib.Polynomial.Dense.Gaussian.Split

open Purelib.Topology.Knot

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

namespace Purelib.Topology.Knot.Braid.Polynomial.Exact.Vertices

/-! ## Canonical base and crossing vertices -/

/-- Widely spaced roots on the real axis. -/
@[expose] def baseRoot {strands : Nat} (position : Fin
  strands) : GaussianInt.LatticePoint where
  x := 2 * position.val
  y := 0

/-- Original base lattice roots are distinct because their real coordinates are twice their indices. -/
theorem baseRoot_injective {strands : Nat} :
    Function.Injective (baseRoot : Fin strands →
      GaussianInt.LatticePoint) := by
  intro left right equal
  apply Fin.ext
  have xEqual := congrArg GaussianInt.LatticePoint.x equal
  change 2 * (left.val : Int) = 2 * (right.val : Int) at xEqual
  omega

/-- Build the exact split-polynomial vertex from the original distinct base roots. -/
@[expose] def baseVertex (strands : Nat) : Lattice.Vertex
  strands where
  root := baseRoot
  root_injective := baseRoot_injective

/-- The pre-crossing diagonal vertex. Its x-coordinates remain those of the base roots, so distinctness is immediate;
the two active heights record which persistent owner passes below the other. -/
@[expose] def approachRoot {strands : Nat} (generator :
  Braid.Generator strands)
    (position : Fin strands) : GaussianInt.LatticePoint :=
  if position = generator.left then
    { x := 2 * position.val
      y := match generator.sign with
        | .positive => -1
        | .negative => 1 }
  else if position = generator.right then
    { x := 2 * position.val
      y := match generator.sign with
        | .positive => 1
        | .negative => -1 }
  else
    baseRoot position

/-- Each original approach root retains its base real coordinate. -/
theorem approachRoot_x {strands : Nat} (generator :
  Braid.Generator strands)
    (position : Fin strands) :
    (approachRoot generator position).x = 2 * position.val := by
  unfold approachRoot
  split
  · rfl
  · split <;> rfl

/-- The original approach row has distinct roots by its retained real coordinates. -/
theorem approachRoot_injective {strands : Nat}
    (generator : Braid.Generator strands) :
    Function.Injective (approachRoot generator) := by
  intro left right equal
  apply Fin.ext
  have xEqual := congrArg GaussianInt.LatticePoint.x equal
  rw [approachRoot_x, approachRoot_x] at xEqual
  change 2 * (left.val : Int) = 2 * (right.val : Int) at xEqual
  omega

/-- Build the exact split-polynomial approach vertex for the original signed generator. -/
@[expose] def approachVertex {strands : Nat}
    (generator : Braid.Generator strands) : Lattice.Vertex strands where
  root := approachRoot generator
  root_injective := approachRoot_injective generator

/-- The collision-free projection midpoint of one adjacent crossing. The two active roots have the same x-coordinate and
heights fixed by the sign; all inactive roots remain at even x-coordinates on the real axis. -/
@[expose] def crossingRoot {strands : Nat} (generator :
  Braid.Generator strands)
    (position : Fin strands) : GaussianInt.LatticePoint :=
  if position = generator.left then
    { x := 2 * generator.index.val + 1
      y := -1 }
  else if position = generator.right then
    { x := 2 * generator.index.val + 1
      y := 1 }
  else
    baseRoot position

/-- The original crossing roots remain distinct by active heights and inactive even real coordinates.

The two active roots have different retained heights, while inactive roots keep distinct even real coordinates. The
original bounded strand indices identify every row in this finite separation argument. -/
theorem crossingRoot_injective {strands : Nat}
    (generator : Braid.Generator strands) :
    Function.Injective (crossingRoot generator) := by
  intro left right equal
  have firstRoot : crossingRoot generator generator.left =
      { x := 2 * generator.index.val + 1, y := -1 } := by
    unfold crossingRoot
    rw [if_pos rfl]
  have secondRoot : crossingRoot generator generator.right =
      { x := 2 * generator.index.val + 1, y := 1 } := by
    unfold crossingRoot
    rw [if_neg generator.left_ne_right.symm, if_pos rfl]
  have inactive (position : Fin strands) (notFirst : position ≠ generator.left)
      (notSecond : position ≠ generator.right) :
      crossingRoot generator position =
        baseRoot position := by
    unfold crossingRoot
    rw [if_neg notFirst, if_neg notSecond]
  by_cases leftAtFirst : left = generator.left
  · subst left
    by_cases rightAtFirst : right = generator.left
    · exact rightAtFirst.symm
    · by_cases rightAtSecond : right = generator.right
      · subst right
        have yEqual := congrArg GaussianInt.LatticePoint.y equal
        rw [firstRoot, secondRoot] at yEqual
        exact False.elim ((by decide : (-1 : Int) ≠ 1) yEqual)
      · have xEqual := congrArg GaussianInt.LatticePoint.x equal
        rw [firstRoot, inactive right rightAtFirst rightAtSecond] at xEqual
        change 2 * (generator.index.val : Int) + 1 = 2 * (right.val : Int) at xEqual
        omega
  · by_cases leftAtSecond : left = generator.right
    · subst left
      by_cases rightAtFirst : right = generator.left
      · subst right
        have yEqual := congrArg GaussianInt.LatticePoint.y equal
        rw [secondRoot, firstRoot] at yEqual
        exact False.elim ((by decide : (1 : Int) ≠ -1) yEqual)
      · by_cases rightAtSecond : right = generator.right
        · exact rightAtSecond.symm
        · have xEqual := congrArg GaussianInt.LatticePoint.x equal
          rw [secondRoot, inactive right rightAtFirst rightAtSecond] at xEqual
          change 2 * (generator.index.val : Int) + 1 = 2 * (right.val : Int) at xEqual
          omega
    · by_cases rightAtFirst : right = generator.left
      · subst right
        have xEqual := congrArg GaussianInt.LatticePoint.x equal
        rw [inactive left leftAtFirst leftAtSecond, firstRoot] at xEqual
        change 2 * (left.val : Int) = 2 * (generator.index.val : Int) + 1 at xEqual
        omega
      · by_cases rightAtSecond : right = generator.right
        · subst right
          have xEqual := congrArg GaussianInt.LatticePoint.x equal
          rw [inactive left leftAtFirst leftAtSecond, secondRoot] at xEqual
          change 2 * (left.val : Int) = 2 * (generator.index.val : Int) + 1 at xEqual
          omega
        · apply Fin.ext
          have xEqual := congrArg GaussianInt.LatticePoint.x equal
          rw [inactive left leftAtFirst leftAtSecond, inactive right rightAtFirst rightAtSecond] at xEqual
          change 2 * (left.val : Int) = 2 * (right.val : Int) at xEqual
          omega

/-- Build the exact split-polynomial crossing vertex with its original simple-root certificate. -/
@[expose] def crossingVertex {strands : Nat}
    (generator : Braid.Generator strands) : Lattice.Vertex strands where
  root := crossingRoot generator
  root_injective := crossingRoot_injective generator

/-- Reversing the original generator preserves its crossing polynomial. -/
@[simp] theorem crossingVertex_reverse {strands : Nat}
    (generator : Braid.Generator strands) :
    (crossingVertex generator.reverse).polynomial =
      (crossingVertex generator).polynomial := by
  cases generator with
  | mk index sign => rfl

end Purelib.Topology.Knot.Braid.Polynomial.Exact.Vertices

end
