module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Braid.Artin
public import Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Artin
public import Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Cancellation
public import Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Far
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Topology.Knot.Braid.Word.Writhe
import Purelib.Topology.Knot.Braid.Basic

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid

open Purelib.Topology.Knot.Braid.Artin

open Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells

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

namespace Purelib.Topology.Knot.Braid.Polynomial.Exact.Homotopy

set_option genInjectivity false in
/-- One local polynomial-space rewrite. Unlike a bare Artin word rewrite, each constructor contains the exact finite
coefficient cell that realizes the move. Context words add unchanged polynomial excursions before and after the
displayed cell.

Each constructor retains the exact source and target words together with the original finite coefficient-space cell.
Prefix and suffix words preserve their displayed occurrence order. -/
inductive PolynomialRewrite {strands : Nat} :
    Braid.Word strands → Braid.Word strands → Type 1
  /-- Retain the exact original cancellation cell within its supplied word context. -/ | cancellation (before after :
    Braid.Word strands)
      (generator : Braid.Generator strands)
      (cell : Cancellation.CancellationCell generator := Cancellation.cancellationCell generator) :
      PolynomialRewrite
        (before ++ [generator, generator.reverse] ++ after)
        (before ++ after)
  /-- Retain the original disjoint-motion coefficient square within its supplied word context. -/ | farCommutation
    (before after : Braid.Word strands)
      (first second : Braid.Generator strands)
      (far : first.index.val + 1 < second.index.val ∨
        second.index.val + 1 < first.index.val)
      (cell : Far.FarCommutationCell first second far :=
        Far.farCommutationCell first second far) :
      PolynomialRewrite
        (before ++ [first, second] ++ after)
        (before ++ [second, first] ++ after)
  /-- Retain the original triple-projection Artin cell within its supplied word context. -/ | artin (before after :
    Braid.Word strands)
      (index : Fin (strands - 2)) (sign : Braid.CrossingSign)
      (cell : Artin.ArtinCell index sign := Artin.artinCell index sign) :
      PolynomialRewrite
        (before ++
          [Generator.lower index sign,
            Generator.upper index sign,
            Generator.lower index sign] ++ after)
        (before ++
          [Generator.upper index sign,
            Generator.lower index sign,
            Generator.upper index sign] ++ after)

constructive_injectivity PolynomialRewrite

namespace PolynomialRewrite

/-- Forgetting coefficient-cell geometry leaves the corresponding finite Artin rewrite. -/
theorem toArtinRewrite {strands : Nat}
  {left right : Braid.Word strands} :
    PolynomialRewrite left right →
      Artin.Rewrite left right
  | .cancellation before after generator _ =>
      .cancel before after generator
  | .farCommutation before after first second far _ =>
      .far before after first second far
  | .artin before after index sign _ =>
      .artin before after index sign

/-- A retained exact coefficient-cell rewrite preserves each original strand permutation value. -/
theorem permutationSame {strands : Nat}
  {left right : Braid.Word strands}
    (rewrite : PolynomialRewrite left right) (position : Fin
      strands) :
    left.permutation.forward position = right.permutation.forward position :=
  rewrite.toArtinRewrite.permutationSame position

/-- A retained exact coefficient-cell rewrite preserves the original integer writhe. -/
theorem writhe_eq {strands : Nat} {left
  right : Braid.Word strands}
    (rewrite : PolynomialRewrite left right) :
    left.writhe = right.writhe :=
  rewrite.toArtinRewrite.writhe_eq

end PolynomialRewrite

set_option genInjectivity false in
/-- Finite polynomial homotopy is the displayed reflexive, symmetric, transitive closure of the concrete coefficient
cells above.

The relation composes original polynomial rewrite steps without choosing another realization. Reflexivity, symmetry and
transitivity retain the indexed endpoint words. -/
inductive PolynomialHomotopic {strands : Nat} :
    Braid.Word strands → Braid.Word strands → Type 1
  /-- Include one original coefficient-cell rewrite in the finite polynomial homotopy. -/ | step {left right :
    Braid.Word strands}
      (rewrite : PolynomialRewrite left right) :
      PolynomialHomotopic left right
  /-- Retain the identity homotopy of one original realized word. -/ | refl (word : Braid.Word strands) :
    PolynomialHomotopic word word
  /-- Reverse a retained finite polynomial homotopy. -/ | symm {left right : Braid.Word strands}
      (homotopy : PolynomialHomotopic left right) :
      PolynomialHomotopic right left
  /-- Concatenate retained polynomial homotopies through the same original intermediate word. -/ | trans {first second
    third : Braid.Word strands}
      (firstSecond : PolynomialHomotopic first second)
      (secondThird : PolynomialHomotopic second third) :
      PolynomialHomotopic first third

constructive_injectivity PolynomialHomotopic

namespace PolynomialHomotopic

/-- Forgetting retained coefficient geometry gives the original finite Artin equivalence. -/
theorem braidEquivalent {strands : Nat}
  {left right : Braid.Word strands}
    (homotopy : PolynomialHomotopic left right) :
    Artin.Equivalent left right := by
  induction homotopy with
  | step rewrite => exact .step rewrite.toArtinRewrite
  | refl word => exact .refl word
  | symm homotopy inductionHypothesis => exact .symm inductionHypothesis
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact .trans firstHypothesis secondHypothesis

/-- A retained finite polynomial homotopy preserves each original strand permutation value. -/
theorem permutationSame {strands : Nat}
  {left right : Braid.Word strands}
    (homotopy : PolynomialHomotopic left right) (position : Fin
      strands) :
    left.permutation.forward position = right.permutation.forward position :=
  homotopy.braidEquivalent.permutationSame position

/-- A retained finite polynomial homotopy preserves the original integer writhe. -/
theorem writhe_eq {strands : Nat} {left
  right : Braid.Word strands}
    (homotopy : PolynomialHomotopic left right) :
    left.writhe = right.writhe :=
  homotopy.braidEquivalent.writhe_eq

/-- The two actual coefficient loops in a cancellation cell are polynomial-homotopic. -/
@[expose] def cancellation {strands :
  Nat} (before after : Braid.Word strands)
    (generator : Braid.Generator strands) :
    PolynomialHomotopic
      (before ++ [generator, generator.reverse] ++ after)
      (before ++ after) :=
  .step (.cancellation before after generator)

/-- The two actual coefficient loops on the boundary of the disjoint-motion square are polynomial-homotopic. -/
@[expose] def farCommutation {strands :
  Nat} (before after : Braid.Word strands)
    (first second : Braid.Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    PolynomialHomotopic
      (before ++ [first, second] ++ after)
      (before ++ [second, first] ++ after) :=
  .step (.farCommutation before after first second far)

/-- The two generic resolutions of the exact simple triple-projection polynomial are polynomial-homotopic. -/
@[expose] def artin {strands : Nat}
  (before after : Braid.Word strands)
    (index : Fin (strands - 2)) (sign : Braid.CrossingSign) :
    PolynomialHomotopic
      (before ++
        [Generator.lower index sign,
          Generator.upper index sign,
          Generator.lower index sign] ++ after)
      (before ++
        [Generator.upper index sign,
          Generator.lower index sign,
          Generator.upper index sign] ++ after) :=
  .step (.artin before after index sign)

end PolynomialHomotopic

end Purelib.Topology.Knot.Braid.Polynomial.Exact.Homotopy

end
