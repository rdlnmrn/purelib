module
import Purelib.Data.List.OfFn.Basic

import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Embedding
public import Purelib.Polynomial.Dense.Gaussian.Split
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Dense.Gaussian.Split.Lattice

set_option genInjectivity false in
/-- A finite exact simple-root vertex.  Pairwise distinct displayed factors
are the squarefree certificate used by this split model.

The original indexed lattice table and its injectivity certificate determine the ordered rational factor list. The same
table supplies each computed polynomial and its displayed root witnesses. -/
structure Vertex (strands : Nat) where
  /-- The original finite indexed table of Gaussian-integer roots. -/ root : Fin strands → GaussianInt.LatticePoint
  /-- Different retained indices carry distinct Gaussian-integer roots. -/ root_injective : Function.Injective root

constructive_injectivity Vertex

namespace Vertex

/-- Enumerate the retained lattice roots as Gaussian rationals in their original finite index order. -/
@[expose] def gaussianRoots {strands : Nat} (vertex :
  Vertex strands) : List Gaussian.Basic.Canonical :=
  List.ofFn (fun position => (vertex.root position).gaussian)

/-- Form the finite monic product of linear factors at the retained Gaussian roots. -/
@[expose] def polynomial {strands : Nat} (vertex :
  Vertex strands) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Split.splitPolynomial vertex.gaussianRoots

/-- Embedding the retained lattice roots into Gaussian rationals preserves their injectivity. -/
theorem gaussianRoot_injective {strands : Nat} (vertex :
  Vertex strands) :
    Function.Injective (fun position => (vertex.root position).gaussian) :=
  GaussianInt.LatticePoint.gaussian_injective.comp vertex.root_injective

/-- Different original finite indices have different embedded Gaussian roots. -/
theorem gaussianRoots_distinct {strands : Nat} (vertex :
  Vertex strands)
    {left right : Fin strands} (different : left ≠ right) :
    (vertex.root left).gaussian ≠ (vertex.root right).gaussian := by
  intro equal
  exact different (vertex.gaussianRoot_injective equal)

/-- The displayed Gaussian root list has exactly the retained number of strands. -/
@[simp] theorem gaussianRoots_length {strands : Nat}
    (vertex : Vertex strands) : vertex.gaussianRoots.length = strands := by
  exact List.OfFn.Basic.length_ofFn

/-- The finite split polynomial has a nonzero normalized coefficient table. -/
@[simp] theorem polynomial_isZero_false {strands : Nat}
    (vertex : Vertex strands) : vertex.polynomial.isZero = false := by
  exact Dense.Gaussian.Split.splitPolynomial_isZero_false vertex.gaussianRoots

/-- The split polynomial degree equals the retained root count. -/
@[simp] theorem polynomial_natDegree {strands : Nat}
    (vertex : Vertex strands) : vertex.polynomial.natDegree = strands := by
  exact (Dense.Gaussian.Split.splitPolynomial_natDegree vertex.gaussianRoots).trans vertex.gaussianRoots_length

/-- The polynomial formed from the displayed linear factors is monic. -/
@[simp] theorem polynomial_leadingCoeff {strands : Nat}
    (vertex : Vertex strands) : vertex.polynomial.leadingCoeff = 1 := by
  exact Dense.Gaussian.Split.splitPolynomial_leadingCoeff vertex.gaussianRoots

/-- Every displayed factor point is an exact root of the computed
coefficient polynomial. -/
@[simp] theorem polynomial_eval_root {strands : Nat}
    (vertex : Vertex strands) (position : Fin strands) :
    vertex.polynomial.eval (vertex.root position).gaussian = 0 := by
  apply Dense.Gaussian.Split.splitPolynomial_eval_eq_zero_of_mem
  exact List.OfFn.Basic.mem_ofFn.mpr ⟨position, rfl⟩

end Vertex

end Purelib.Polynomial.Dense.Gaussian.Split.Lattice

end
