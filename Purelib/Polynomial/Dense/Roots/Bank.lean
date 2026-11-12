module

public import Purelib.Polynomial.Dense.Multiplication.Basic
public import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.List.GetD
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Ordered root blocks of an original dense polynomial

Each block retains a positive multiplicity, including at the root zero.
The bank retains an actual product table, its original coefficient identity,
and a finite table of inverses of differences between distinct block roots.
-/

public section

namespace Purelib.Polynomial.Dense.Roots

open Purelib.Polynomial.Dense.Basic
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix

variable {K : Type*} [CommRing K] [DecidableEq K]

set_option genInjectivity false in
/-- One scalar root with its positive displayed multiplicity. -/
structure Block (K : Type*) where
  /-- The original root scalar. -/
  point : K
  /-- The positive number of generalized coordinates at this same root. -/
  multiplicity : Nat
  /-- The block retains at least one coordinate. -/
  positive : 0 < multiplicity

constructive_injectivity Block

namespace Block

omit [CommRing K] [DecidableEq K] in
/-- Map the original root scalar while preserving its same positive multiplicity. -/
@[expose] def map {L : Type*} (function : K → L) (block : Block K) : Block L :=
  ⟨function block.point, block.multiplicity, block.positive⟩

/-- Construct the displayed monic linear factors of one ordered root block. -/
@[expose] def polynomial (block : Block K) : DensePolynomial K :=
  (List.replicate block.multiplicity (⟨[1, -block.point]⟩ : DensePolynomial K)).foldr
    (fun factor remaining => factor * remaining) (DensePolynomial.constant 1)

end Block

/-- Construct the ordered finite product of the displayed root blocks. -/
@[expose] def product (blocks : List (Block K)) : DensePolynomial K :=
  blocks.foldr (fun block remaining => block.polynomial * remaining) (DensePolynomial.constant 1)

/-- Count all retained generalized coordinates in the same ordered root blocks. -/
@[expose] def totalMultiplicity (blocks : List (Block K)) : Nat :=
  blocks.foldr (fun block remaining => block.multiplicity + remaining) 0

set_option genInjectivity false in
/-- An ordered split factorization of the original source with retained root-difference units.

The original polynomial fixes the complete coordinate count. Its normalized
coefficient table is the same retained monic block product times its original
leading coefficient. No root itself is assumed invertible.
-/
structure Bank (polynomial : DensePolynomial K) where
  /-- The actual ordered distinct-root blocks and their positive multiplicities. -/
  blocks : List (Block K)
  /-- The block multiplicities exhaust the original source degree. -/
  count_eq : totalMultiplicity blocks = polynomial.natDegree
  /-- The cached actual monic product of the original root blocks. -/
  monicProduct : DensePolynomial K
  /-- The retained product uses those exact ordered block factors. -/
  product_eq : monicProduct = product blocks
  /-- The original normalized coefficient table has this exact split factorization. -/
  factorization : polynomial.normalize = DensePolynomial.scale polynomial.leadingCoeff monicProduct
  /-- The actual finite table of inverses of ordered root differences. -/
  differenceInverses : SquareMatrix K blocks.length
  /-- Every distinct pair of blocks has the same retained unit root difference. -/
  difference_unit : ∀ first second : Fin blocks.length, first ≠ second →
    ((blocks[first.val]'first.isLt).point - (blocks[second.val]'second.isLt).point) *
      differenceInverses first second = 1

constructive_injectivity Bank

namespace Bank

/-- Read an original retained block at its original bounded list index. -/
@[expose] def block {polynomial : DensePolynomial K} (bank : Bank polynomial)
    (index : Fin bank.blocks.length) : Block K := bank.blocks[index.val]'index.isLt

end Bank
end Purelib.Polynomial.Dense.Roots
