module

public import Purelib.Polynomial.Dense.Roots.Bank
public import Purelib.Polynomial.Dense.Multiplication.Laws
import Purelib.Data.List.Replicate

/-!
# Original root-block products with simple factors

A multiplicity-one block supplies its displayed linear factor to the same
original ordered product. Its internal terminal constant contributes only
normalization, which original multiplication already preserves.
-/

public section

namespace Purelib.Polynomial.Dense.Roots

open Basic (DensePolynomial)

variable {K : Type*} [CommRing K] [DecidableEq K]

omit [CommRing K] [DecidableEq K] in
/-- Concatenating original root-block lists adds their same displayed multiplicity totals. -/
theorem totalMultiplicity_append (first second : List (Block K)) :
    totalMultiplicity (first ++ second) = totalMultiplicity first + totalMultiplicity second := by
  induction first with
  | nil => exact (Nat.zero_add _).symm
  | cons block remaining previous =>
      change block.multiplicity + totalMultiplicity (remaining ++ second) =
        (block.multiplicity + totalMultiplicity remaining) + totalMultiplicity second
      rewrite [previous]
      exact (Nat.add_assoc _ _ _).symm

section Maps

variable {L : Type*} [CommRing L] [DecidableEq L]

/-- Mapping the original root block maps the same finite linear-factor product. -/
theorem Block.map_polynomial (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (mapNeg : ∀ value, function (-value) = -function value) (block : Block K) :
    Map.map function block.polynomial = (block.map function).polynomial := by
  have linear : Map.map function (⟨[1, -block.point]⟩ : DensePolynomial K) =
      (⟨[1, -function block.point]⟩ : DensePolynomial L) := by
    apply DensePolynomial.ext
    change [function 1, function (-block.point)] = [1, -function block.point]
    rewrite [mapOne, mapNeg]
    rfl
  have factors : ∀ count : Nat,
      Map.map function ((List.replicate count (⟨[1, -block.point]⟩ : DensePolynomial K)).foldr
        (fun factor remaining => factor * remaining) (DensePolynomial.constant 1)) =
      (List.replicate count (⟨[1, -function block.point]⟩ : DensePolynomial L)).foldr
        (fun factor remaining => factor * remaining) (DensePolynomial.constant 1) := by
    intro count
    induction count with
    | zero => exact congrArg DensePolynomial.constant mapOne
    | succ count previous =>
        change Map.map function ((⟨[1, -block.point]⟩ : DensePolynomial K) * _) = _
        rewrite [Map.map_mul function mapZero injective mapAdd mapMul, linear, previous]
        rfl
  exact factors block.multiplicity

/-- Coefficient mapping preserves the same original ordered root-block product. -/
theorem map_product (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (mapNeg : ∀ value, function (-value) = -function value) (blocks : List (Block K)) :
    Map.map function (product blocks) = product (blocks.map (Block.map function)) := by
  induction blocks with
  | nil => exact congrArg DensePolynomial.constant mapOne
  | cons block remaining previous =>
      change Map.map function (block.polynomial * product remaining) =
        (block.map function).polynomial * product (remaining.map (Block.map function))
      rewrite [Map.map_mul function mapZero injective mapAdd mapMul,
        Block.map_polynomial function mapZero injective mapOne mapAdd mapMul mapNeg, previous]
      rfl

end Maps

/-- A leading multiplicity-one block contributes its displayed original linear factor. -/
theorem product_cons_one (point : K) (remaining : List (Block K)) :
    product (⟨point, 1, Nat.zero_lt_succ 0⟩ :: remaining) =
      (⟨[1, -point]⟩ : DensePolynomial K) * product remaining := by
  change ((⟨[1, -point]⟩ : DensePolynomial K) * DensePolynomial.constant 1) * product remaining = _
  rewrite [DensePolynomial.mul_constant_one]
  exact DensePolynomial.normalize_mul_left _ _

end Purelib.Polynomial.Dense.Roots

end
