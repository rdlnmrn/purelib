module

public import Purelib.Polynomial.Dense.Roots.Bank
public import Purelib.Polynomial.Dense.Map.Ring
import Purelib.Data.List.Replicate
import Purelib.Tactic.Ring

/-!
# Evaluation of the original ordered root products

The original monic block product evaluates to its displayed finite powers of
root differences. Injective ring maps transport the same original coefficient
tables and normalization decisions before evaluation at an arbitrary target point.
-/

public section

namespace Purelib.Polynomial.Dense.Roots

open Purelib.Polynomial.Dense.Basic

variable {K L : Type*} [CommRing K] [DecidableEq K] [CommRing L] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
/-- A mapped displayed monic linear factor evaluates to its same target root difference. -/
theorem Block.eval_linear (function : K → L) (mapOne : function 1 = 1)
    (mapNeg : ∀ value, function (-value) = -function value) (root : K) (point : L) :
    (Map.map function (⟨[1, -root]⟩ : DensePolynomial K)).eval point = point - function root := by
  change (0 * point + function 1) * point + function (-root) = point - function root
  rw [mapOne, mapNeg, zero_mul, zero_add, one_mul]
  ring0

/-- A mapped original root block evaluates to its same displayed finite difference power. -/
theorem Block.eval_map (block : Block K) (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (mapNeg : ∀ value, function (-value) = -function value) (point : L) :
    (Map.map function block.polynomial).eval point = (point - function block.point) ^ block.multiplicity := by
  have factors : ∀ count : Nat,
      (Map.map function ((List.replicate count (⟨[1, -block.point]⟩ : DensePolynomial K)).foldr
        (fun factor remaining => factor * remaining) (DensePolynomial.constant 1))).eval point =
        (point - function block.point) ^ count := by
    intro count
    induction count with
    | zero =>
        change (Map.map function (DensePolynomial.constant 1)).eval point = _
        rw [Map.map_constant, DensePolynomial.eval_constant, mapOne, pow_zero]
    | succ count previous =>
        change (Map.map function ((⟨[1, -block.point]⟩ : DensePolynomial K) *
          (List.replicate count (⟨[1, -block.point]⟩ : DensePolynomial K)).foldr
            (fun factor remaining => factor * remaining) (DensePolynomial.constant 1))).eval point = _
        rw [Map.map_mul function mapZero injective mapAdd mapMul, DensePolynomial.eval_mul,
          Block.eval_linear function mapOne mapNeg, previous, pow_succ, mul_comm]
  exact factors block.multiplicity

/-- A vanished displayed block makes the same original ordered product vanish at that point.

The original bounded block index locates the factor. Only that actual factor
vanishes; the remaining ordered factors need no inverses or cancellation laws.
-/
theorem product_eval_zero (blocks : List (Block K)) (index : Fin blocks.length)
    (function : K → L) (mapZero : function 0 = 0) (injective : Function.Injective function)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (point : L) (vanishes : (Map.map function (blocks[index.val]'index.isLt).polynomial).eval point = 0) :
    (Map.map function (product blocks)).eval point = 0 := by
  induction blocks with
  | nil => exact Fin.elim0 index
  | cons block remaining previous =>
      change (Map.map function (block.polynomial * product remaining)).eval point = 0
      rw [Map.map_mul function mapZero injective mapAdd mapMul, DensePolynomial.eval_mul]
      rcases index with ⟨position, bound⟩
      cases position with
      | zero =>
          change (Map.map function block.polynomial).eval point = 0 at vanishes
          rw [vanishes, zero_mul]
      | succ position =>
          have bounded : position < remaining.length := Nat.lt_of_succ_lt_succ bound
          let tailIndex : Fin remaining.length := ⟨position, bounded⟩
          have tailVanishes : (Map.map function (remaining[position]'bounded).polynomial).eval point = 0 := vanishes
          rw [previous tailIndex tailVanishes, mul_zero]

end Purelib.Polynomial.Dense.Roots

end
