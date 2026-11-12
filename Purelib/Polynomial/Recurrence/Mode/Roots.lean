module

public import Purelib.Polynomial.Recurrence.Mode.Algebra
public import Purelib.Polynomial.Dense.Roots.Bank.Evaluation
import Purelib.Tactic.Ring

/-!
# Original recurrence modes of a retained root bank

Every displayed order below an original root block's multiplicity annihilates
the same normalized source coefficient row. The proof evaluates its exact
ordered factorization in the original finite nilpotent cyclic algebra.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode

open Purelib.Algebra.Monogenic
open Purelib.Algebra.Monogenic.Cyclic
open Purelib.LinearAlgebra.Matrix
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Dense.Roots

variable {K : Type*} [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K}

/-- Every displayed generalized order in an original root block annihilates the complete source row.

The original literal split factorization is evaluated in a nilpotent cyclic
algebra of exactly that block's multiplicity. The vanishing factor is retained
at its original bounded index, including when its root is zero.
-/
theorem bank_coefficientRow (bank : Bank polynomial) (index : Fin bank.blocks.length)
    (order : Nat) (bound : order < (bank.block index).multiplicity) (start : Nat) :
    coefficientRow polynomial.normalize.coeffs (bank.block index).point order start = 0 := by
  let block := bank.block index
  let cyclic := Cyclic.shift K block.multiplicity block.positive
  let point := shiftedRoot cyclic block.point
  have injective : Function.Injective (Element.scalar cyclic) :=
    fun _ _ same => Element.scalar_injective cyclic same
  have blockVanishes : (Map.map (Element.scalar cyclic) block.polynomial).eval point = 0 := by
    rw [Block.eval_map block (Element.scalar cyclic) (Element.scalar_zero cyclic) injective
      (Element.scalar_one cyclic) (Element.scalar_add cyclic) (Element.scalar_mul cyclic)
      (Element.scalar_neg cyclic)]
    have difference : point - Element.scalar cyclic block.point = Element.root cyclic := by
      change (Element.scalar cyclic block.point + Element.root cyclic) - Element.scalar cyclic block.point = _
      ring0
    rw [difference]
    exact shift_nilpotent cyclic
  have productVanishes : (Map.map (Element.scalar cyclic) (Roots.product bank.blocks)).eval point = 0 :=
    product_eval_zero bank.blocks index (Element.scalar cyclic) (Element.scalar_zero cyclic)
      injective (Element.scalar_add cyclic) (Element.scalar_mul cyclic) point blockVanishes
  have sourceVanishes : (Map.map (Element.scalar cyclic) polynomial.normalize).eval point = 0 := by
    rw [bank.factorization, Map.map_scale (Element.scalar cyclic) (Element.scalar_zero cyclic)
      injective (Element.scalar_mul cyclic), DensePolynomial.eval_scale, bank.product_eq, productVanishes,
      mul_zero]
  have readback := coefficientRow_shiftedRoot cyclic rfl polynomial.normalize.coeffs block.point
    ⟨order, bound⟩ start
  change (point ^ start * (Map.map (Element.scalar cyclic) polynomial.normalize).eval point).matrix
    ⟨order, bound⟩ cyclic.origin = _ at readback
  rw [sourceVanishes, mul_zero] at readback
  exact readback.symm.trans (Arithmetic.zero_apply _ _)

/-- Every finite original mode window in the bank satisfies the original cached companion recurrence. -/
theorem bank_window_satisfies (bank : Bank polynomial) (companion : Companion polynomial)
    (index : Fin bank.blocks.length) (order : Nat)
    (bound : order < (bank.block index).multiplicity) (count : Nat) :
    companion.Satisfies (window (bank.block index).point order count) :=
  window_satisfies companion _ order count (fun start _ => bank_coefficientRow bank index order bound start)

/-- Each original retained root is a root of the same normalized source polynomial. -/
theorem bank_eval_root (bank : Bank polynomial) (index : Fin bank.blocks.length) :
    polynomial.normalize.eval (bank.block index).point = 0 := by
  have zero := bank_coefficientRow bank index 0 (bank.block index).positive 0
  rw [coefficientRow_eval] at zero
  exact zero

/-- The same actual synthetic division at a retained root has zero original remainder. -/
theorem bank_synthetic_remainder (bank : Bank polynomial) (index : Fin bank.blocks.length)
    (result : Division.Synthetic.Result polynomial.normalize (bank.block index).point) :
    result.remainder = 0 := result.remainder_eval.trans (bank_eval_root bank index)

end Purelib.Polynomial.Recurrence.Mode

end
