module

public import Purelib.Polynomial.Recurrence.Mode.Coefficients
public import Purelib.Algebra.Monogenic.Algebra
public import Purelib.Algebra.Monogenic.Cyclic.Shift
public import Purelib.Polynomial.Dense.Map.Ring
import Purelib.Data.List.Map
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Generalized modes in the original nilpotent cyclic algebra

Adding a scalar root to the original finite nilpotent shift retains the
binomial mode readings in its original distinguished column. Original dense
Horner evaluation then reads the complete finite coefficient action.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode

open Purelib.Algebra.Monogenic
open Purelib.Algebra.Monogenic.Cyclic
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Polynomial.Dense.Basic
open Purelib.Data
open Purelib.Data.List

variable {K : Type*} [CommRing K] {dimension : Nat}

/-- Translate the same original nilpotent cyclic generator by one scalar root. -/
@[expose] def shiftedRoot (cyclic : Cyclic (Shift.matrix K dimension)) (root : K) : Element cyclic :=
  Element.scalar cyclic root + Element.root cyclic

/-- A translated generator retains the same scalar diagonal and original nilpotent displacement entries. -/
theorem shiftedRoot_apply (cyclic : Cyclic (Shift.matrix K dimension)) (root : K)
    (row column : Fin dimension) :
    (shiftedRoot cyclic root).matrix row column =
      (if row = column then root else 0) + (if row.val = column.val + 1 then 1 else 0) := by
  rw [shiftedRoot, Element.add_matrix, Arithmetic.add_apply]
  change Multiplication.scaleIdentity root row column + Shift.matrix K dimension row column = _
  rw [Multiplication.scaleIdentity_apply, Shift.matrix_apply]

/-- The original dimension-th generator power vanishes in the same finite cyclic algebra. -/
theorem shift_nilpotent (cyclic : Cyclic (Shift.matrix K dimension)) :
    Element.root cyclic ^ dimension = 0 := by
  apply Element.ext
  rw [Element.pow_matrix]
  exact Shift.nilpotent

/-- Original powers of a translated nilpotent generator read the original generalized modes.

The finite cyclic certificate and its distinguished coordinate are retained.
Pascal's transition proves every column entry, without factorial division or
an assumption that the scalar root is invertible.
-/
theorem shiftedRoot_power (cyclic : Cyclic (Shift.matrix K dimension))
    (origin : cyclic.origin.val = 0) (root : K) (exponent : Nat) (order : Fin dimension) :
    (shiftedRoot cyclic root ^ exponent).matrix order cyclic.origin = entry root order.val exponent := by
  cases dimension with
  | zero => exact Fin.elim0 order
  | succ dimension =>
      induction exponent generalizing order with
      | zero =>
          change Multiplication.scaleIdentity (1 : K) order cyclic.origin = entry root order.val 0
          rw [Multiplication.scaleIdentity_apply]
          by_cases first : order.val = 0
          · have same : order = cyclic.origin := Fin.ext (first.trans origin.symm)
            rw [if_pos same, first, entry_start]
          · have different : order ≠ cyclic.origin := fun equal => first ((congrArg Fin.val equal).trans origin)
            rw [if_neg different, entry_before root order.val 0 (Nat.pos_of_ne_zero first)]
      | succ exponent previous =>
          rw [pow_succ, mul_comm (shiftedRoot cyclic root ^ exponent) (shiftedRoot cyclic root)]
          change ((Element.scalar cyclic root + Element.root cyclic) *
            shiftedRoot cyclic root ^ exponent).matrix order cyclic.origin = _
          rw [add_mul, Element.add_matrix, Arithmetic.add_apply, Element.scalar_mul_apply,
            Element.mul_matrix]
          change root * (shiftedRoot cyclic root ^ exponent).matrix order cyclic.origin +
            Multiplication.mul (Shift.matrix K (dimension + 1))
              (shiftedRoot cyclic root ^ exponent).matrix order cyclic.origin = _
          rw [previous order]
          cases value : order.val with
          | zero =>
              have same : order = (⟨0, Nat.zero_lt_succ dimension⟩ : Fin (dimension + 1)) := Fin.ext value
              rw [same, Shift.mul_first]
              change root * entry root 0 exponent + 0 = entry root 0 (exponent + 1)
              exact (add_zero _).trans (entry_succ_zero root exponent).symm
          | succ index =>
              have bounded : index < dimension := by have bound := order.isLt; omega0
              let previousOrder : Fin dimension := ⟨index, bounded⟩
              have same : order = previousOrder.succ := Fin.ext value
              rw [same, Shift.mul_succ, previous previousOrder.castSucc]
              exact (entry_succ root index exponent).symm

/-- The same original mapped Horner table reads its complete original mode coefficient row.

Multiplication by a finite starting power retains the displayed starting index.
The source coefficient list is consumed unchanged and is not normalized.
-/
theorem coefficientRow_shiftedRoot (cyclic : Cyclic (Shift.matrix K dimension))
    (origin : cyclic.origin.val = 0) (coefficients : List K) (root : K)
    (order : Fin dimension) (start : Nat) :
    (shiftedRoot cyclic root ^ start *
      DensePolynomial.evalCoeffs (shiftedRoot cyclic root) (coefficients.map (Element.scalar cyclic))).matrix
      order cyclic.origin = coefficientRow coefficients root order.val start := by
  induction coefficients with
  | nil =>
      rw [List.map_nil, DensePolynomial.evalCoeffs_nil, mul_zero]
      exact Arithmetic.zero_apply order cyclic.origin
  | cons leading remaining previous =>
      rw [List.map_cons, DensePolynomial.evalCoeffs_cons_expansion, mul_add, Element.add_matrix,
        Arithmetic.add_apply, previous]
      change _ = leading * entry root order.val (start + remaining.length) + _
      have scalarPower : shiftedRoot cyclic root ^ start *
          (Element.scalar cyclic leading * shiftedRoot cyclic root ^ (remaining.map (Element.scalar cyclic)).length) =
          Element.scalar cyclic leading * shiftedRoot cyclic root ^ (start + remaining.length) := by
        rw [List.Map.length_map, pow_add]
        ring0
      rw [scalarPower, Element.scalar_mul_apply, shiftedRoot_power cyclic origin]

/-- The same original mapped polynomial evaluation reads its zero-start mode row. -/
theorem coefficientRow_evaluation (cyclic : Cyclic (Shift.matrix K dimension))
    (origin : cyclic.origin.val = 0) (polynomial : DensePolynomial K) (root : K) (order : Fin dimension) :
    ((Dense.Map.map (Element.scalar cyclic) polynomial).eval (shiftedRoot cyclic root)).matrix
      order cyclic.origin = coefficientRow polynomial.coeffs root order.val 0 := by
  have reading := coefficientRow_shiftedRoot cyclic origin polynomial.coeffs root order 0
  rw [pow_zero, one_mul] at reading
  exact reading

/-- Removing representation-only leading zeros preserves every original generalized-mode coefficient row. -/
theorem coefficientRow_normalize [DecidableEq K] (polynomial : DensePolynomial K)
    (root : K) (order start : Nat) :
    coefficientRow polynomial.normalize.coeffs root order start =
      coefficientRow polynomial.coeffs root order start := by
  let cyclic := Cyclic.shift K (order + 1) (Nat.zero_lt_succ order)
  let coordinate : Fin (order + 1) := ⟨order, Nat.lt_succ_self order⟩
  have same := Dense.Map.map_normalize_eval (Element.scalar cyclic) (Element.scalar_zero cyclic)
    polynomial (shiftedRoot cyclic root)
  have entries := congrArg (fun value : Element cyclic =>
    (shiftedRoot cyclic root ^ start * value).matrix coordinate cyclic.origin) same
  exact (coefficientRow_shiftedRoot cyclic rfl polynomial.normalize.coeffs root coordinate start).symm.trans
    (entries.trans (coefficientRow_shiftedRoot cyclic rfl polynomial.coeffs root coordinate start))

/-- Original normalized polynomial scaling preserves the same scalar multiple of every mode row. -/
theorem coefficientRow_scale [DecidableEq K] (scalar : K) (polynomial : DensePolynomial K)
    (root : K) (order start : Nat) :
    coefficientRow (DensePolynomial.scale scalar polynomial).coeffs root order start =
      scalar * coefficientRow polynomial.coeffs root order start := by
  change coefficientRow (⟨polynomial.coeffs.map (scalar * ·)⟩ : DensePolynomial K).normalize.coeffs
    root order start = _
  rw [coefficientRow_normalize, coefficientRow_map_mul]

/-- The first original mode coefficient row of a product obeys its finite Leibniz law.

The original coefficient Horner product is interpreted in the same original
two-coordinate nilpotent cyclic algebra. No derivative factorial, characteristic
restriction or inverse root enters the identity.
-/
theorem coefficientRow_mul_first [DecidableEq K] (left right : DensePolynomial K) (root : K) :
    coefficientRow (left * right).coeffs root 1 0 =
      coefficientRow left.coeffs root 1 0 * right.eval root +
        left.eval root * coefficientRow right.coeffs root 1 0 := by
  let cyclic := Cyclic.shift K 2 (by decide)
  let point := shiftedRoot cyclic root
  let leftValue := (Dense.Map.map (Element.scalar cyclic) left).eval point
  let rightValue := (Dense.Map.map (Element.scalar cyclic) right).eval point
  have injective : Function.Injective (Element.scalar cyclic) :=
    fun _ _ same => Element.scalar_injective cyclic same
  have product : (Dense.Map.map (Element.scalar cyclic) (left * right)).eval point = leftValue * rightValue := by
    rw [Dense.Map.map_mul (Element.scalar cyclic) (Element.scalar_zero cyclic) injective
      (Element.scalar_add cyclic) (Element.scalar_mul cyclic), DensePolynomial.eval_mul]
  have leftZero := coefficientRow_evaluation cyclic rfl left root (0 : Fin 2)
  have rightZero := coefficientRow_evaluation cyclic rfl right root (0 : Fin 2)
  have zeroIndex : (0 : Fin 2).val = 0 := rfl
  have oneIndex : (1 : Fin 2).val = 1 := rfl
  rw [zeroIndex, coefficientRow_eval] at leftZero rightZero
  have leftOne := coefficientRow_evaluation cyclic rfl left root (1 : Fin 2)
  have rightOne := coefficientRow_evaluation cyclic rfl right root (1 : Fin 2)
  have readProduct := coefficientRow_evaluation cyclic rfl (left * right) root (1 : Fin 2)
  rw [oneIndex] at leftOne rightOne readProduct
  change ((Dense.Map.map (Element.scalar cyclic) (left * right)).eval point).matrix 1 0 = _ at readProduct
  rw [product] at readProduct
  have first := Element.shift_mul_one leftValue rightValue
  change (leftValue * rightValue).matrix 1 0 =
    leftValue.matrix 1 cyclic.origin * rightValue.matrix 0 cyclic.origin +
      leftValue.matrix 0 cyclic.origin * rightValue.matrix 1 cyclic.origin at first
  rw [leftZero, rightZero, leftOne, rightOne] at first
  exact readProduct.symm.trans first

end Purelib.Polynomial.Recurrence.Mode

end
