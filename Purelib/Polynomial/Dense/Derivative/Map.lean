module

public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Recurrence.Mode.Algebra
import Purelib.Data.List.Fold
import Purelib.Data.List.Map
import Purelib.Tactic.Ring

/-!
# Original derivatives under coefficient interpretation

The original polynomial derivative-state producer remains unchanged over its
source field. Interpreting its retained coefficients in a commutative ring
reads the same first mode coefficient through the original nilpotent shift.
-/

public section

namespace Purelib.Polynomial.Dense.Derivative.Map

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Recurrence
open Purelib.Algebra.Field
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Monogenic.Cyclic
open Purelib.LinearAlgebra.Matrix
open Purelib.Data
open Purelib.Data.List

variable {K L : Type*} [ExplicitField K] [DecidableEq K] [CommRing L] [DecidableEq L]

omit [DecidableEq L] in
/-- The original translated two-coordinate generator reads its same scalar root. -/
private theorem point_zero (cyclic : Cyclic (Shift.matrix L 2)) (root : L) :
    (Mode.shiftedRoot cyclic root).matrix (0 : Fin 2) (0 : Fin 2) = root := by
  rw [Mode.shiftedRoot_apply, if_pos rfl]
  have different : (0 : Fin 2).val ≠ (0 : Fin 2).val + 1 := by decide
  rw [if_neg different, add_zero]

omit [DecidableEq L] in
/-- The first translated nilpotent displacement is the same original unit. -/
private theorem point_one (cyclic : Cyclic (Shift.matrix L 2)) (root : L) :
    (Mode.shiftedRoot cyclic root).matrix (1 : Fin 2) (0 : Fin 2) = 1 := by
  rw [Mode.shiftedRoot_apply]
  have different : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  have next : (1 : Fin 2).val = (0 : Fin 2).val + 1 := by decide
  rw [if_neg different, if_pos next, zero_add]

/-- An interpreted original derivative-state scan retains the same two original Horner column entries. -/
private theorem fold_readback (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (cyclic : Cyclic (Shift.matrix L 2)) (root : L) (coefficients : List K)
    (state : DensePolynomial K × DensePolynomial K) (value : Element cyclic)
    (zero : value.matrix (0 : Fin 2) 0 = (Dense.Map.map function state.1).eval root)
    (one : value.matrix (1 : Fin 2) 0 = (Dense.Map.map function state.2).eval root) :
    let modeled := coefficients.foldl
      (fun current coefficient => current * Mode.shiftedRoot cyclic root +
        Element.scalar cyclic (function coefficient)) value
    let final := coefficients.foldl Derivative.derivativeStep state
    modeled.matrix (0 : Fin 2) 0 = (Dense.Map.map function final.1).eval root ∧
      modeled.matrix (1 : Fin 2) 0 = (Dense.Map.map function final.2).eval root := by
  induction coefficients generalizing state value with
  | nil => exact ⟨zero, one⟩
  | cons coefficient remaining previous =>
      apply previous (Derivative.derivativeStep state coefficient)
        (value * Mode.shiftedRoot cyclic root + Element.scalar cyclic (function coefficient))
      · have mapped : (Dense.Map.map function (Derivative.derivativeStep state coefficient).1).eval root =
            (Dense.Map.map function state.1).eval root * root + function coefficient := by
          change (Dense.Map.map function (DensePolynomial.shift 1 state.1 +
            DensePolynomial.constant coefficient)).eval root = _
          rw [Dense.Map.map_add function mapZero injective mapAdd,
            Dense.Map.map_shift function mapZero injective, Dense.Map.map_constant,
            DensePolynomial.eval_add, DensePolynomial.eval_shift, DensePolynomial.eval_constant, pow_one]
        have scalar : (Element.scalar cyclic (function coefficient)).matrix (0 : Fin 2) 0 =
            function coefficient := by
          change Multiplication.scaleIdentity (function coefficient) (0 : Fin 2) 0 = _
          rw [Multiplication.scaleIdentity_apply, if_pos rfl]
        rw [Element.add_matrix, Arithmetic.add_apply, Element.shift_mul_zero, point_zero, scalar, zero]
        exact mapped.symm
      · have mapped : (Dense.Map.map function (Derivative.derivativeStep state coefficient).2).eval root =
            (Dense.Map.map function state.2).eval root * root + (Dense.Map.map function state.1).eval root := by
          change (Dense.Map.map function (DensePolynomial.shift 1 state.2 + state.1)).eval root = _
          rw [Dense.Map.map_add function mapZero injective mapAdd,
            Dense.Map.map_shift function mapZero injective, DensePolynomial.eval_add,
            DensePolynomial.eval_shift, pow_one]
        have scalar : (Element.scalar cyclic (function coefficient)).matrix (1 : Fin 2) 0 = 0 := by
          change Multiplication.scaleIdentity (function coefficient) (1 : Fin 2) 0 = _
          rw [Multiplication.scaleIdentity_apply, if_neg (by decide : (1 : Fin 2) ≠ (0 : Fin 2))]
        rw [Element.add_matrix, Arithmetic.add_apply, Element.shift_mul_one,
          point_zero, point_one, scalar, mul_one, add_zero, zero, one]
        exact mapped.symm

/-- The original mapped derivative reads the same first generalized-mode coefficient.

The original field-valued derivative producer is interpreted by one retained
coefficient function into an arbitrary commutative target ring. Only the
original derivative-state fold is used; the target ring is not given a field
structure or a second derivative producer.
-/
theorem firstJet (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (polynomial : DensePolynomial K) (root : L) :
    (Dense.Map.map function (Derivative.derivative polynomial)).eval root =
      Mode.coefficientRow (Dense.Map.map function polynomial).coeffs root 1 0 := by
  let cyclic := Cyclic.shift L 2 (by decide)
  have initialZero : (0 : Element cyclic).matrix (0 : Fin 2) 0 =
      (Dense.Map.map function (0 : DensePolynomial K)).eval root := by
    rw [Dense.Map.map_zero_polynomial, DensePolynomial.eval_zero]
    exact Arithmetic.zero_apply _ _
  have initialOne : (0 : Element cyclic).matrix (1 : Fin 2) 0 =
      (Dense.Map.map function (0 : DensePolynomial K)).eval root := by
    rw [Dense.Map.map_zero_polynomial, DensePolynomial.eval_zero]
    exact Arithmetic.zero_apply _ _
  have original := fold_readback function mapZero injective mapAdd cyclic root polynomial.coeffs
    (0, 0) 0 initialZero initialOne
  have reading := Mode.coefficientRow_evaluation cyclic rfl (Dense.Map.map function polynomial) root (1 : Fin 2)
  change (DensePolynomial.evalCoeffs (Mode.shiftedRoot cyclic root)
      ((polynomial.coeffs.map function).map (Element.scalar cyclic))).matrix (1 : Fin 2) 0 =
        Mode.coefficientRow (Dense.Map.map function polynomial).coeffs root (1 : Fin 2).val 0 at reading
  rw [List.Map.map_map] at reading
  unfold DensePolynomial.evalCoeffs at reading
  rw [Fold.foldl_map] at reading
  have position : (1 : Fin 2).val = 1 := rfl
  rw [position] at reading
  exact original.2.symm.trans reading

end Purelib.Polynomial.Dense.Derivative.Map

end
