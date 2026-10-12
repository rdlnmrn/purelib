module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Gaussian.Arithmetic
public import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Coefficient

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Horner evaluation of ascending Gaussian coefficient tables

The nominal polynomial retains its finite table from constant term upward.
Right-fold evaluation and direct list recursion keep that order, while scalar
certificates transport zero padding, addition and scaling.
-/

public section
namespace Purelib.Polynomial.Ascending.Gaussian.Evaluation

open Purelib.Data
open Purelib.Polynomial

/-- Evaluate an ascending Gaussian coefficient table by Horner folding.

The original right fold combines each retained coefficient with the input
times its tail value, starting from Gaussian zero. -/
@[expose] def evalCoeffs (coefficients : List Gaussian.Basic.Canonical) (input : Gaussian.Basic.Canonical) :
  Gaussian.Basic.Canonical :=
  coefficients.foldr (fun coefficient total => coefficient + input * total) 0

/-- Evaluate the retained Gaussian polynomial by finite Horner recursion. -/
@[expose] def eval (polynomial : CoefficientPolynomial) (input : Gaussian.Basic.Canonical) :
  Gaussian.Basic.Canonical :=
  evalCoeffs polynomial.coefficients input

/-- The empty zero polynomial evaluates to zero. -/
@[simp] theorem eval_zero (input : Gaussian.Basic.Canonical) : eval Ascending.Gaussian.Basic.zero input = 0 := rfl

/-- A constant Gaussian polynomial evaluates to its retained value. -/
@[simp] theorem eval_constant (value input : Gaussian.Basic.Canonical) :
    eval (Ascending.Gaussian.Basic.constant value) input = value := by
  change value + input * 0 = value
  rw [Gaussian.Basic.mul_zero, _root_.add_zero]

/-- The empty Gaussian coefficient table has Horner value zero. -/
@[simp] theorem evalCoeffs_nil (input : Gaussian.Basic.Canonical) : evalCoeffs [] input = 0 := rfl

/-- A nonempty Gaussian table evaluates as its head plus the input times its tail value. -/
@[simp] theorem evalCoeffs_cons (head : Gaussian.Basic.Canonical) (tail : List Gaussian.Basic.Canonical)
    (input : Gaussian.Basic.Canonical) :
    evalCoeffs (head :: tail) input = head + input * evalCoeffs tail input := rfl

/-- A Gaussian coefficient list with every zero-extended coefficient zero evaluates to zero. -/
theorem evalCoeffs_zero (input : Gaussian.Basic.Canonical) : ∀ (coefficients : List Gaussian.Basic.Canonical),
    (∀ degree, Ascending.Gaussian.Coefficient.coefficientList coefficients degree = 0) → evalCoeffs coefficients input =
      0
  | [], _ => rfl
  | head :: tail, equal => by
      rw [evalCoeffs_cons, show head = 0 from equal 0,
        Purelib.Polynomial.Ascending.Gaussian.Evaluation.evalCoeffs_zero input tail (fun degree => equal (degree + 1)),
          Gaussian.Basic.mul_zero, _root_.add_zero]

/-- Coefficientwise equal Gaussian lists have equal Horner values.

The lists may have different lengths or trailing zeros; structural recursion uses equality of their zero-extended
coefficients. -/
theorem evalCoeffs_eq (input : Gaussian.Basic.Canonical) : ∀ (left right : List Gaussian.Basic.Canonical),
    (∀ degree, Ascending.Gaussian.Coefficient.coefficientList left degree =
      Ascending.Gaussian.Coefficient.coefficientList right degree) →
      evalCoeffs left input = evalCoeffs right input
  | [], right, equal =>
      (evalCoeffs_zero input right (fun degree => (equal degree).symm)).symm
  | head :: tail, [], equal =>
      evalCoeffs_zero input (head :: tail) equal
  | left :: leftTail, right :: rightTail, equal => by
      rw [evalCoeffs_cons, evalCoeffs_cons, show left = right from equal 0,
        Purelib.Polynomial.Ascending.Gaussian.Evaluation.evalCoeffs_eq input leftTail rightTail (fun degree => equal
          (degree + 1))]

/-- Coefficientwise equal Gaussian polynomials evaluate equally at every supplied input. -/
theorem eval_eq_of_coefficientwise {left right : CoefficientPolynomial}
    (equal : Ascending.Gaussian.Coefficient.CoefficientwiseEqual left right) (input : Gaussian.Basic.Canonical) :
    eval left input = eval right input :=
  evalCoeffs_eq input left.coefficients right.coefficients equal

/-- Gaussian Horner evaluation preserves padded coefficient-list addition.

Empty spines retain the unchanged other table. Paired heads use the recursive
tail equality and exact scalar distributivity at the same Gaussian input. -/
theorem evalCoeffs_add (input : Gaussian.Basic.Canonical) : ∀ (left right : List Gaussian.Basic.Canonical),
    evalCoeffs (List.Gaussian.Arithmetic.addCoefficients left right) input =
      evalCoeffs left input + evalCoeffs right input
  | [], right => by
      change evalCoeffs right input = 0 + evalCoeffs right input
      exact (_root_.zero_add _).symm
  | head :: tail, [] => by
      change evalCoeffs (head :: tail) input = evalCoeffs (head :: tail) input + 0
      exact (_root_.add_zero _).symm
  | left :: leftTail, right :: rightTail => by
      rw [List.Gaussian.Arithmetic.addCoefficients, evalCoeffs_cons, evalCoeffs_cons, evalCoeffs_cons,
        Purelib.Polynomial.Ascending.Gaussian.Evaluation.evalCoeffs_add input leftTail rightTail]
      ring1

/-- Evaluation preserves Gaussian polynomial addition. -/
@[simp] theorem eval_add (left right : CoefficientPolynomial) (input : Gaussian.Basic.Canonical) :
    eval (Ascending.Gaussian.Arithmetic.add left right) input = eval left input + eval right input :=
  evalCoeffs_add input left.coefficients right.coefficients

/-- Scaling each Gaussian coefficient scales the retained Horner value.

The empty table uses multiplication by zero. A nonempty table retains the
same coefficient order and applies scalar distributivity to its recursive tail. -/
theorem evalCoeffs_scale (factor input : Gaussian.Basic.Canonical) : ∀ coefficients : List Gaussian.Basic.Canonical,
    evalCoeffs (coefficients.map (factor * ·)) input = factor * evalCoeffs coefficients input
  | [] => by
      change 0 = factor * 0
      exact (Gaussian.Basic.mul_zero factor).symm
  | head :: tail => by
      rw [List.map_cons, evalCoeffs_cons, evalCoeffs_cons,
        Purelib.Polynomial.Ascending.Gaussian.Evaluation.evalCoeffs_scale factor input tail]
      ring1

/-- Evaluation commutes with Gaussian coefficient scaling. -/
@[simp] theorem eval_scale (factor : Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial) (input
  : Gaussian.Basic.Canonical) :
    eval (Ascending.Gaussian.Arithmetic.scale factor polynomial) input = factor * eval polynomial input :=
  evalCoeffs_scale factor input polynomial.coefficients

/-- A one-degree shift multiplies the polynomial value by the input. -/
@[simp] theorem eval_shift (polynomial : CoefficientPolynomial) (input : Gaussian.Basic.Canonical) :
    eval (Ascending.Gaussian.Arithmetic.shift polynomial) input = input * eval polynomial input := by
  change 0 + input * eval polynomial input = _
  exact _root_.zero_add _

/-- Evaluate a finite Gaussian table by its direct Horner recurrence.

Each retained head is added to the input times its remaining table value.
The empty spine supplies zero without changing coefficient order. -/
@[expose] def evalList : List Gaussian.Basic.Canonical → Gaussian.Basic.Canonical → Gaussian.Basic.Canonical
  | [], _ => 0
  | coefficient :: remaining, input =>
      coefficient + input * evalList remaining input

end Purelib.Polynomial.Ascending.Gaussian.Evaluation
end
