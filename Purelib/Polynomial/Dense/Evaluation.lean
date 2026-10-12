module
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Fold
-- The public reverse-cast law retains the original ascending evaluation owner.
public import Purelib.Polynomial.Ascending.Integer.Basic
public import Purelib.Polynomial.Dense.Basic

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

/-!
# Descending finite Horner evaluation

Evaluation consumes the retained coefficient spine with its original scalar
multiply-and-add step. Scalar expansion, leading-zero trimming and the
original reversal accumulator relate that same scan to normalized data and
ascending integer coefficient evaluation in an explicit field.
-/

namespace Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Algebra.Field
open Purelib.Polynomial

open Purelib.Data.List

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Horner evaluation is a recursion over the finite coefficient list.

The retained finite list is consumed from highest degree to constant term.
Every original coefficient uses the same supplied point and scalar operations. -/
@[expose] public def evalCoeffs (x : K) (cs : List K) : K :=
  cs.foldl (fun acc a => acc * x + a) 0

/-- Evaluate a dense polynomial by descending Horner recursion over its retained coefficients.

The retained coefficient list supplies the original descending Horner scan.
No coefficient conversion or normalization is performed during evaluation. -/
@[expose] public def eval (p : Dense.Basic.DensePolynomial K) (x : K) : K :=
  Purelib.Polynomial.Dense.Basic.DensePolynomial.evalCoeffs x p.coeffs

omit [DecidableEq K] in
/-- Evaluating a constant polynomial returns its single retained coefficient. -/
@[simp] public theorem eval_constant (a x : K) : (constant a).eval x = a := by
  change 0 * x + a = a
  rw [zero_mul, zero_add]

omit [DecidableEq K] in
/-- The empty dense zero polynomial evaluates to zero. -/
@[simp] public theorem eval_zero (x : K) : (0 : Dense.Basic.DensePolynomial K).eval x = 0 := rfl

omit [DecidableEq K] in
/-- Descending Horner evaluation of an empty coefficient list is zero. -/
@[simp] public theorem evalCoeffs_nil (x : K) : evalCoeffs x [] = 0 := rfl

omit [DecidableEq K] in
/-- Horner evaluation of a nonempty list starts at its leading coefficient. -/
@[simp] public theorem evalCoeffs_cons (x a : K) (as : List K) :
    evalCoeffs x (a :: as) = as.foldl (fun acc b => acc * x + b) a := by
  change as.foldl (fun acc b => acc * x + b) (0 * x + a) = _
  rw [zero_mul, zero_add]

omit [DecidableEq K] in
/-- A leading zero does not change finite Horner evaluation. -/
public theorem evalCoeffs_cons_zero (x : K) (as : List K) :
    evalCoeffs x (0 :: as) = evalCoeffs x as := by
  change as.foldl (fun acc b => acc * x + b) (0 * x + 0) = _
  rw [zero_mul, zero_add]
  rfl

omit [DecidableEq K] in
/-- A retained Horner accumulator contributes its scaled value to the final evaluation.

The scaling exponent is the length of the finite remaining coefficient list. -/
private theorem foldl_horner_expansion (x : K) :
    ∀ (coefficients : List K) (accumulator : K),
      coefficients.foldl (fun value coefficient => value * x + coefficient)
          accumulator =
        accumulator * x ^ coefficients.length +
          evalCoeffs x coefficients
  | [], accumulator => by
      change accumulator = accumulator * x ^ 0 + 0
      rw [pow_zero, mul_one, add_zero]
  | coefficient :: coefficients, accumulator => by
      rw [List.foldl_cons,
        foldl_horner_expansion x coefficients
          (accumulator * x + coefficient)]
      have coefficientExpansion :
          evalCoeffs x (coefficient :: coefficients) =
            coefficient * x ^ coefficients.length +
              evalCoeffs x coefficients := by
        rw [evalCoeffs_cons]
        exact foldl_horner_expansion x coefficients coefficient
      rw [coefficientExpansion]
      rw [List.length_cons, pow_succ, add_mul]
      have regrouped : (accumulator * x) * x ^ coefficients.length =
          accumulator * (x ^ coefficients.length * x) := by
        rw [mul_assoc, mul_comm x (x ^ coefficients.length)]
      rw [regrouped]
      exact add_assoc _ _ _

omit [DecidableEq K] in
/-- Exact finite monomial expansion of one high-to-low Horner list step.

The original leading coefficient contributes at the retained tail length.
The unchanged tail supplies its own descending Horner evaluation. -/
public theorem evalCoeffs_cons_expansion (x a : K) (as : List K) :
    evalCoeffs x (a :: as) =
      a * x ^ as.length + evalCoeffs x as := by
  rw [evalCoeffs_cons]
  exact foldl_horner_expansion x as a

/-- Removing a finite leading zero prefix preserves Horner evaluation.

Each original zero head leaves the Horner starting accumulator unchanged.
The original Boolean zero test discards exactly those retained heads. -/
public theorem evalCoeffs_dropWhile_zero (x : K) (cs : List K) :
    evalCoeffs x (cs.dropWhile (· = 0)) = evalCoeffs x cs := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a = 0
      · rw [DropWhile.cons_of_true _ a as (decide_eq_true ha), ha,
          evalCoeffs_cons_zero]
        exact ih
      · rw [DropWhile.cons_of_false _ a as (decide_eq_false ha)]

/-- Normalization preserves every supplied polynomial evaluation.

Normalization removes the original finite leading-zero prefix.
The retained Horner scan has the same value before and after that removal. -/
@[simp] public theorem eval_normalize (p : Dense.Basic.DensePolynomial K) (x : K) :
    p.normalize.eval x = p.eval x := evalCoeffs_dropWhile_zero x p.coeffs
omit [DecidableEq K] in
/-- Descending evaluation of reversed integer casts equals the original ascending evaluation.

The original reversal accumulator turns the left Horner fold into a right fold
on the same retained integer table. Each original cast and scalar step is
transported into the supplied explicit field without identifying fold functions. -/
public theorem evalCoeffs_reverse_intCast (coefficients : List Int) (point : K) :
    evalCoeffs point (coefficients.reverse.map fun coefficient : Int => (coefficient : K)) =
      Ascending.Integer.Basic.eval coefficients point := by
  have folded : ∀ values : List Int,
      values.foldr (fun (coefficient : Int) state => state * point + (coefficient : K)) 0 =
        Ascending.Integer.Basic.eval values point := by
    intro values
    induction values with
    | nil => rfl
    | cons coefficient remaining ih =>
        change remaining.foldr (fun (value : Int) state => state * point + (value : K)) 0 *
          point + (coefficient : K) = Ascending.Integer.Basic.eval (coefficient :: remaining) point
        rewrite [ih, Ascending.Integer.Basic.eval_cons]
        ring0
  unfold evalCoeffs
  rewrite [Fold.foldl_map, Fold.foldl_reverse]
  exact folded coefficients

end Purelib.Polynomial.Dense.Basic.DensePolynomial

namespace Purelib.Polynomial.Dense.Evaluation

/-- The shared finite Horner clause at the supplied point. -/
@[expose] public def step {K : Type*} [Mul K] [Add K] (point accumulator coefficient : K) : K :=
  accumulator * point + coefficient

/-- Descending finite Horner evaluation retaining the supplied accumulator.

The original finite fold consumes the retained descending list using the
supplied starting accumulator and unchanged scalar step. -/
@[expose] public def evalCoeffsFrom {K : Type*} [Mul K] [Add K]
    (point accumulator : K) (coefficients : List K) : K :=
  coefficients.foldl (step point) accumulator

/-- An empty Horner input preserves its supplied accumulator. -/
@[simp] public theorem evalCoeffsFrom_nil {K : Type*} [Mul K] [Add K]
    (point accumulator : K) : evalCoeffsFrom point accumulator [] = accumulator := rfl

/-- Consume one coefficient by updating the accumulator, then evaluate the remaining descending list. -/
@[simp] public theorem evalCoeffsFrom_cons {K : Type*} [Mul K] [Add K]
    (point accumulator coefficient : K) (remaining : List K) :
    evalCoeffsFrom point accumulator (coefficient :: remaining) =
      evalCoeffsFrom point (step point accumulator coefficient) remaining := rfl

end Purelib.Polynomial.Dense.Evaluation
