module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Algebra.Field.ExplicitField
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

/-- Evaluation at the origin reads the same original constant coefficient. -/
theorem eval_at_zero (polynomial : CoefficientPolynomial) :
    eval polynomial 0 = Coefficient.coefficient polynomial 0 := by
  cases polynomial with
  | mk coefficients =>
      cases coefficients with
      | nil => rfl
      | cons head tail =>
          change head + 0 * evalCoeffs tail 0 = head
          rewrite [Gaussian.Basic.zero_mul, Gaussian.Basic.add_zero]
          rfl

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

/-- Evaluation of the retained finite convolution is the product of the original two Horner values. -/
theorem eval_mul (left right : CoefficientPolynomial) (input : Gaussian.Basic.Canonical) :
    eval (Arithmetic.mul left right) input = eval left input * eval right input := by
  cases left with
  | mk left =>
      induction left with
      | nil =>
          change 0 = 0 * eval right input
          exact (Gaussian.Basic.zero_mul _).symm
      | cons head tail inductionHypothesis =>
          rewrite [Arithmetic.mul_cons, eval_add, eval_scale, eval_shift, inductionHypothesis]
          change head * eval right input + input * (eval ⟨tail⟩ input * eval right input) =
            (head + input * eval ⟨tail⟩ input) * eval right input
          ring1

/-- Split one retained Horner table at a displayed degree without changing either original coefficient block. -/
private theorem evalCoeffs_take_drop (input : Gaussian.Basic.Canonical) :
    (degree : Nat) → (coefficients : List Gaussian.Basic.Canonical) →
      evalCoeffs coefficients input = evalCoeffs (coefficients.take degree) input +
        input ^ degree * evalCoeffs (coefficients.drop degree) input
  | 0, coefficients => by
      change evalCoeffs coefficients input = 0 + 1 * evalCoeffs coefficients input
      rewrite [Gaussian.Basic.one_mul, Gaussian.Basic.zero_add]
      rfl
  | degree + 1, [] => by
      change 0 = 0 + input ^ (degree + 1) * 0
      rewrite [Gaussian.Basic.mul_zero, Gaussian.Basic.add_zero]
      rfl
  | degree + 1, head :: tail => by
      change head + input * evalCoeffs tail input =
        (head + input * evalCoeffs (tail.take degree) input) +
          input ^ (degree + 1) * evalCoeffs (tail.drop degree) input
      rewrite [evalCoeffs_take_drop input degree tail, pow_succ]
      ring1

/-- The original finite polynomial is its retained low coefficient block plus the shifted literal higher tail.

The displayed degree may exceed the coefficient-list length. The same take
and drop operations retain all supplied coefficients, without normalization,
zero tests, successful-reduction assumptions or a new polynomial owner.
-/
theorem eval_splitAt (polynomial : CoefficientPolynomial) (degree : Nat) (input : Gaussian.Basic.Canonical) :
    eval polynomial input = eval ⟨polynomial.coefficients.take degree⟩ input +
      input ^ degree * eval (Arithmetic.divideByPower degree polynomial) input :=
  evalCoeffs_take_drop input degree polynomial.coefficients

/-- At a nonzero coordinate, division by a power separates the same finite principal block and literal regular tail.

The actual coordinate witness justifies cancelling the displayed power.
Every low coefficient remains in the finite numerator of the principal
block; the regular part consumes the original dropped coefficient tail.
-/
theorem eval_mul_inverse_power (polynomial : CoefficientPolynomial) (degree : Nat)
    (input : Gaussian.Basic.Canonical) (nonzero : input ≠ 0) :
    eval polynomial input * (input ^ degree)⁻¹ =
      eval ⟨polynomial.coefficients.take degree⟩ input * (input ^ degree)⁻¹ +
        eval (Arithmetic.divideByPower degree polynomial) input := by
  have powerNonzero := Gaussian.Power.pow_ne_zero_direct input nonzero degree
  calc
    _ = (eval ⟨polynomial.coefficients.take degree⟩ input +
        input ^ degree * eval (Arithmetic.divideByPower degree polynomial) input) * (input ^ degree)⁻¹ :=
      congrArg (fun value => value * (input ^ degree)⁻¹) (eval_splitAt polynomial degree input)
    _ = eval ⟨polynomial.coefficients.take degree⟩ input * (input ^ degree)⁻¹ +
        eval (Arithmetic.divideByPower degree polynomial) input * (input ^ degree * (input ^ degree)⁻¹) := by ring1
    _ = _ := by
      rewrite [Algebra.Field.ExplicitField.mul_inv_cancel _ powerNonzero, Gaussian.Basic.mul_one]
      rfl

/-- A zero initial coefficient block factors from the same finite Horner table as an exact indeterminate power. -/
private theorem evalCoeffs_power_factor (input : Gaussian.Basic.Canonical) :
    (degree : Nat) → (coefficients : List Gaussian.Basic.Canonical) →
    (∀ index, index < degree → Coefficient.coefficientList coefficients index = 0) →
      evalCoeffs coefficients input = input ^ degree * evalCoeffs (coefficients.drop degree) input
  | 0, coefficients, _ => by
      change evalCoeffs coefficients input = 1 * evalCoeffs coefficients input
      exact (Gaussian.Basic.one_mul _).symm
  | degree + 1, [], _ => by
      change 0 = input ^ (degree + 1) * 0
      exact (Gaussian.Basic.mul_zero _).symm
  | degree + 1, head :: tail, zero => by
      have headZero : head = 0 := zero 0 (Nat.zero_lt_succ degree)
      change head + input * evalCoeffs tail input =
        input ^ (degree + 1) * evalCoeffs (tail.drop degree) input
      rewrite [headZero, Gaussian.Basic.zero_add,
        evalCoeffs_power_factor input degree tail (fun index bound => zero (index + 1) (Nat.succ_lt_succ bound)),
        pow_succ]
      ring1

/-- A finite polynomial with zero low coefficients factors by that exact power through its literal retained tail. -/
theorem eval_eq_power_mul_divideByPower (polynomial : CoefficientPolynomial) (degree : Nat)
    (zero : ∀ index, index < degree → Coefficient.coefficient polynomial index = 0)
    (input : Gaussian.Basic.Canonical) :
    eval polynomial input = input ^ degree * eval (Arithmetic.divideByPower degree polynomial) input :=
  evalCoeffs_power_factor input degree polynomial.coefficients zero

/-- Increasing the retained low-block bound adds exactly the original next coefficient and its displayed power.

The induction follows the original coefficient spine and bound together.
Empty or short tables supply their original zero-extended coefficient.
-/
private theorem evalCoeffs_take_succ (point : Gaussian.Basic.Canonical) :
    (order : Nat) → (coefficients : List Gaussian.Basic.Canonical) →
      evalCoeffs (coefficients.take (order + 1)) point = evalCoeffs (coefficients.take order) point +
        point ^ order * Coefficient.coefficientList coefficients order
  | 0, [] => by
      change (0 : Gaussian.Basic.Canonical) = 0 + 1 * 0
      ring1
  | 0, head :: tail => by
      change head + point * 0 = 0 + 1 * head
      ring1
  | order + 1, [] => by
      change (0 : Gaussian.Basic.Canonical) = 0 + point ^ (order + 1) * 0
      ring1
  | order + 1, head :: tail => by
      change head + point * evalCoeffs (tail.take (order + 1)) point =
        (head + point * evalCoeffs (tail.take order) point) +
          point ^ (order + 1) * Coefficient.coefficientList tail order
      rw [evalCoeffs_take_succ point order tail, pow_succ]
      ring1

/-- The original finite reciprocal expression splits into its nonlogarithmic polar block, one logarithmic term and tail.

The coefficient at the displayed original order remains a separate scalar.
The same coordinate's nonzero witness cancels the exact adjacent powers;
the regular tail is the original literal dropped coefficient table.
-/
theorem eval_polar_split (source : CoefficientPolynomial) (order : Nat)
    (point : Gaussian.Basic.Canonical) (nonzero : point ≠ 0) :
    eval source point * (point ^ (order + 1))⁻¹ =
      eval ⟨source.coefficients.take order⟩ point * (point ^ (order + 1))⁻¹ +
        Coefficient.coefficient source order * point⁻¹ +
        eval (Arithmetic.divideByPower (order + 1) source) point := by
  rw [eval_mul_inverse_power source (order + 1) point nonzero]
  change evalCoeffs (source.coefficients.take (order + 1)) point * (point ^ (order + 1))⁻¹ + _ = _
  rw [evalCoeffs_take_succ]
  change (evalCoeffs (source.coefficients.take order) point +
    point ^ order * Coefficient.coefficient source order) * (point ^ (order + 1))⁻¹ +
      eval (Arithmetic.divideByPower (order + 1) source) point =
    evalCoeffs (source.coefficients.take order) point * (point ^ (order + 1))⁻¹ +
      Coefficient.coefficient source order * point⁻¹ + eval (Arithmetic.divideByPower (order + 1) source) point
  have unit := Algebra.Field.ExplicitField.mul_inv_cancel (point ^ order)
    (Gaussian.Power.pow_ne_zero_direct point nonzero order)
  rw [Algebra.Field.ExplicitField.inverse_pow_nonzero nonzero] at unit
  have cancelled : point ^ order * (point ^ (order + 1))⁻¹ = point⁻¹ := by
    rw [Algebra.Field.ExplicitField.inverse_pow_nonzero nonzero, pow_succ]
    calc
      _ = (point ^ order * point⁻¹ ^ order) * point⁻¹ := by ring1
      _ = point⁻¹ := by rw [unit, Gaussian.Basic.one_mul]
  calc
    _ = evalCoeffs (source.coefficients.take order) point * (point ^ (order + 1))⁻¹ +
        Coefficient.coefficient source order * (point ^ order * (point ^ (order + 1))⁻¹) +
        eval (Arithmetic.divideByPower (order + 1) source) point := by ring1
    _ = _ := by rw [cancelled]

/-- Evaluate a finite Gaussian table by its direct Horner recurrence.

Each retained head is added to the input times its remaining table value.
The empty spine supplies zero without changing coefficient order. -/
@[expose] def evalList : List Gaussian.Basic.Canonical → Gaussian.Basic.Canonical → Gaussian.Basic.Canonical
  | [], _ => 0
  | coefficient :: remaining, input =>
      coefficient + input * evalList remaining input

end Purelib.Polynomial.Ascending.Gaussian.Evaluation
end
