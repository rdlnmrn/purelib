module

public import Purelib.Polynomial.Dense.Derivative
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.NatCast
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite powers and their automatic derivatives

Polynomial powers retain the finite multiplication chain. Their readback and
derivative identities use the original coefficient fold and explicit field
laws, including at zero values of the source polynomial.
-/

public section

namespace Purelib.Polynomial.Dense.Power

open Purelib.Algebra.Field
open Purelib.Polynomial.Dense.Basic
open DensePolynomial
open Purelib.Polynomial.Dense.Derivative

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Multiply the original dense polynomial a finite number of times.

The empty multiplication is the retained constant-one table. Each successor
uses the preceding polynomial as the accumulator and the original right factor.
-/
@[expose] def power (polynomial : DensePolynomial K) : Nat → DensePolynomial K
  | 0 => constant 1
  | index + 1 => power polynomial index * polynomial

/-- Read back the finite polynomial multiplication chain as a scalar power. -/
theorem eval_power (polynomial : DensePolynomial K) (index : Nat) (point : K) :
    (power polynomial index).eval point = polynomial.eval point ^ index := by
  induction index with
  | zero => exact (eval_constant 1 point).trans (pow_zero _).symm
  | succ index previous =>
      change (power polynomial index * polynomial).eval point = _
      rewrite [eval_mul, previous, pow_succ]
      exact Eq.refl _

/-- The automatic derivative of a constant dense polynomial evaluates to zero. -/
theorem eval_derivative_constant (value point : K) :
    (derivative (constant value)).eval point = 0 := by
  rewrite [eval_derivative]
  change (0 * point + 0 : K) = 0
  ring1

/-- The derivative of the original empty coefficient table evaluates to zero. -/
theorem eval_derivative_zero (point : K) :
    (derivative (0 : DensePolynomial K)).eval point = 0 := rfl

/-- A power's automatic derivative satisfies the denominator-cleared power rule.

Multiplication by the original polynomial avoids a predecessor exponent and
keeps the statement valid at every source value, including zero.
-/
theorem eval_derivative_power_mul (polynomial : DensePolynomial K) (index : Nat) (point : K) :
    (derivative (power polynomial index)).eval point * polynomial.eval point =
      (index : K) * polynomial.eval point ^ index * (derivative polynomial).eval point := by
  induction index with
  | zero =>
      rewrite [power, eval_derivative_constant, Nat.cast_zero]
      ring1
  | succ index previous =>
      change (derivative (power polynomial index * polynomial)).eval point * polynomial.eval point = _
      rewrite [eval_derivative_mul, eval_power, Nat.cast_succ, pow_succ]
      calc
        _ = ((derivative (power polynomial index)).eval point * polynomial.eval point) * polynomial.eval point +
            polynomial.eval point ^ index * (derivative polynomial).eval point * polynomial.eval point := by ring1
        _ = _ := by rewrite [previous]; ring1

/-- The derivative of a positive polynomial power has the ordinary finite power-rule readback. -/
theorem eval_derivative_power_succ (polynomial : DensePolynomial K) (index : Nat) (point : K) :
    (derivative (power polynomial (index + 1))).eval point =
      ((index : K) + 1) * polynomial.eval point ^ index * (derivative polynomial).eval point := by
  change (derivative (power polynomial index * polynomial)).eval point = _
  rewrite [eval_derivative_mul, eval_power, eval_derivative_power_mul]
  ring1

set_option genInjectivity false in
/-- The original polynomial's square, cube and fifth power retained as one shared multiplication cache.

The cube consumes the same cached square, and the fifth power consumes the
same cached cube and square. Each defining equation binds the retained data
to these original multiplication operations without recomputing a power. -/
structure OddPowers (polynomial : DensePolynomial K) where
  /-- The cached square of the original polynomial. -/
  square : DensePolynomial K
  /-- The square cache is the original polynomial times itself. -/
  square_eq : square = polynomial * polynomial
  /-- The cached cube of the original polynomial. -/
  cube : DensePolynomial K
  /-- The cube consumes the retained square and original polynomial. -/
  cube_eq : cube = square * polynomial
  /-- The cached fifth power of the original polynomial. -/
  fifth : DensePolynomial K
  /-- The fifth power consumes the retained cube and square. -/
  fifth_eq : fifth = cube * square

constructive_injectivity OddPowers

namespace OddPowers

/-- Compute the original polynomial's square, cube and fifth power once with shared retained factors. -/
@[expose] def build (polynomial : DensePolynomial K) : OddPowers polynomial :=
  let square := polynomial * polynomial
  let cube := square * polynomial
  let fifth := cube * square
  ⟨square, rfl, cube, rfl, fifth, rfl⟩

/-- Every complete retained power cache is the original factory result on its same polynomial.

The original three defining equations fix the square, cube and fifth
polynomials. Eliminating those equalities preserves every complete field,
including the retained proof fields, without polynomial extensionality.
-/
theorem eq_build {polynomial : DensePolynomial K} (powers : OddPowers polynomial) :
    powers = build polynomial := by
  obtain ⟨square, squareEq, cube, cubeEq, fifth, fifthEq⟩ := powers
  cases squareEq
  cases cubeEq
  cases fifthEq
  rfl

/-- The retained square reads back as the square of the same original polynomial evaluation. -/
theorem square_eval {polynomial : DensePolynomial K} (powers : OddPowers polynomial) (point : K) :
    powers.square.eval point = polynomial.eval point ^ 2 := by
  rw [powers.square_eq, eval_mul, pow_two]

/-- The retained cube reads back as the cube of the same original polynomial evaluation. -/
theorem cube_eval {polynomial : DensePolynomial K} (powers : OddPowers polynomial) (point : K) :
    powers.cube.eval point = polynomial.eval point ^ 3 := by
  rw [powers.cube_eq, eval_mul, powers.square_eval]
  ring1

/-- The retained fifth power reads back through its same cached cube and square. -/
theorem fifth_eval {polynomial : DensePolynomial K} (powers : OddPowers polynomial) (point : K) :
    powers.fifth.eval point = polynomial.eval point ^ 5 := by
  rw [powers.fifth_eq, eval_mul, powers.cube_eval, powers.square_eval]
  ring1

/-- Read an odd polynomial power, retaining the original cube and fifth caches when their indices are selected.

The zero pair is the original polynomial itself. The next two pairs consume
the actual cached cube and fifth power. Larger finite indices use the
original finite polynomial power operation without changing this cache.
-/
@[expose] def odd {polynomial : DensePolynomial K} (powers : OddPowers polynomial) : Nat → DensePolynomial K
  | 0 => polynomial
  | 1 => powers.cube
  | 2 => powers.fifth
  | remaining + 3 => power polynomial (2 * (remaining + 3) + 1)

/-- Each selected cached odd power reads the same original polynomial at its actual odd exponent. -/
theorem odd_eval {polynomial : DensePolynomial K} (powers : OddPowers polynomial) (pairs : Nat) (point : K) :
    (powers.odd pairs).eval point = match pairs with
      | 0 => polynomial.eval point
      | remaining + 1 => polynomial.eval point ^ (2 * (remaining + 1) + 1) := by
  cases pairs with
  | zero => rfl
  | succ remaining =>
      cases remaining with
      | zero => exact powers.cube_eval point
      | succ remaining =>
          cases remaining with
          | zero => exact powers.fifth_eval point
          | succ remaining => exact eval_power polynomial (2 * (remaining + 3) + 1) point

/-- The retained square's exact derivative obeys the finite polynomial product rule. -/
theorem square_derivative_eval {polynomial : DensePolynomial K} (powers : OddPowers polynomial) (point : K) :
    (derivative powers.square).eval point = 2 * polynomial.eval point * (derivative polynomial).eval point := by
  rw [powers.square_eq, eval_derivative_mul]
  ring1

/-- The retained cube's derivative reuses the retained square's derivative identity. -/
theorem cube_derivative_eval {polynomial : DensePolynomial K} (powers : OddPowers polynomial) (point : K) :
    (derivative powers.cube).eval point = 3 * polynomial.eval point ^ 2 * (derivative polynomial).eval point := by
  rw [powers.cube_eq, eval_derivative_mul, powers.square_derivative_eval, powers.square_eval]
  ring1

/-- The retained fifth power's derivative reuses the original square and cube caches. -/
theorem fifth_derivative_eval {polynomial : DensePolynomial K} (powers : OddPowers polynomial) (point : K) :
    (derivative powers.fifth).eval point = 5 * polynomial.eval point ^ 4 * (derivative polynomial).eval point := by
  rw [powers.fifth_eq, eval_derivative_mul, powers.cube_derivative_eval, powers.square_derivative_eval,
    powers.cube_eval, powers.square_eval]
  ring1

end OddPowers

end Purelib.Polynomial.Dense.Power
