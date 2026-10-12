module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Quadratic.RationalBounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

/-!
# Dense rational quadratic lower bounds

A certificate retains a nonnegative floor and its pointwise bound for one
descending rational coefficient table. Preparation normalizes leading zeroes
once and transfers the resulting quadratic or zero certificate to the supplied polynomial.
-/

namespace Purelib.Polynomial.Dense.Rational.Bounds.Quadratic

open Purelib.Data.Rat
open Purelib.Polynomial

set_option genInjectivity false in
/-- A nonnegative global lower bound for the absolute value of a retained rational polynomial.

The bound is accompanied by a pointwise proof for every rational parameter; zero is a valid inconclusive lower bound. -/
public structure Certificate (polynomial : CoordinatePolynomial) where
  /-- The retained rational lower bound for the absolute polynomial value. -/ coordinateFloor : Fraction.Rational
  /-- The retained coordinate floor is nonnegative. -/ nonnegative : 0 ≤ coordinateFloor
  /-- The retained floor bounds the absolute polynomial value at every supplied rational parameter. -/ lower :
    (parameter : Fraction.Rational) → coordinateFloor ≤ Fraction.abs (polynomial.eval parameter)

constructive_injectivity Certificate

/-- Give a rational polynomial the zero lower-bound certificate.

The canonical rational magnitude is nonnegative at every parameter. The
certificate therefore retains zero without inspecting the coefficient table. -/
@[expose] public def Certificate.zero (polynomial : CoordinatePolynomial) : Certificate
  polynomial :=
  ⟨0, le_rfl, fun parameter => Fraction.Order.Arithmetic.abs_nonneg_direct (polynomial.eval parameter)⟩

set_option backward.match.sparseCases false in
/-- Compute a global floor from a displayed quadratic coefficient triple, otherwise retain the zero floor.

The result is indexed by the original descending coefficient table and carries the pointwise lower-bound proof. -/
@[expose] public def ofCoefficients : (coefficients : List Fraction.Rational) → Certificate ⟨coefficients⟩
  | [a, b, c] =>
      { coordinateFloor := Quadratic.RationalBounds.quadraticFloor a b c
        nonnegative := Quadratic.RationalBounds.quadraticFloor_nonnegative a b c
        lower := by
          intro parameter
          simpa only [DensePolynomial.eval,
            DensePolynomial.evalCoeffs, List.foldl,
            Fraction.Field.zero_mul_direct, _root_.zero_add, Quadratic.RationalBounds.value] using
              Quadratic.RationalBounds.quadraticFloor_le_abs a b c parameter }
  | coefficients => Certificate.zero ⟨coefficients⟩

/-- Normalize leading zero coefficients before selecting a quadratic floor.

The normalized table is computed once. Its retained floor and nonnegativity
certificate are reused, while evaluation equality transfers the pointwise bound
to the supplied polynomial. -/
@[expose] public def prepare (polynomial : CoordinatePolynomial) : Certificate
  polynomial :=
  let computed := ofCoefficients polynomial.normalize.coeffs
  { coordinateFloor := computed.coordinateFloor
    nonnegative := computed.nonnegative
    lower := by
      intro parameter
      have bound := computed.lower parameter
      change computed.coordinateFloor ≤ Fraction.abs (polynomial.normalize.eval parameter) at bound
      rw [DensePolynomial.eval_normalize] at bound
      exact bound }
end Purelib.Polynomial.Dense.Rational.Bounds.Quadratic
