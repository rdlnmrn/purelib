module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Bivariate.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Elimination.Separated.Bezout

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.Separated.Bezout.Normalized

/-! ## Specialized rational Bézout certificates -/

/-- Scale the left separated Bézout cofactor by the inverse evaluated Sylvester scalar.

The rational parameter is embedded into the Gaussian field, and the original first-column coefficient polynomial is
retained up to this scalar multiplication. -/
def normalizedLeftCofactor (p :
  CoefficientPolynomial)
    (degreePositive : 0 < p.natDegree) (parameter : Fraction.Rational) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  let gaussianParameter :=
    Gaussian.Cast.Path.ofCoordinate parameter
  DensePolynomial.scale ((Elimination.Separated.Bezout.separatedData p).scalar.eval gaussianParameter)⁻¹
    (Elimination.Separated.Bezout.leftCofactor p degreePositive gaussianParameter)

/-- Scale the right separated Bézout cofactor by the inverse evaluated Sylvester scalar.

The rational parameter is embedded into the Gaussian field, and the original second-half coefficient polynomial is
retained up to this scalar multiplication. -/
def normalizedRightCofactor (p :
  CoefficientPolynomial)
    (degreePositive : 0 < p.natDegree) (parameter : Fraction.Rational) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  let gaussianParameter :=
    Gaussian.Cast.Path.ofCoordinate parameter
  DensePolynomial.scale ((Elimination.Separated.Bezout.separatedData p).scalar.eval gaussianParameter)⁻¹
    (Elimination.Separated.Bezout.rightCofactor p degreePositive gaussianParameter)

/-- The normalized separated cofactors give an exact Bézout identity equal to one.

The source polynomial is nonzero of positive degree, and the specialized Sylvester scalar must be nonzero at the
displayed rational parameter. -/
theorem normalizedSeparatedIdentity (p :
  CoefficientPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (parameter : Fraction.Rational)
    (scalarNonzero : (Elimination.Separated.Bezout.separatedData p).scalar.eval
      (Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0)
    (outer : Gaussian.Basic.Canonical) :
    (normalizedLeftCofactor p degreePositive parameter).eval outer *
        Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p) outer
          (Gaussian.Cast.Path.ofCoordinate parameter) +
      (normalizedRightCofactor p degreePositive parameter).eval outer *
        Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer
          (Gaussian.Cast.Path.ofCoordinate parameter) = 1 := by
  rw [normalizedLeftCofactor,
    normalizedRightCofactor, DensePolynomial.eval_scale,
    DensePolynomial.eval_scale]
  let scalar := (Elimination.Separated.Bezout.separatedData p).scalar.eval
    (Gaussian.Cast.Path.ofCoordinate parameter)
  have identity := Elimination.Separated.Bezout.separated_bezout_identity p nonzero degreePositive outer
    (Gaussian.Cast.Path.ofCoordinate parameter)
  change scalar⁻¹ * (Elimination.Separated.Bezout.leftCofactor p degreePositive
      (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
        Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p) outer
          (Gaussian.Cast.Path.ofCoordinate parameter) +
      scalar⁻¹ * (Elimination.Separated.Bezout.rightCofactor p degreePositive
        (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
          Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer
            (Gaussian.Cast.Path.ofCoordinate parameter) = 1
  calc
    scalar⁻¹ * (Elimination.Separated.Bezout.leftCofactor p degreePositive
          (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
          Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p) outer
            (Gaussian.Cast.Path.ofCoordinate parameter) +
        scalar⁻¹ * (Elimination.Separated.Bezout.rightCofactor p degreePositive
          (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
          Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer
            (Gaussian.Cast.Path.ofCoordinate parameter) =
      scalar⁻¹ *
        ((Elimination.Separated.Bezout.leftCofactor p degreePositive
            (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
            Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p) outer
              (Gaussian.Cast.Path.ofCoordinate parameter) +
          (Elimination.Separated.Bezout.rightCofactor p degreePositive
            (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
            Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer
              (Gaussian.Cast.Path.ofCoordinate parameter)) := by
                rw [Gaussian.Basic.mul_assoc,
                  Gaussian.Basic.mul_assoc]
                exact
                  (Gaussian.Basic.left_distrib _ _ _).symm
    _ = scalar⁻¹ * scalar := by rw [identity]
    _ = 1 := by
      rw [Gaussian.Field.inv_eq]
      exact Gaussian.Field.inv_mul scalar scalarNonzero
end Purelib.Polynomial.Elimination.Separated.Bezout.Normalized

end
