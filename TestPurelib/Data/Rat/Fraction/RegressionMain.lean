module

public import TestPurelib.Data.Nat.GCD
import all TestPurelib.Data.Nat.GCD

public import TestPurelib.Data.Rat.Fraction.Regression
import all TestPurelib.Data.Rat.Fraction.Regression
public import TestPurelib.Data.Gaussian.Regression
import all TestPurelib.Data.Gaussian.Regression
public import TestPurelib.Polynomial.Dense.Gaussian.Regression
import all TestPurelib.Polynomial.Dense.Gaussian.Regression
public import TestPurelib.Polynomial.Evaluation.Gaussian.NewtonResidual
import all TestPurelib.Polynomial.Evaluation.Gaussian.NewtonResidual
-- `lean --run` executes the imported compiled predicates through their private IR.

import Purelib.Data.Rat.Fraction.Arithmetic
import all Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import all Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.GCD.Scalar
import all Purelib.Data.Nat.GCD.Scalar
import Purelib.Data.Rat.Fraction.Order
import all Purelib.Data.Rat.Fraction.Order
-- The original comparison owner supplies private instance IR used by `lean --run`.
import all Purelib.Data.Rat.Fraction.Order.Basic
-- Gaussian constants, structural decisions and coordinate arithmetic execute in the predicates.
import all Purelib.Data.Gaussian.Constants
import all Purelib.Data.Gaussian.Basic
import all Purelib.Data.Gaussian.Field
import all Purelib.Data.Gaussian.Norm.Basic
-- The polynomial predicates execute these original coefficient programs and their Gaussian specializations.
import all Purelib.Polynomial.Dense.Basic
import all Purelib.Polynomial.Dense.Arithmetic
import all Purelib.Polynomial.Dense.Multiplication.Basic
import all Purelib.Polynomial.Dense.Derivative
import all Purelib.Polynomial.Dense.Evaluation
import all Purelib.Polynomial.Dense.Gaussian.Basic
import all Purelib.Polynomial.Dense.Gaussian.Arithmetic
import all Purelib.Polynomial.Dense.Gaussian.Multiplication
import all Purelib.Polynomial.Dense.Gaussian.Derivative
import all Purelib.Polynomial.Dense.Gaussian.Evaluation
-- The Newton predicate runs this original update and derivative-value body.
import all Purelib.Polynomial.Evaluation.Gaussian.NewtonResidual
import Init.Prelude
import Init.System.IO
import Init.System.IOError

open TestPurelib.Data
open TestPurelib.Data.Nat

open TestPurelib.Polynomial

@[expose] public section

/-- Execute the scalar gcd and four compiled fraction-family regression predicates and fail if any returns false. -/
def main : IO Unit :=
  if GCD.compiledRegressionPassed &&
      Rat.Fraction.Regression.compiledRegressionPassed &&
      Gaussian.Regression.compiledGaussianRegressionPassed &&
      Dense.Gaussian.Regression.compiledPolynomialRegressionPassed &&
      Evaluation.Gaussian.NewtonResidual.compiledResidualRegressionPassed then
    pure ()
  else
    throw (IO.userError "compiled fraction-family regression failed")
