module

public import Test.Data.Rat.Fraction.Regression
import all Test.Data.Rat.Fraction.Regression
public import Test.Data.Gaussian.Regression
import all Test.Data.Gaussian.Regression
public import Test.Polynomial.Dense.Gaussian.Regression
import all Test.Polynomial.Dense.Gaussian.Regression
public import Test.Polynomial.Evaluation.Gaussian.NewtonResidual
import all Test.Polynomial.Evaluation.Gaussian.NewtonResidual
-- `lean --run` executes the imported compiled predicates through their private IR.

import Purelib.Data.Rat.Fraction.Arithmetic
import all Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import all Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.GCD.Scalar
import all Purelib.Data.Nat.GCD.Scalar
import Purelib.Data.Rat.Fraction.Order
import all Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Init.System.IO
import Init.System.IOError

open Test.Data

open Test.Polynomial

@[expose] public section

/-- Execute the four compiled fraction-family regression predicates and fail if any returns false. -/
def main : IO Unit :=
  if Rat.Fraction.Regression.compiledRegressionPassed &&
      Gaussian.Regression.compiledGaussianRegressionPassed &&
      Dense.Gaussian.Regression.compiledPolynomialRegressionPassed &&
      Evaluation.Gaussian.NewtonResidual.compiledResidualRegressionPassed then
    pure ()
  else
    throw (IO.userError "compiled fraction-family regression failed")
