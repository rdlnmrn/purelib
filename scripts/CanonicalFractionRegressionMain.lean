import mathlib.RFAP.CanonicalFractionRegression
import mathlib.RFAP.CanonicalGaussianRegression
import mathlib.RFAP.CanonicalPolynomialRegression
import mathlib.RFAP.CanonicalResidualRegression

def main : IO Unit :=
  if RFAP.CanonicalFraction.compiledRegressionPassed &&
      RFAP.CanonicalGaussian.Gaussian.compiledGaussianRegressionPassed &&
      RFAP.CanonicalPolynomial.compiledPolynomialRegressionPassed &&
      RFAP.CanonicalResidual.compiledResidualRegressionPassed then
    pure ()
  else
    throw (IO.userError "compiled canonical-number regression failed")
