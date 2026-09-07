import mathlib.RFAP.CanonicalGaussian

/-!
# Executable regression table for canonical Gaussian rationals

The checks exercise structural Gaussian multiplication and total reciprocal
over quotient-free canonical coordinates in both the kernel and the compiled
evaluator.
-/

namespace RFAP.CanonicalGaussian.Gaussian

private def oneHalf : Coordinate :=
  ⟨1, 2, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

private def negativeOneHalf : Coordinate :=
  ⟨-1, 2, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

private def gammaSquared : Gaussian := ⟨0, 2⟩

private def gammaInverse : Gaussian := ⟨oneHalf, negativeOneHalf⟩

theorem regression_gamma_multiplication : gamma * gamma = gammaSquared := by
  decide

theorem regression_gamma_inverse : gamma⁻¹ = gammaInverse := by
  decide

/-- One executable Boolean used by the compiled regression runner. -/
def compiledGaussianRegressionPassed : Bool :=
  decide (gamma * gamma = gammaSquared) && decide (gamma⁻¹ = gammaInverse)

theorem compiledGaussianRegressionPassed_eq_true :
    compiledGaussianRegressionPassed = true := by
  decide

end RFAP.CanonicalGaussian.Gaussian
