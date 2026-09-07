import mathlib.RFAP.CanonicalResidual

/-!
# Executable regression for the canonical Newton residual

For `p(X) = X² - 2` at the displayed sample `3/2`, the finite Newton update
is `17/12` and its squared displacement is `1/144`.
-/

namespace RFAP.CanonicalResidual

private def threeHalves : Coordinate :=
  ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

private def seventeenTwelfths : Coordinate :=
  ⟨17, 12, by decide, ⟨⟨5, -7, by decide⟩⟩⟩

private def oneOneHundredFortyFourth : Coordinate :=
  ⟨1, 144, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

private def quadratic : Polynomial := ⟨[1, 0, -2]⟩
private def sample : Gaussian := ⟨threeHalves, 0⟩
private def expectedCenter : Gaussian := ⟨seventeenTwelfths, 0⟩

theorem regression_newton_center :
    newtonCenter quadratic sample = expectedCenter := by
  decide

theorem regression_newton_displacement :
    RFAP.CanonicalGaussian.Gaussian.normSq
        (newtonCenter quadratic sample - sample) =
      oneOneHundredFortyFourth := by
  decide

theorem regression_newton_displacement_certificate :
    RFAP.CanonicalGaussian.Gaussian.normSq
        (newtonCenter quadratic sample - sample) =
      residualSq quadratic sample *
        (RFAP.CanonicalGaussian.Gaussian.normSq
          (derivativeValue quadratic sample))⁻¹ :=
  newtonDisplacementSq quadratic sample (by decide)

/-- One executable Boolean used by the compiled regression runner. -/
def compiledResidualRegressionPassed : Bool :=
  decide (newtonCenter quadratic sample = expectedCenter) &&
    decide (RFAP.CanonicalGaussian.Gaussian.normSq
      (newtonCenter quadratic sample - sample) =
        oneOneHundredFortyFourth)

theorem compiledResidualRegressionPassed_eq_true :
    compiledResidualRegressionPassed = true := by
  decide

end RFAP.CanonicalResidual
