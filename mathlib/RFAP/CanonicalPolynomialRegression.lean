import mathlib.RFAP.CanonicalPolynomial

/-!
# Executable regression table for canonical dense polynomials

The closed checks exercise every operation in the dense-polynomial pilot in
both the kernel and the compiled evaluator.
-/

namespace RFAP.CanonicalPolynomial

private def variablePlusOne : Polynomial := ⟨[1, 1]⟩
private def variableMinusOne : Polynomial := ⟨[1, -1]⟩
private def displayedWithLeadingZeros : Polynomial := ⟨[0, 0, 1, 1]⟩
private def twiceVariable : Polynomial := ⟨[2, 0]⟩
private def squareMinusOne : Polynomial := ⟨[1, 0, -1]⟩
private def onePolynomial : Polynomial := ⟨[1]⟩
private def valueAtGamma : Gaussian := ⟨-1, 2⟩

theorem regression_normalize :
    normalize displayedWithLeadingZeros = variablePlusOne := by
  decide

theorem regression_add : add variablePlusOne variableMinusOne = twiceVariable := by
  decide

theorem regression_mul : mul variablePlusOne variableMinusOne = squareMinusOne := by
  decide

theorem regression_derivative : derivative variablePlusOne = onePolynomial := by
  decide

theorem regression_horner : eval squareMinusOne RFAP.CanonicalGaussian.Gaussian.gamma =
    valueAtGamma := by
  decide

/-- One executable Boolean used by the compiled regression runner. -/
def compiledPolynomialRegressionPassed : Bool :=
  decide (normalize displayedWithLeadingZeros = variablePlusOne) &&
    decide (add variablePlusOne variableMinusOne = twiceVariable) &&
    decide (mul variablePlusOne variableMinusOne = squareMinusOne) &&
    decide (derivative variablePlusOne = onePolynomial) &&
    decide (eval squareMinusOne RFAP.CanonicalGaussian.Gaussian.gamma =
      valueAtGamma)

theorem compiledPolynomialRegressionPassed_eq_true :
    compiledPolynomialRegressionPassed = true := by
  decide

end RFAP.CanonicalPolynomial
