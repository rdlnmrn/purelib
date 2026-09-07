import CCL.Progressive.SquarefreeEvaluation
import CCL.Riemann.LegendrePaths

/-!
# Finite squarefreeness for the Legendre cubic

The explicit Bézout identity belongs to the family itself, independently of
any particular root frame.  Keeping it in this lightweight module lets
finite period clients construct a curve without initializing a complete
worked path example.
-/

namespace CCL.Riemann.LegendreSquarefree

open CCL.Riemann.LegendrePaths

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial

/-- Explicit parameterized left Bézout coefficient. -/
def bezoutLeft (lambda : Gaussian) : GaussianPolynomial :=
  ⟨[-6 * (lambda ^ 2 - lambda + 1),
    (lambda + 1) * (4 * lambda ^ 2 - 7 * lambda + 4)]⟩

/-- Explicit parameterized right Bézout coefficient. -/
def bezoutRight (lambda : Gaussian) : GaussianPolynomial :=
  ⟨[2 * (lambda ^ 2 - lambda + 1),
    -(lambda + 1) * (2 * lambda ^ 2 - 3 * lambda + 2),
    lambda * (lambda - 1) ^ 2]⟩

theorem derivative_eval (lambda point : Gaussian) :
    (RFAP.ConstructiveGCD.derivative (polynomial lambda)).eval point =
      3 * point * point - 2 * (lambda + 1) * point + lambda := by
  unfold RFAP.ConstructiveGCD.derivative
  rw [RFAP.ComputableDerivative.eval_derivative]
  unfold polynomial
    RFAP.ComputableDerivative.evalDerivativeCoeffs
    RFAP.ComputableDerivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

theorem bezout_identity (lambda point : Gaussian) :
    (bezoutLeft lambda).eval point * (polynomial lambda).eval point +
        (bezoutRight lambda).eval point *
          (RFAP.ConstructiveGCD.derivative
            (polynomial lambda)).eval point = lambda ^ 2 * (lambda - 1) ^ 2 := by
  rw [polynomial_eval, derivative_eval]
  unfold bezoutLeft bezoutRight
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- A wholly finite squarefree certificate at every displayed nonsingular
Legendre parameter. -/
def certificate (lambda : Gaussian)
    (unitNonzero : lambda ^ 2 * (lambda - 1) ^ 2 ≠ 0) :
    RFAP.Squarefree.SquarefreeCertificate (polynomial lambda) :=
  CCL.ProgressiveSquarefree.ofEvalBezoutUnit
    (polynomial lambda) (polynomial_isZero lambda)
    (lambda ^ 2 * (lambda - 1) ^ 2) unitNonzero
    (bezoutLeft lambda) (bezoutRight lambda) (bezout_identity lambda)

end CCL.Riemann.LegendreSquarefree
