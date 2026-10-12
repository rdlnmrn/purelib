module
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic

open Purelib.Polynomial

section
/-!
# Executable squarefreeness under finite coefficient reversal

Clear the reciprocal denominators in the original finite Bézout identity.
This gives a power of the coordinate in the ideal of the reversed polynomial
and its derivative. The reversed constant coefficient is the original
nonzero leading coefficient; a finite recursive Bézout calculation removes
that coordinate power. No root enumeration or nonzero affine constant term
is assumed.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Transport

/-- Transport squarefreeness through a finite coefficient identity. Only
the explicit bounded candidate list of the difference is used to obtain the
derivative equality. -/
def ofSameValues (source target :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (targetNonzero : target.isZero = false)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate source) (same : ∀ point, source.eval
      point = target.eval point) :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate target := by
  have difference := Dense.Gaussian.NonzeroEvaluation.difference_isZero_of_candidate_evals source target
    (fun point _ => same point)
  apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity target (Dense.Gaussian.GCD.derivative target)
    (Or.inl targetNonzero) squarefree.left squarefree.right
  intro point
  have derivativeSame := Dense.Derivative.eval_derivative_eq_of_sub_isZero difference point
  change (Dense.Gaussian.GCD.derivative source).eval point =
    (Dense.Gaussian.GCD.derivative target).eval point at derivativeSame
  have identity := squarefree.identity point
  rw [same, derivativeSame] at identity
  exact identity
end Purelib.Polynomial.Dense.Gaussian.Squarefree.Transport

end
