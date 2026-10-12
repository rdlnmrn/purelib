module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Leading
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive squarefreeness of coprime products

The certificates below use only finite dense polynomial arithmetic, the
derivative product rule and displayed Bézout identities.  Their conversion
back to the executable Euclidean certificate uses the existing bounded
coefficient-candidate test, not extensionality over an infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Constants

/-- Every displayed nonzero constant is squarefree, including constants
whose square root is not a Gaussian-rational coefficient. -/
def constant (value : Gaussian.Basic.Canonical) (nonzero :
  value ≠ 0) :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate (DensePolynomial.constant value) :=
      open Purelib.Algebra.Field in by
  apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity _ _
    (Or.inl (Dense.Leading.LeadingTerm.constant nonzero).nonzero)
    (DensePolynomial.constant value⁻¹) 0
  intro point
  simp only [DensePolynomial.eval_constant, DensePolynomial.eval_zero, zero_mul, add_zero]
  rw [Gaussian.Basic.mul_comm]
  exact (ExplicitField.mul_inv_cancel value nonzero).symm
end Purelib.Polynomial.Dense.Gaussian.Squarefree.Constants

end
