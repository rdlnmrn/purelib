module

public import Purelib.Polynomial.Ascending.Gaussian.Secant
public import Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Shared finite secant kernels for original Gaussian coefficient tables -/

public section

namespace Purelib.Polynomial.Ascending.Gaussian.Evaluation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Specialize the shared original Horner secant traversal to the actual Gaussian tail evaluator. -/
@[expose] def coefficientsKernel (x y : Canonical) (coefficients : List Canonical) : Canonical :=
  Ascending.Gaussian.Secant.coefficientsKernel (fun point table => evalCoeffs table point) x y coefficients

/-- The actual retained Gaussian table's finite secant kernel at its two supplied arguments. -/
@[expose] def polynomialKernel (polynomial : CoefficientPolynomial) (x y : Canonical) : Canonical :=
  coefficientsKernel x y polynomial.coefficients

/-- Both original Gaussian Horner values factor through their actual shared finite secant traversal. -/
theorem eval_sub_factor (polynomial : CoefficientPolynomial) (x y : Canonical) :
    eval polynomial x - eval polynomial y = (x - y) * polynomialKernel polynomial x y :=
  Ascending.Gaussian.Secant.evalCoefficients_sub_factor
    (fun point table => evalCoeffs table point) (fun coefficient => coefficient)
    (fun _ => rfl) (fun _ _ _ => rfl) x y polynomial.coefficients

/-- The same Gaussian Horner jet reads its actual value and the diagonal of its shared secant traversal.

Both state components follow the same original coefficient tail. Scalar
readbacks relate its retained value and derivative to the shared traversal.
-/
private theorem kernel_jet (point : Canonical) : ∀ coefficients,
    coefficientsKernel point point coefficients = (Dense.Evaluation.jet coefficients point).2 ∧
      evalCoeffs coefficients point = (Dense.Evaluation.jet coefficients point).1
  | [] => ⟨rfl, rfl⟩
  | head :: tail => by
      have previous := kernel_jet point tail
      constructor
      · change evalCoeffs tail point + point * coefficientsKernel point point tail =
          (Dense.Evaluation.jet tail point).2 * point + (Dense.Evaluation.jet tail point).1
        rw [previous.1, previous.2]
        ring1
      · change head + point * evalCoeffs tail point = (Dense.Evaluation.jet tail point).1 * point + head
        rw [previous.2]
        ring1

/-- The original dense derivative evaluates to the diagonal of the same retained Gaussian polynomial's secant kernel. -/
theorem polynomialKernel_diagonal (polynomial : CoefficientPolynomial) (point : Canonical) :
    polynomialKernel polynomial point point =
      (Polynomial.Dense.Gaussian.GCD.derivative (Dense.Evaluation.toDense polynomial)).eval point := by
  rw [Dense.Evaluation.toDense_derivative_eval]
  exact (kernel_jet point polynomial.coefficients).1

end Purelib.Polynomial.Ascending.Gaussian.Evaluation

end
