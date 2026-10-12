module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative
import Purelib.Polynomial.Dense.Gaussian.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Multiplication
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.GaussianCanonical (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Displayed Newton residuals over canonical finite arithmetic

This is the representative RFAP calculation for the quotient-free pilot.  It
computes a polynomial value and its finite automatic derivative at a supplied
Gaussian-rational sample, forms the displayed Newton correction, and proves
its squared displacement by canonical Gaussian arithmetic alone.
-/

namespace Purelib.Polynomial.Evaluation.Gaussian.NewtonResidual

/-- Squared residual at one explicitly supplied Gaussian-rational sample. -/
def residualSq (polynomial :
  CoefficientPolynomial) (sample : Gaussian.Basic.Canonical) :
    Fraction.Rational :=
  Canonical.normSq (Dense.Gaussian.Evaluation.eval polynomial sample)

/-- Value of the finite automatic derivative at the supplied sample. -/
def derivativeValue (polynomial :
  CoefficientPolynomial) (sample : Gaussian.Basic.Canonical) :
    Gaussian.Basic.Canonical :=
  Dense.Gaussian.Evaluation.eval
    (Dense.Gaussian.Derivative.derivative polynomial) sample

/-- Executable Newton update based only at the supplied finite sample. -/
def newtonCenter (polynomial :
  CoefficientPolynomial) (sample : Gaussian.Basic.Canonical) :
    Gaussian.Basic.Canonical :=
  sample - Dense.Gaussian.Evaluation.eval polynomial sample /
    derivativeValue polynomial sample

/-- Residual quadrance is multiplicative for the finite dense product. -/
theorem residualSq_mul (left right :
  CoefficientPolynomial) (sample : Gaussian.Basic.Canonical) :
    residualSq (Dense.Gaussian.Multiplication.mul left right) sample =
      residualSq left sample * residualSq right
        sample := by
  unfold residualSq
  rw [Dense.Gaussian.Multiplication.eval_mul, Canonical.normSq_mul]

/-- The exact Newton displacement is the negative source-value to derivative-value quotient. -/
theorem newtonCenter_sub_sample
    (polynomial : CoefficientPolynomial) (sample :
      Gaussian.Basic.Canonical) :
    newtonCenter polynomial sample - sample =
      -(Dense.Gaussian.Evaluation.eval polynomial sample /
        derivativeValue polynomial sample) := by
  unfold newtonCenter
  exact Canonical.sub_sub_right sample
    (Dense.Gaussian.Evaluation.eval polynomial sample /
      derivativeValue polynomial sample)

/-- The exact displayed Newton-displacement identity used by residual
localization.  It is an equality of finite canonical records. -/
theorem newtonDisplacementSq
    (polynomial : CoefficientPolynomial) (sample :
      Gaussian.Basic.Canonical)
    (derivativeNonzero : derivativeValue polynomial sample ≠ 0) :
    Canonical.normSq (newtonCenter polynomial sample - sample) =
      residualSq polynomial sample *
        (Canonical.normSq (derivativeValue polynomial sample))⁻¹ := by
  rw [newtonCenter_sub_sample, Canonical.normSq_neg,
    Canonical.normSq_div _ _ derivativeNonzero]
  rfl

end Purelib.Polynomial.Evaluation.Gaussian.NewtonResidual

end
