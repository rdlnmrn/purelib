module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free local residual extraction

A fixed rational corner of a shrinking box supplies the local sample.  Finite
Horner bounds and the box diagonal bound its residual variation.  If that
sample value were larger than the variation, a finite Rouché contraction to
the nonzero constant path would force raw winding zero.  Thus every proper
nonzero-winding box has an explicitly small rational residual.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree

/-- A fixed positive residual threshold computed from the left Bézout
coefficient on the ambient box. -/
def derivativeThreshold {p :
  CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient :
      Box) : Fraction.Rational :=
  (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient).threshold

/-- A uniform positive derivative lower bound computed from the right
Bézout coefficient.  It is used only after the residual has crossed
`derivativeThreshold`. -/
def derivativeMargin {p :
  CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient :
      Box) : Fraction.Rational :=
  (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient).margin

/-- The squarefree residual threshold is positive. -/
theorem derivativeThreshold_pos {p :
  CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient :
      Box) :
    0 < derivativeThreshold squarefree ambient :=
  (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient).threshold_pos

/-- The derivative margin extracted from the squarefree Bézout certificate is positive. -/
theorem derivativeMargin_pos {p :
  CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient :
      Box) :
    0 < derivativeMargin squarefree ambient :=
  (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient).margin_pos

/-- The finite Bézout identity supplies a uniform positive lower bound for
the derivative once the residual is below the left-coefficient threshold. -/
theorem derivativeMargin_le_of_small_residual
    {p : CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient :
      Box)
    {z : Gaussian.Basic.Canonical} (inside : ambient.Contains z)
    (small : Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤
      derivativeThreshold squarefree ambient) :
    derivativeMargin squarefree ambient ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval z) :=
  (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient).lower inside small

/-- The finite Bézout identity forces the derivative to be nonzero whenever
the displayed residual is below the fixed threshold. -/
theorem derivative_ne_zero_of_small_residual
    {p : CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient :
      Box)
    {z : Gaussian.Basic.Canonical} (inside : ambient.Contains z)
    (small : Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤
      derivativeThreshold squarefree ambient) :
    (Dense.Gaussian.GCD.derivative p).eval z ≠ 0 := by
  have margin := derivativeMargin_le_of_small_residual
    squarefree ambient inside small
  have marginPositive := derivativeMargin_pos squarefree ambient
  intro derivativeZero
  rw [derivativeZero, Gaussian.Norm.Basic.normSq_zero] at margin
  exact (not_lt_of_ge margin) marginPositive
end Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree

end
