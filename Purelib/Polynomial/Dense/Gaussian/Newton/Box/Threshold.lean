module
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free refinement to a certified Newton point

The raw nonzero-winding subdivision is iterated to a coefficient-computed
positive diagonal threshold.  Its explicit contraction bound then supplies
the small residual required by the finite Bézout derivative argument.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Threshold

/-- Positive squared-diagonal target that makes the raw anchor residual small
enough for the finite Bézout derivative separation. -/
def newtonDiagonalThreshold
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) : Fraction.Rational :=
  Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient /
    Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient

/-- The computed Newton squared-diagonal threshold is strictly positive. -/
theorem newtonDiagonalThreshold_pos
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) :
    0 < newtonDiagonalThreshold p ambient squarefree :=
  Fraction.Order.Field.div_pos_direct
    (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold_pos squarefree ambient)
    (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Threshold

end
