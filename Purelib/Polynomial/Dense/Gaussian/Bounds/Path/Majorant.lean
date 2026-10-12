module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Path.Majorant

/-- Finite Horner majorant appearing in one side of a boundary-dominance
clearance. -/
def boundarySideMajorant (p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (interval : Data.Rat.Interval.Bounds) : Fraction.Rational :=
  max 1
    (Dense.Rational.Bounds.Horner.evalSqBound (Dense.Gaussian.Path.Components.pathReal p origin direction) interval +
      Dense.Rational.Bounds.Horner.evalSqBound (Dense.Gaussian.Path.Components.pathImag p origin direction) interval)
end Purelib.Polynomial.Dense.Gaussian.Bounds.Path.Majorant

end
