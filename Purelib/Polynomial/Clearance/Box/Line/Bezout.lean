module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Intervals
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Path
public import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Data.Gaussian.Cast

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Polynomial.Clearance.Box.Line.Bezout

/-- A displayed finite Bézout certificate produces vertical-line clearance. -/
def verticalOfCoprime
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) (x : Fraction.Rational)
    (coprime : Dense.Rational.Bezout.Basic.CoprimeCertificate
      (Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      (Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)) :
    Clearance.Box.Line.Basic.VerticalLineClearance p ambient x :=
  Clearance.Box.Line.Path.verticalOfPathCertificate p ambient x
    (Clearance.Pair.Bezout.certificateOfCoprime coprime (Box.Intervals.verticalInterval ambient))

/-- A displayed finite Bézout certificate produces horizontal-line clearance. -/
def horizontalOfCoprime
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) (y : Fraction.Rational)
    (coprime : Dense.Rational.Bezout.Basic.CoprimeCertificate
      (Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)
      (Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)) :
    Clearance.Box.Line.Basic.HorizontalLineClearance p ambient y :=
  Clearance.Box.Line.Path.horizontalOfPathCertificate p ambient y
    (Clearance.Pair.Bezout.certificateOfCoprime coprime (Box.Intervals.horizontalInterval ambient))
end Purelib.Polynomial.Clearance.Box.Line.Bezout

end
