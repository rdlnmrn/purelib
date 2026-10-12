module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Segment

/-! ## Finite polygonal walks -/

/-- The affine segment from `start` to `finish`, with displayed parameter
interval `[0,1]`. -/
def segment (p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (start finish :
    Gaussian.Basic.Canonical) :
    Dense.Rational.Pair.Path.Basic.PolynomialEdge :=
  Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine p start (finish - start) 0 1
end Purelib.Polynomial.Dense.Gaussian.Path.Segment

end
