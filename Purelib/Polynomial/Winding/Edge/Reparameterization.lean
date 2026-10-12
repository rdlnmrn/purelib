module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Gaussian.Path.Reparameterization
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Affine
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Affine segments retain their finite winding under subdivision

The normalized coordinate coefficient lists identify an affine subsegment
with the corresponding affine substitution of the original line.  Cauchy
index reparameterization then relates its unit interval to the original
parameter interval, including reversed and stationary clear subsegments.
-/

namespace Purelib.Polynomial.Winding.Edge.Reparameterization

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

public section

/-- Affine reparameterization preserves an edge's doubled winding.

A nonzero rational slope transforms both endpoints and the retained Gaussian direction, including orientation reversal
for negative slopes. -/
theorem ofLine_doubledWinding_affine (polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (origin
  direction : Gaussian.Basic.Canonical)
    (offset slope left right : Fraction.Rational) (nonzero : slope ≠ 0) :
    (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine polynomial (Affine.line origin direction offset)
      (Gaussian.Cast.Path.ofCoordinate slope * direction) left right).doubledWinding =
      (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine polynomial origin direction (offset + slope * left) (offset
        + slope * right)).doubledWinding := by
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
    (Dense.Gaussian.Path.Components.pathReal polynomial (Affine.line origin direction offset)
      (Gaussian.Cast.Path.ofCoordinate slope * direction))
    (Dense.Gaussian.Path.Components.pathImag polynomial (Affine.line origin direction offset)
      (Gaussian.Cast.Path.ofCoordinate slope * direction)) left right = _
  rw [← Dense.Rational.CauchyIndex.Basic.cauchyIndex2_normalize,
    Purelib.Polynomial.Dense.Gaussian.Path.Reparameterization.pathReal_affine,
    Purelib.Polynomial.Dense.Gaussian.Path.Reparameterization.pathImag_affine]
  exact Dense.Rational.CauchyIndex.Affine.cauchyIndex2_affine _ _ offset slope left right nonzero
end

end Purelib.Polynomial.Winding.Edge.Reparameterization
