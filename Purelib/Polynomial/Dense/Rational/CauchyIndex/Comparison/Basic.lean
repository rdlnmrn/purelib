module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.ConjugateProduct
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic

open Purelib.Data.Rat

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

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Basic

/-- The two finite formulas attached to one oriented Rouché edge. -/
structure LineData
    (A B U V : Dense.Rational.Basic.CoordinatePolynomial) (a b : Fraction.Rational) : Prop where
  /-- The endpoint-jump identity for the real and imaginary coordinates of the conjugate product. -/ halfPlane :
    Dense.Rational.CauchyIndex.HalfPlane.Formula
    (Dense.Rational.Pair.ConjugateProduct.roucheReal A B U V) (Dense.Rational.Pair.ConjugateProduct.roucheImag A B U V)
      a b
  /-- The auxiliary product formula relating the conjugated first pair, second pair and their displayed product
    coordinates. -/ product : Dense.Rational.CauchyIndex.Product.Basic.AuxiliaryProductFormula A (-B) U V
    (Dense.Rational.Pair.ConjugateProduct.roucheReal A B U V) (Dense.Rational.Pair.ConjugateProduct.roucheImag A B U V)
      a b

/-- Reverse both finite formulas while preserving their exact polynomial coordinate pairs. -/
theorem LineData.reverse
    {A B U V : Dense.Rational.Basic.CoordinatePolynomial} {a b : Fraction.Rational}
    (data : LineData A B U V a b) :
      LineData A B U V b a where
  halfPlane := data.halfPlane.reverse
  product := data.product.reverse
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Basic

end
