module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.Product
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

namespace Purelib.Polynomial.Dense.Rational.Pair.ConjugateProduct

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational.Pair

/-- Real coordinate of `conj(A+iB) * (U+iV)`.

Dense multiplication and subtraction form the real coordinate using the
original four polynomials, with negation of the second left coordinate. Its
evaluation is the sum of the two corresponding scalar coordinate products. -/
@[expose] public def roucheReal (A B U V : Dense.Rational.Basic.CoordinatePolynomial) : (Dense.Basic.DensePolynomial
  Fraction.Rational) :=
  Product.productReal A (-B) U V

/-- Imaginary coordinate of `conj(A+iB) * (U+iV)`.

The original dense product forms the imaginary coordinate after negating
the second left coordinate. Its evaluation is the alternating sum of the
two scalar cross products for the same four polynomial inputs. -/
@[expose] public def roucheImag (A B U V : Dense.Rational.Basic.CoordinatePolynomial) : (Dense.Basic.DensePolynomial
  Fraction.Rational) :=
  Product.productImag A (-B) U V

/-- The real conjugate-product coordinate evaluates to the sum of the two coordinate products.

The retained dense product and negation evaluation laws identify its value
at the supplied rational parameter. Scalar ring arithmetic converts the
subtracted negative product into the sum of the two displayed products. -/
@[simp] public theorem eval_roucheReal (A B U V : Dense.Rational.Basic.CoordinatePolynomial) (x : Fraction.Rational) :
    (roucheReal A B U V).eval x =
      A.eval x * U.eval x + B.eval x * V.eval x := by
  unfold roucheReal
  rw [Product.eval_productReal,
    Dense.Basic.DensePolynomial.eval_neg]
  ring1

/-- The imaginary conjugate-product coordinate evaluates to the alternating coordinate product.

The same dense product and negation evaluation laws identify its value at
the supplied rational parameter. The alternating scalar expression retains
the original order of the four coordinate inputs. -/
@[simp] public theorem eval_roucheImag (A B U V : Dense.Rational.Basic.CoordinatePolynomial) (x : Fraction.Rational) :
    (roucheImag A B U V).eval x =
      A.eval x * V.eval x - B.eval x * U.eval x := by
  simp [roucheImag, Product.productImag]
  ring1

end Purelib.Polynomial.Dense.Rational.Pair.ConjugateProduct
