module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Sign.CauchyIndex.Endpoint
import Purelib.Data.Rat.Sign.CauchyIndex.Product
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint

/-- All finite facts needed on one resolved one-sided event cell. -/
structure LocalEndpointData
    (A B C D E H : Dense.Rational.Basic.CoordinatePolynomial) (a b : Fraction.Rational) : Prop where
  /-- The first factor index equals its one-sided endpoint contribution. -/ leftIndex :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 A B a b =
    Data.Rat.Sign.CauchyIndex.Endpoint.leftEndpointIndex2 (A.eval a) (B.eval a) (A.eval b) (B.eval b)
  /-- The second factor index equals its one-sided endpoint contribution. -/ rightIndex :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 C D a b =
    Data.Rat.Sign.CauchyIndex.Endpoint.leftEndpointIndex2 (C.eval a) (D.eval a) (C.eval b) (D.eval b)
  /-- The product index equals its one-sided endpoint contribution. -/ productIndex :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 E H a b =
    Data.Rat.Sign.CauchyIndex.Endpoint.leftEndpointIndex2 (E.eval a) (H.eval a) (E.eval b) (H.eval b)
  /-- At least one coordinate of the first factor is nonzero at the start. -/ factorLeftStart : A.eval a ≠ 0 ∨ B.eval a
    ≠ 0
  /-- At least one coordinate of the second factor is nonzero at the start. -/ factorRightStart : C.eval a ≠ 0 ∨ D.eval
    a ≠ 0
  /-- The first factor imaginary coordinate is nonzero at the stop. -/ leftImagStop : B.eval b ≠ 0
  /-- The second factor imaginary coordinate is nonzero at the stop. -/ rightImagStop : D.eval b ≠ 0
  /-- The product imaginary coordinate is nonzero at the stop. -/ productImagStop : H.eval b ≠ 0
  /-- The first factor real coordinate starts at zero or retains a strict sign across the endpoints. -/ leftRealStable :
    A.eval a = 0 ∨ 0 < A.eval a * A.eval b
  /-- The first factor imaginary coordinate starts at zero or retains a strict sign across the endpoints. -/
    leftImagStable : B.eval a = 0 ∨ 0 < B.eval a * B.eval b
  /-- The second factor real coordinate starts at zero or retains a strict sign across the endpoints. -/ rightRealStable
    : C.eval a = 0 ∨ 0 < C.eval a * C.eval b
  /-- The second factor imaginary coordinate starts at zero or retains a strict sign across the endpoints. -/
    rightImagStable : D.eval a = 0 ∨ 0 < D.eval a * D.eval b
  /-- The product real coordinate starts at zero or retains a strict sign across the endpoints. -/ productRealStable :
    E.eval a = 0 ∨ 0 < E.eval a * E.eval b
  /-- The product imaginary coordinate starts at zero or retains a strict sign across the endpoints. -/
    productImagStable : H.eval a = 0 ∨ 0 < H.eval a * H.eval b
  /-- The product real coordinate obeys complex multiplication at the start. -/ productRealStart : E.eval a =
    A.eval a * C.eval a - B.eval a * D.eval a
  /-- The product imaginary coordinate obeys complex multiplication at the start. -/ productImagStart : H.eval a =
    A.eval a * D.eval a + B.eval a * C.eval a
  /-- The product real coordinate obeys complex multiplication at the stop. -/ productRealStop : E.eval b =
    A.eval b * C.eval b - B.eval b * D.eval b
  /-- The product imaginary coordinate obeys complex multiplication at the stop. -/ productImagStopEq : H.eval b =
    A.eval b * D.eval b + B.eval b * C.eval b

/-- The finite local endpoint data implies the complete doubled product
identity on that cell. -/
theorem
  auxiliaryProductFormula_of_localEndpointData
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {a b : Fraction.Rational}
    (data : LocalEndpointData A B C D E H a b) :
    Dense.Rational.CauchyIndex.Product.Basic.AuxiliaryProductFormula A B C D E H a b := by
  unfold Dense.Rational.CauchyIndex.Product.Basic.AuxiliaryProductFormula
    Dense.Rational.CauchyIndex.Product.Basic.auxiliaryEndpointCorrection2
  rw [data.leftIndex, data.rightIndex, data.productIndex,
    data.productRealStart, data.productImagStart,
    data.productRealStop, data.productImagStopEq]
  exact Data.Rat.Sign.CauchyIndex.Product.coordinateLocalProductTable
    (A.eval a) (B.eval a) (C.eval a) (D.eval a)
    (A.eval b) (B.eval b) (C.eval b) (D.eval b)
    data.factorLeftStart data.factorRightStart
    data.leftImagStop data.rightImagStop
    (by simpa only [← data.productImagStopEq] using data.productImagStop)
    data.leftRealStable data.leftImagStable
    data.rightRealStable data.rightImagStable
    (by
        simpa only [← data.productRealStart, ← data.productRealStop]
          using data.productRealStable)
    (by
        simpa only [← data.productImagStart, ← data.productImagStopEq]
          using data.productImagStable)

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint

end
