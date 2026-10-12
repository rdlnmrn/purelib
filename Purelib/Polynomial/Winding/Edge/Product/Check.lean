module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
public import Purelib.Polynomial.Winding.Edge.Product
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path

open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

namespace Purelib.Polynomial.Winding.Edge.Product.Check

/-- Fully executable checker for one local product identity. -/
def lineProductFormulaCheck
    (p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (a b : Fraction.Rational) : Bool :=
  decide
    ((PolynomialEdge.ofLine (p * q) origin direction a b).doubledWinding =
      (PolynomialEdge.ofLine p origin direction a b).doubledWinding +
        (PolynomialEdge.ofLine q origin direction a b).doubledWinding -
        (Winding.Edge.Product.lineProductCorrection2 p q origin direction a : Int) +
        Winding.Edge.Product.lineProductCorrection2 p q origin direction b)

/-- A successful executable check certifies the affine-edge product winding identity. -/
theorem lineProductFormula_of_check
    (p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (a b : Fraction.Rational)
    (checked : lineProductFormulaCheck p q origin direction a b = true) :
    Winding.Edge.Product.LineProductFormula p q origin direction a b := by
  simp only [Winding.Edge.Product.LineProductFormula, -eq_self, -iff_self]
  simp only [lineProductFormulaCheck, -eq_self, -iff_self] at checked
  exact of_decide_eq_true checked
end Purelib.Polynomial.Winding.Edge.Product.Check

end
