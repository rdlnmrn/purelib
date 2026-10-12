module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Edge.Product.Check
public import Purelib.Polynomial.Winding.Polygon.Product
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

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

namespace Purelib.Polynomial.Winding.Polygon.Product.Check

/-- The fully executable per-edge product checks can be folded into a closed
walk certificate without introducing a new trust boundary. -/
theorem checkedChainProductFormula (p q :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (start : Gaussian.Basic.Canonical) → (vertices : List Gaussian.Basic.Canonical) →
      (∀ current next,
        Winding.Edge.Product.Check.lineProductFormulaCheck
          p q current (next - current) 0 1 = true) →
      Winding.Polygon.Product.ChainProductFormula p q start vertices
  | start, [], _ => .nil start
  | start, finish :: remaining, checked =>
      .cons
        (Winding.Edge.Product.Check.lineProductFormula_of_check
          p q start (finish - start) 0 1 (checked start finish))
        (checkedChainProductFormula p q finish remaining checked)
end Purelib.Polynomial.Winding.Polygon.Product.Check

end
