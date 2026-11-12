module

public import Purelib.Curves.Legendre.Degeneration.Conic
public import Purelib.Curves.Legendre.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Fin.Two
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Original cubic derivatives at the retained conic coordinates

The original cubic derivative factors through its labelled collision pair
and remaining affine factor. The same original conic point identifies its
pair with the exact normalized-ordinate square, giving both the original
curve value and its independently computed spatial derivative.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Point

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Quadratic
open Purelib.Polynomial.Dense.Gaussian

variable {site : Fin 2} {parameter : Canonical}

/-- The independent original cubic derivative reads the actual labelled pair and remaining affine factor. -/
private theorem polynomial_derivative_pair (site : Fin 2) (parameter point : Canonical) :
    (GCD.derivative (Paths.polynomial parameter)).eval point =
      ((point - criticalValue site) + (point - parameter)) * (unitPolynomial site).eval point +
        (point - criticalValue site) * (point - parameter) := by
  rewrite [Squarefree.derivative_eval, unitPolynomial, Linear.Translated.translatedCoordinate_eval]
  rcases Data.Fin.Two.finTwo_cases site with zero | one
  · subst site
    change 3 * point * point - 2 * (parameter + 1) * point + parameter =
      ((point - 0) + (point - parameter)) * (point - 1) + (point - 0) * (point - parameter)
    ring1
  · subst site
    change 3 * point * point - 2 * (parameter + 1) * point + parameter =
      ((point - 1) + (point - parameter)) * (point - 0) + (point - 1) * (point - parameter)
    ring1

/-- The retained original conic point's exact ordinate square factors the complete original cubic value. -/
theorem polynomial_eq (point : Point site parameter) :
    (Paths.polynomial parameter).eval point.base =
      (unitPolynomial site).eval point.base * (point.ordinate * point.ordinate) := by
  rewrite [polynomial_centered, point.coordinate_base, ← point.quadratic, pow_two]
  ring1

/-- The original cubic derivative at the retained conic point is its exact ordinate square plus the affine product term.

The original automatic cubic derivative and the same labelled midpoint,
remaining factor and conic abscissa remain unchanged. This pointwise identity
does not assume any primitive or integral relation.
-/
theorem polynomialDerivative_eq (point : Point site parameter) :
    (GCD.derivative (Paths.polynomial parameter)).eval point.base =
      point.ordinate * point.ordinate + 2 * (unitPolynomial site).eval point.base * point.abscissa := by
  have centerTwo : center site parameter * 2 = criticalValue site + parameter :=
    Algebra.Field.ExplicitField.div_mul_cancel _ (by decide +kernel)
  have pairSum : (point.base - criticalValue site) + (point.base - parameter) = 2 * point.abscissa := by
    change ((center site parameter + point.abscissa) - criticalValue site) +
      ((center site parameter + point.abscissa) - parameter) = _
    calc
      _ = 2 * point.abscissa + (center site parameter * 2 - (criticalValue site + parameter)) := by ring1
      _ = _ := by rewrite [centerTwo]; ring1
  have pair : (point.base - criticalValue site) * (point.base - parameter) =
      point.ordinate * point.ordinate := by
    rewrite [Split.product_eq _ _ _ (by decide +kernel)]
    change coordinate site parameter point.base ^ 2 - smoothing site parameter = _
    rewrite [point.coordinate_base, ← point.quadratic, pow_two]
    rfl
  rewrite [polynomial_derivative_pair, pairSum, pair]
  ring1

end Purelib.Curves.Legendre.Degeneration.Conic.Point

end
