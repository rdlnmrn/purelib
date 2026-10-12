module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Square
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.LeadingDominance
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.LeadingDominance.Box

/-- The leading monomial strictly dominates the lower terms in quadrance along the computed large square's bottom edge.
-/
theorem largeSquare_bottom_dominance
    {p : CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {t : Fraction.Rational}
    (lower : -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ t)
    (upper : t ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval
        (Gaussian.Components.Basic.point t (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p))) <
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval
        (Gaussian.Components.Basic.point t (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p))) := open
          Purelib in by
  have bounds := Gaussian.Norm.Bounds.horizontal_symmetric_norm_bounds
    (Data.Rat.Bounds.Square.symmetric_coordinate_sq_bound lower upper)
    (show (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) ^ 2 =
        Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 by ring1)
  exact Dense.Gaussian.Bounds.LeadingDominance.largeSquare_radial_dominance degreePositive bounds.1 bounds.2

/-- The leading monomial strictly dominates the lower terms in quadrance along the computed large square's top edge. -/
theorem largeSquare_top_dominance
    {p : CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {t : Fraction.Rational}
    (lower : -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ t)
    (upper : t ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval
        (Gaussian.Components.Basic.point t (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p))) <
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval
        (Gaussian.Components.Basic.point t (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p))) := open Purelib
          in by
  have bounds := Gaussian.Norm.Bounds.horizontal_symmetric_norm_bounds
    (Data.Rat.Bounds.Square.symmetric_coordinate_sq_bound lower upper) rfl
  exact Dense.Gaussian.Bounds.LeadingDominance.largeSquare_radial_dominance degreePositive bounds.1 bounds.2

/-- The leading monomial strictly dominates the lower terms in quadrance along the computed large square's right edge.
-/
theorem largeSquare_right_dominance
    {p : CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {t : Fraction.Rational}
    (lower : -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ t)
    (upper : t ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval
        (Gaussian.Components.Basic.point (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) t)) <
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval
        (Gaussian.Components.Basic.point (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) t)) := open Purelib
          in by
  have bounds := Gaussian.Norm.Bounds.vertical_symmetric_norm_bounds
    (Data.Rat.Bounds.Square.symmetric_coordinate_sq_bound lower upper) rfl
  exact Dense.Gaussian.Bounds.LeadingDominance.largeSquare_radial_dominance degreePositive bounds.1 bounds.2

/-- The leading monomial strictly dominates the lower terms in quadrance along the computed large square's left edge. -/
theorem largeSquare_left_dominance
    {p : CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {t : Fraction.Rational}
    (lower : -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ t)
    (upper : t ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval
        (Gaussian.Components.Basic.point (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) t)) <
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval
        (Gaussian.Components.Basic.point (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) t)) := open
          Purelib in by
  have bounds := Gaussian.Norm.Bounds.vertical_symmetric_norm_bounds
    (Data.Rat.Bounds.Square.symmetric_coordinate_sq_bound lower upper)
    (show (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) ^ 2 =
        Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 by ring1)
  exact Dense.Gaussian.Bounds.LeadingDominance.largeSquare_radial_dominance degreePositive bounds.1 bounds.2
end Purelib.Polynomial.Dense.Gaussian.Bounds.LeadingDominance.Box

end
