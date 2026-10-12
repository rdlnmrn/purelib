module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
public import Purelib.Polynomial.Elimination.Axis.Certificate

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free degree-sharp maximality

The finite exact-isolation partition assigns every sufficiently refined
winding-one track to one displayed output cell.  Zero-winding remainder cells
cannot own such a track, and a raw-winding-four output cell cannot own two
separated tracks.  All searches below scan finite lists directly.
-/

namespace Purelib.Polynomial.Elimination.Axis.Gap

/-! ## One safe cut between two ordered states -/

/-- Find a vertical eliminant-safe coordinate between two ordered rational endpoints.

The scan uses the retained nonzero eliminant and its finite degree bound. -/
def verticalGapCoordinate
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Fraction.Rational} (less : a < b) : Fraction.Rational :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue elimination.vertical
    degreeBound less elimination.vertical_nonzero elimination.vertical_degree

/-- The selected vertical coordinate is strictly between the endpoints and avoids the eliminant. -/
theorem verticalGapCoordinate_spec
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Fraction.Rational} (less : a < b) :
    elimination.vertical.eval (verticalGapCoordinate elimination less) ≠ 0 ∧
      a < verticalGapCoordinate elimination less ∧
      verticalGapCoordinate elimination less < b :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec elimination.vertical
    degreeBound less elimination.vertical_nonzero elimination.vertical_degree

/-- Find a horizontal eliminant-safe coordinate between two ordered rational endpoints.

The scan uses the retained nonzero eliminant and its finite degree bound. -/
def horizontalGapCoordinate
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Fraction.Rational} (less : a < b) : Fraction.Rational :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue elimination.horizontal
    degreeBound less elimination.horizontal_nonzero
      elimination.horizontal_degree

/-- The selected horizontal coordinate is strictly between the endpoints and avoids the eliminant. -/
theorem horizontalGapCoordinate_spec
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Fraction.Rational} (less : a < b) :
    elimination.horizontal.eval (horizontalGapCoordinate elimination less) ≠
        0 ∧
      a < horizontalGapCoordinate elimination less ∧
      horizontalGapCoordinate elimination less < b :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec
    elimination.horizontal degreeBound less elimination.horizontal_nonzero
      elimination.horizontal_degree
end Purelib.Polynomial.Elimination.Axis.Gap

end
