module
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.SafeCut
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field

open Purelib.Polynomial.Dense.Basic (RationalPolynomial)

open Purelib.Polynomial

section
@[expose] public section

/-!
# Common finite event partitions for curve roots and box edges

The root-event polynomial of a boundary chart and the four cleared box-edge
polynomials must be classified on the same parameter cells.  This module
forms one product of their complete reduced-chain guards, uses it for every
central-third cut, and chooses a coefficient-computed depth below all of the
individual event-resolution widths.

Consequently every emitted leaf has, simultaneously:

* a finite Cauchy--Sturm event record for the chart root polynomial; and
* a finite event record for every nontrivial box-edge condition.

Identically-zero box conditions are retained separately by
`CurveBoxConditions.condition_zero_or_active`; they never make
the common cut guard vanish.
-/

namespace Purelib.RootIsolation.Sturm.Event

/-- Complete reduced-chain guard for the Sturm count of one polynomial. -/
def polynomialEventGuard (polynomial :
  RationalPolynomial) : RationalPolynomial :=
  Dense.Rational.SignedRemainder.SafeCut.chainGuard (Dense.Derivative.derivative polynomial) polynomial

open Purelib.RootIsolation in
/-- A nonzero event polynomial has a nonzero complete reduced-chain guard. -/
theorem polynomialEventGuard_isZero_false
    {polynomial : RationalPolynomial} (nonzero : polynomial.isZero = false) :
    (polynomialEventGuard polynomial).isZero = false :=
  Dense.Rational.SignedRemainder.SafeCut.chainGuard_isZero_false nonzero
end Purelib.RootIsolation.Sturm.Event

end
