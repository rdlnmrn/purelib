module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Sign.CauchyIndex.Phase
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic

open Purelib

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

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Event

/-- One resolved event already carries the complete local modulo-four phase
formula. -/
def phaseFormulaOfEvent
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (event : Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns R S interval) :
    Dense.Rational.CauchyIndex.Phase.Basic.PhaseFormula R S interval.lower interval.upper where
  turns := Data.Sign.CauchyIndex.Phase.signQuarterTurns event.numerator event.denominator
    (Data.Sign.ofCoordinate (R.eval interval.lower))
    (Data.Sign.ofCoordinate (S.eval interval.lower))
    (Data.Sign.ofCoordinate (R.eval interval.upper))
    (Data.Sign.ofCoordinate (S.eval interval.upper))
  index_eq := by
    rw [event.index]
    exact Data.Sign.CauchyIndex.Phase.sign_eventIndex2_eq_phase_change_add_four_mul
      event.numerator event.denominator
      (Data.Sign.ofCoordinate (R.eval interval.lower))
      (Data.Sign.ofCoordinate (S.eval interval.lower))
      (Data.Sign.ofCoordinate (R.eval interval.upper))
      (Data.Sign.ofCoordinate (S.eval interval.upper))
      event.nonzero event.numeratorLowerStable event.denominatorLowerStable
      event.numeratorUpperStable event.denominatorUpperStable
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Event

end
