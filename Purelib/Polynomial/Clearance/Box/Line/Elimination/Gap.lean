module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Elimination.Axis.Gap

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Components

open Purelib.Data.Rat

open Purelib.Geometry.Rational

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

namespace Purelib.Polynomial.Clearance.Box.Line.Elimination.Gap

/-- Construct full vertical-line clearance at the coordinate selected inside a strict gap.

The finite eliminant search retains nonvanishing at that coordinate; its coprimality certificate supplies clearance
relative to the given ambient box. -/
def verticalGapClearance
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    {a b : Fraction.Rational} (less : a < b) (ambient : Box) :
    Clearance.Box.Line.Basic.VerticalLineClearance p ambient
      (Elimination.Axis.Gap.verticalGapCoordinate elimination less) :=
  Clearance.Box.Line.Bezout.verticalOfCoprime p ambient _ (by
    simpa only [Dense.Gaussian.Path.Axis.verticalPathReal,
      Dense.Gaussian.Path.Axis.verticalPathImag] using
      elimination.vertical_coprime _
        (Elimination.Axis.Gap.verticalGapCoordinate_spec elimination less).1)

/-- Construct full horizontal-line clearance at the coordinate selected inside a strict gap.

The finite eliminant search retains nonvanishing at that coordinate; its coprimality certificate supplies clearance
relative to the given ambient box. -/
def horizontalGapClearance
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    {a b : Fraction.Rational} (less : a < b) (ambient : Box) :
    Clearance.Box.Line.Basic.HorizontalLineClearance p ambient
      (Elimination.Axis.Gap.horizontalGapCoordinate elimination less) :=
  Clearance.Box.Line.Bezout.horizontalOfCoprime p ambient _ (by
    simpa only [Dense.Gaussian.Path.Axis.horizontalPathReal,
      Dense.Gaussian.Path.Axis.horizontalPathImag] using
      elimination.horizontal_coprime _
        (Elimination.Axis.Gap.horizontalGapCoordinate_spec elimination less).1)
end Purelib.Polynomial.Clearance.Box.Line.Elimination.Gap

end
