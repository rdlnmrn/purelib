module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
public import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free eliminant-safe Newton bands

Four bounded eliminant searches choose axis-parallel sides at distances
between `r` and `2r` from an extracted Newton center.  The sides carry
full-line Bézout clearances, while finite Taylor estimates transfer affine
winding four to the original polynomial on the selected rectangle.
-/

namespace Purelib.Polynomial.Clearance.Box.Line.Elimination.Band

/-- Construct full vertical-line clearance at the selected left band coordinate.

The retained eliminant nonvanishing certificate supplies coprimality on the entire line, with the clearance evaluated
relative to the supplied ambient box. -/
def selectedBandLeftClearance
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (ambient : Box) (center : Gaussian.Basic.Canonical) {r : Fraction.Rational}
    (positive : 0 < r) : Clearance.Box.Line.Basic.VerticalLineClearance p ambient
      (Elimination.Axis.Band.selectedBand elimination center r positive).box.xLower := by
  apply Clearance.Box.Line.Bezout.verticalOfCoprime p ambient
  simpa only [Dense.Gaussian.Path.Axis.verticalPathReal, Dense.Gaussian.Path.Axis.verticalPathImag] using
    elimination.vertical_coprime _
      (Elimination.Axis.Band.selectedBand_left_nonzero elimination center positive)

/-- Construct full vertical-line clearance at the selected right band coordinate.

The retained eliminant nonvanishing certificate supplies coprimality on the entire line, with the clearance evaluated
relative to the supplied ambient box. -/
def selectedBandRightClearance
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (ambient : Box) (center : Gaussian.Basic.Canonical) {r : Fraction.Rational}
    (positive : 0 < r) : Clearance.Box.Line.Basic.VerticalLineClearance p ambient
      (Elimination.Axis.Band.selectedBand elimination center r positive).box.xUpper := by
  apply Clearance.Box.Line.Bezout.verticalOfCoprime p ambient
  simpa only [Dense.Gaussian.Path.Axis.verticalPathReal, Dense.Gaussian.Path.Axis.verticalPathImag] using
    elimination.vertical_coprime _
      (Elimination.Axis.Band.selectedBand_right_nonzero elimination center positive)

/-- Construct full horizontal-line clearance at the selected bottom band coordinate.

The retained eliminant nonvanishing certificate supplies coprimality on the entire line, with the clearance evaluated
relative to the supplied ambient box. -/
def selectedBandBottomClearance
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (ambient : Box) (center : Gaussian.Basic.Canonical) {r : Fraction.Rational}
    (positive : 0 < r) : Clearance.Box.Line.Basic.HorizontalLineClearance p ambient
      (Elimination.Axis.Band.selectedBand elimination center r positive).box.yLower := by
  apply Clearance.Box.Line.Bezout.horizontalOfCoprime p ambient
  simpa only [Dense.Gaussian.Path.Axis.horizontalPathReal, Dense.Gaussian.Path.Axis.horizontalPathImag] using
    elimination.horizontal_coprime _
      (Elimination.Axis.Band.selectedBand_bottom_nonzero elimination center positive)

/-- Construct full horizontal-line clearance at the selected top band coordinate.

The retained eliminant nonvanishing certificate supplies coprimality on the entire line, with the clearance evaluated
relative to the supplied ambient box. -/
def selectedBandTopClearance
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (ambient : Box) (center : Gaussian.Basic.Canonical) {r : Fraction.Rational}
    (positive : 0 < r) : Clearance.Box.Line.Basic.HorizontalLineClearance p ambient
      (Elimination.Axis.Band.selectedBand elimination center r positive).box.yUpper := by
  apply Clearance.Box.Line.Bezout.horizontalOfCoprime p ambient
  simpa only [Dense.Gaussian.Path.Axis.horizontalPathReal, Dense.Gaussian.Path.Axis.horizontalPathImag] using
    elimination.horizontal_coprime _
      (Elimination.Axis.Band.selectedBand_top_nonzero elimination center positive)
end Purelib.Polynomial.Clearance.Box.Line.Elimination.Band

end
