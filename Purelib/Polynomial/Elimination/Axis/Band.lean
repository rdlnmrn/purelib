module
import Purelib.Data.Rat.Bounds.Radius
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
public import Purelib.Polynomial.Elimination.Axis.Certificate
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Eliminant-safe axis coordinates and retained rectangular bands

Four original bounded central-third scans select coordinates between one and
two positive radii from the retained centre. Their pointwise eliminant
certificates construct the same rectangle and its eight radial bounds.
-/

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data
open Purelib.Geometry.Rational
open Rat.Bounds
open Purelib.Polynomial.Dense.Rational.Nonzero

namespace Purelib.Polynomial.Elimination.Axis.Band

/-- Search for an eliminant-safe left coordinate around the center.

The bounded candidate scan stays between two radii and one radius to the left of the center and uses the retained
vertical eliminant degree bound. -/
@[expose] public def leftCoordinate {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound
  : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) (r : Fraction.Rational) (positive : 0 < r) : Fraction.Rational :=
  Search.Central.centralSearchValue elimination.vertical degreeBound
    (a := center.re - 2 * r) (b := center.re - r)
    (Radius.sub_twice_lt_sub (c := center.re) positive) elimination.vertical_nonzero
    elimination.vertical_degree

/-- Search for an eliminant-safe right coordinate around the center.

The bounded candidate scan stays between one radius and two radii to the right of the center and uses the retained
vertical eliminant degree bound. -/
@[expose] public def rightCoordinate {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {degreeBound : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) (r : Fraction.Rational) (positive : 0 < r) : Fraction.Rational :=
  Search.Central.centralSearchValue elimination.vertical degreeBound
    (a := center.re + r) (b := center.re + 2 * r)
    (Radius.add_lt_add_twice (c := center.re) positive) elimination.vertical_nonzero
    elimination.vertical_degree

/-- Search for an eliminant-safe bottom coordinate around the center.

The bounded candidate scan stays between two radii and one radius below of the center and uses the retained horizontal
eliminant degree bound. -/
@[expose] public def bottomCoordinate {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {degreeBound : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) (r : Fraction.Rational) (positive : 0 < r) : Fraction.Rational :=
  Search.Central.centralSearchValue elimination.horizontal degreeBound
    (a := center.im - 2 * r) (b := center.im - r)
    (Radius.sub_twice_lt_sub (c := center.im) positive)
    elimination.horizontal_nonzero
    elimination.horizontal_degree

/-- Search for an eliminant-safe top coordinate around the center.

The bounded candidate scan stays between one radius and two radii above of the center and uses the retained horizontal
eliminant degree bound. -/
@[expose] public def topCoordinate {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound
  : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) (r : Fraction.Rational) (positive : 0 < r) : Fraction.Rational :=
  Search.Central.centralSearchValue elimination.horizontal degreeBound
    (a := center.im + r) (b := center.im + 2 * r)
    (Radius.add_lt_add_twice (c := center.im) positive)
    elimination.horizontal_nonzero
    elimination.horizontal_degree

/-- The selected left coordinate avoids the vertical eliminant and lies in its open band.

The original bounded coordinate scan supplies both its nonzero
eliminant evaluation and its strict position between the displayed
radial endpoints about the same retained centre. -/
public theorem leftCoordinate_spec {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound
  : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    elimination.vertical.eval
        (leftCoordinate elimination center r positive) ≠ 0 ∧
      center.re - 2 * r < leftCoordinate elimination center r positive ∧
      leftCoordinate elimination center r positive < center.re - r := by
  exact Search.Central.centralSearchValue_spec elimination.vertical degreeBound
    (a := center.re - 2 * r) (b := center.re - r)
    (Radius.sub_twice_lt_sub (c := center.re) positive) elimination.vertical_nonzero
    elimination.vertical_degree

/-- The selected right coordinate avoids the vertical eliminant and lies in its open band.

The original bounded coordinate scan supplies both its nonzero
eliminant evaluation and its strict position between the displayed
radial endpoints about the same retained centre. -/
public theorem rightCoordinate_spec {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound
  : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    elimination.vertical.eval
        (rightCoordinate elimination center r positive) ≠ 0 ∧
      center.re + r < rightCoordinate elimination center r positive ∧
      rightCoordinate elimination center r positive < center.re + 2 * r := by
  exact Search.Central.centralSearchValue_spec elimination.vertical degreeBound
    (a := center.re + r) (b := center.re + 2 * r)
    (Radius.add_lt_add_twice (c := center.re) positive) elimination.vertical_nonzero
    elimination.vertical_degree

/-- The selected bottom coordinate avoids the horizontal eliminant and lies in its open band.

The original bounded coordinate scan supplies both its nonzero
eliminant evaluation and its strict position between the displayed
radial endpoints about the same retained centre. -/
public theorem bottomCoordinate_spec {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {degreeBound : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    elimination.horizontal.eval
        (bottomCoordinate elimination center r positive) ≠ 0 ∧
      center.im - 2 * r < bottomCoordinate elimination center r positive ∧
      bottomCoordinate elimination center r positive < center.im - r := by
  exact Search.Central.centralSearchValue_spec elimination.horizontal degreeBound
    (a := center.im - 2 * r) (b := center.im - r)
    (Radius.sub_twice_lt_sub (c := center.im) positive)
    elimination.horizontal_nonzero
    elimination.horizontal_degree

/-- The selected top coordinate avoids the horizontal eliminant and lies in its open band.

The original bounded coordinate scan supplies both its nonzero
eliminant evaluation and its strict position between the displayed
radial endpoints about the same retained centre. -/
public theorem topCoordinate_spec {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound :
  Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    elimination.horizontal.eval
        (topCoordinate elimination center r positive) ≠ 0 ∧
      center.im + r < topCoordinate elimination center r positive ∧
      topCoordinate elimination center r positive < center.im + 2 * r := by
  exact Search.Central.centralSearchValue_spec elimination.horizontal degreeBound
    (a := center.im + r) (b := center.im + 2 * r)
    (Radius.add_lt_add_twice (c := center.im) positive)
    elimination.horizontal_nonzero
    elimination.horizontal_degree

/-- Execute all four bounded safe-coordinate searches.

The original four coordinate searches supply the same retained endpoint
values and eliminant-avoidance certificates. Their scalar comparisons
construct the original box and all eight radial side bounds. -/
@[expose] public def selectedBand {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound :
  Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) (r : Fraction.Rational) (positive : 0 < r) :
    Box.Band.Basic.BandBox center r := by
  have left := leftCoordinate_spec elimination center positive
  have right := rightCoordinate_spec elimination center positive
  have bottom := bottomCoordinate_spec elimination center positive
  have top := topCoordinate_spec elimination center positive
  exact
    { box :=
        { xLower := leftCoordinate elimination center r positive
          xUpper := rightCoordinate elimination center r positive
          yLower := bottomCoordinate elimination center r positive
          yUpper := topCoordinate elimination center r positive
          x_valid := (left.2.2.trans
            ((Radius.sub_lt_center positive).trans
              ((Radius.center_lt_add positive).trans right.2.1))).le
          y_valid := (bottom.2.2.trans
            ((Radius.sub_lt_center positive).trans
              ((Radius.center_lt_add positive).trans top.2.1))).le }
      left_lower := left.2.1.le
      left_upper := left.2.2.le
      right_lower := right.2.1.le
      right_upper := right.2.2.le
      bottom_lower := bottom.2.1.le
      bottom_upper := bottom.2.2.le
      top_lower := top.2.1.le
      top_upper := top.2.2.le }

/-- The vertical eliminant is nonzero on the selected band's left coordinate.

The selected rectangle retains the corresponding original coordinate
scan as its endpoint. The scan's pointwise certificate supplies nonzero
evaluation of the same displayed eliminant there. -/
public theorem selectedBand_left_nonzero
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    elimination.vertical.eval
      (selectedBand elimination center r positive).box.xLower ≠ 0 := by
  simpa only [selectedBand] using
    (leftCoordinate_spec elimination center positive).1

/-- The vertical eliminant is nonzero on the selected band's right coordinate.

The selected rectangle retains the corresponding original coordinate
scan as its endpoint. The scan's pointwise certificate supplies nonzero
evaluation of the same displayed eliminant there. -/
public theorem selectedBand_right_nonzero
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    elimination.vertical.eval
      (selectedBand elimination center r positive).box.xUpper ≠ 0 := by
  simpa only [selectedBand] using
    (rightCoordinate_spec elimination center positive).1

/-- The horizontal eliminant is nonzero on the selected band's bottom coordinate.

The selected rectangle retains the corresponding original coordinate
scan as its endpoint. The scan's pointwise certificate supplies nonzero
evaluation of the same displayed eliminant there. -/
public theorem selectedBand_bottom_nonzero
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    elimination.horizontal.eval
      (selectedBand elimination center r positive).box.yLower ≠ 0 := by
  simpa only [selectedBand] using
    (bottomCoordinate_spec elimination center positive).1

/-- The horizontal eliminant is nonzero on the selected band's top coordinate.

The selected rectangle retains the corresponding original coordinate
scan as its endpoint. The scan's pointwise certificate supplies nonzero
evaluation of the same displayed eliminant there. -/
public theorem selectedBand_top_nonzero
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
    (elimination : Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (center : Gaussian.Basic.Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    elimination.horizontal.eval
      (selectedBand elimination center r positive).box.yUpper ≠ 0 := by
  simpa only [selectedBand] using
    (topCoordinate_spec elimination center positive).1

end Purelib.Polynomial.Elimination.Axis.Band
