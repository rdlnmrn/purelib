module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.Boundary
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path

import Purelib.Tactic.QuotientFreeOmega
-- The exposed integer sum retains the original arithmetic data through this owner.
public import Purelib.Algebra.Ring.Int
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
import Purelib.Tactic.Ring

/-!
# Integer winding sums of displayed box boundaries

The positively oriented four-edge boundary determines an integer sum of the
same doubled edge indices. Division by two and four gives the retained winding
normalizations; normalization of the polynomial preserves the edge records.
-/

namespace Purelib.Polynomial.Winding.Box.Basic

open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- Sum the four doubled winding indices of the displayed box boundary.

The original oriented edge order and list sum are retained. Both the polynomial
and the box determine the same four edge records used by the integer fold. -/
@[expose] public def quadrupledBoxWinding (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box :
  Box) : Int :=
  ((Dense.Gaussian.Path.Box.Boundary.boxBoundary p box).map
    Dense.Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding).sum

/-- Closed-box winding ignores the finite prefix of representation zeros removed by dense normalization.

Normalization preserves each of the four displayed edge coefficient records.
Their retained doubled indices therefore give the same integer boundary sum. -/
@[simp] public theorem quadrupledBoxWinding_normalize
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box) :
    quadrupledBoxWinding p.normalize box = quadrupledBoxWinding p box := by
  unfold quadrupledBoxWinding Dense.Gaussian.Path.Box.Boundary.boxBoundary
  rw [Dense.Gaussian.Path.Box.Sides.horizontalEdge_normalize p box.yLower box.xLower box.xUpper,
    Dense.Gaussian.Path.Box.Sides.verticalEdge_normalize p box.xUpper box.yLower box.yUpper,
    Dense.Gaussian.Path.Box.Sides.horizontalEdge_normalize p box.yUpper box.xUpper box.xLower,
    Dense.Gaussian.Path.Box.Sides.verticalEdge_normalize p box.xLower box.yUpper box.yLower]

/-- Expand the raw box winding as the sum of its four oriented doubled edge indices.

The bottom, right, top and left edges retain the boundary orientation and their
original endpoints. The displayed sum uses their doubled indices in that order. -/
public theorem quadrupledBoxWinding_eq (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box :
  Box) :
    quadrupledBoxWinding p box =
      (Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yLower box.xLower box.xUpper).doubledWinding +
      (Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xUpper box.yLower box.yUpper).doubledWinding +
      (Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yUpper box.xUpper box.xLower).doubledWinding +
      (Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xLower box.yUpper box.yLower).doubledWinding := by
  simp only [quadrupledBoxWinding, Dense.Gaussian.Path.Box.Boundary.boxBoundary, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring1

/-- Divide the boundary index sum by two to obtain doubled box winding.

The same original integer quotient is used on the retained four-edge sum,
including its total behavior when no divisibility certificate is supplied. -/
@[expose] public def doubledBoxWinding (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box :
  Box) : Int :=
  quadrupledBoxWinding p box / 2

/-- Divide the boundary index sum by four to obtain box winding.

The same original integer quotient is used on the retained four-edge sum.
Separate divisibility certificates justify its mathematical winding interpretation. -/
@[expose] public def boxWinding (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box) :
  Int :=
  quadrupledBoxWinding p box / 4
end Purelib.Polynomial.Winding.Box.Basic
