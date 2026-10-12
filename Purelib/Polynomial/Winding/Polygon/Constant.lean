module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Winding.Edge.Constant
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

open Purelib.Data

open Purelib.Polynomial

section
public section

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

namespace Purelib.Polynomial.Winding.Polygon.Constant

/-- A nonzero constant Gaussian polynomial contributes zero raw winding to
every finite open polygonal chain. -/
theorem chainRaw_gaussianConstant_zero
    {constantValue : Gaussian.Basic.Canonical} (nonzero : constantValue ≠ 0) :
    ∀ (start : Gaussian.Basic.Canonical) (vertices : List Gaussian.Basic.Canonical),
      Winding.Polygon.Basic.chainRaw (Dense.Gaussian.Constants.gaussianConstant constantValue)
        start vertices = 0
  | _, [] => rfl
  | start, finish :: remaining => by
      simp only [-eq_self, -iff_self, Winding.Polygon.Basic.chainRaw, Dense.Gaussian.Path.Segment.segment]
      rw [Purelib.Polynomial.Winding.Edge.Constant.gaussianConstant_edge_winding_zero
        nonzero start (finish - start) 0 1,
        Purelib.Polynomial.Winding.Polygon.Constant.chainRaw_gaussianConstant_zero nonzero finish remaining,
        Int.Arithmetic.zero_add]
end Purelib.Polynomial.Winding.Polygon.Constant

end
