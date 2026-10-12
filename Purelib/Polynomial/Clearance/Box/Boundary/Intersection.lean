module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Geometry.Rational.Box.Intersection
import Purelib.Geometry.Rational.Box.Intersection.Boundary
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation

/-!
# Boundary clearance of retained box intersections

A supplied common subbox certifies ordered intersection endpoints. Their sides
are selected from the input boxes, so their original boundary certificates
supply the minimum of the two retained clearance bounds without a new scan.
-/

public section

namespace Purelib.Polynomial.Clearance.Box.Boundary.Intersection

open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.Rat

namespace BoxClearance.BoundaryClearance

/-- Reuse both input boundary certificates with their exact minimum bound.

The common inner box supplies geometric evidence of ordered endpoints. Every
intersection side keeps one original clearance certificate at that bound. -/
@[expose] def intersection {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {first
  second common :
  Box}
    (left : Clearance.Box.Boundary.Basic.BoundaryClearance polynomial first) (right :
      Clearance.Box.Boundary.Basic.BoundaryClearance polynomial second)
    (inFirst : common.Refines first) (inSecond : common.Refines second) :
    Clearance.Box.Boundary.Basic.BoundaryClearance polynomial (Box.Intersection.intersection first second
      common inFirst inSecond) where
  bound := min left.bound right.bound
  positive := Fraction.Order.Basic.lt_min left.positive right.positive
  lower := by
    intro point boundary
    rcases Box.Intersection.Boundary.intersection_boundary boundary with boundary | boundary
    · exact Data.Rat.Fraction.Order.Basic.le_trans _ _ _
        (Fraction.Order.Basic.min_le_left _ _) (left.lower point boundary)
    · exact Data.Rat.Fraction.Order.Basic.le_trans _ _ _
        (Fraction.Order.Basic.min_le_right _ _) (right.lower point boundary)

end BoxClearance.BoundaryClearance
end Purelib.Polynomial.Clearance.Box.Boundary.Intersection
