module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Dense.Gaussian.Constants

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Geometry.Rational

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

namespace Purelib.Polynomial.Clearance.Box.Boundary.Constant

/-- A nonzero constant polynomial carries its exact norm as a quantitative
boundary clearance on every box. -/
def gaussianConstant_boundaryClearance
    {c : Gaussian.Basic.Canonical} (nonzero : c ≠ 0) (box : Box) :
    Clearance.Box.Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Constants.gaussianConstant c) box where
  bound := Gaussian.Basic.Canonical.normSq c
  positive := by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      Gaussian.Norm.Basic.normSq_pos nonzero
  lower := by
    intro z _boundary
    rw [Dense.Gaussian.Constants.gaussianConstant_eval]
end Purelib.Polynomial.Clearance.Box.Boundary.Constant

end
