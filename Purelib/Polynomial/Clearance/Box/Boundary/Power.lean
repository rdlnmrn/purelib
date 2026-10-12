module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Constant
public import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Power
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Winding of finite weighted multiplicity products

This module connects the executable multiplicity polynomial from
`ConstructiveMultiplicity` to the finite box product formula.  Powers are
structural recursion over a displayed natural number; no root collection or
factor evaluation over a completed carrier is introduced.
-/

namespace Purelib.Polynomial.Clearance.Box.Boundary.Power

/-- A boundary clearance for one factor induces a clearance for every
displayed finite power. -/
def polynomialPower_boundaryClearance
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) :
    ∀ exponent : Nat, BoundaryClearance
      (Dense.Gaussian.Power.polynomialPower p exponent) box
  | 0 => by
      exact Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance
        one_ne_zero box
  | exponent + 1 =>
      BoundaryClearance.mul clearance
        (polynomialPower_boundaryClearance clearance exponent)

end Purelib.Polynomial.Clearance.Box.Boundary.Power

end
