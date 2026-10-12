module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Power
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Power
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Product
import Purelib.Tactic.Ring

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

namespace Purelib.Polynomial.Winding.Box.Power

/-- Raw winding of a finite polynomial power is the displayed exponent
times the factor winding. -/
theorem quadrupledBoxWinding_polynomialPower
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} (proper : box.Proper)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) (exponent : Nat) :
    Winding.Box.Basic.quadrupledBoxWinding
        (Dense.Gaussian.Power.polynomialPower p exponent) box =
      (exponent : Int) * Winding.Box.Basic.quadrupledBoxWinding p box := by
  induction exponent with
  | zero =>
      simp only [Dense.Gaussian.Power.polynomialPower, Nat.cast_zero,
        zero_mul]
      exact Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant
        one_ne_zero box
  | succ exponent inductionHypothesis =>
      have product :=
        Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
          p (Dense.Gaussian.Power.polynomialPower p exponent) box
          proper clearance (Clearance.Box.Boundary.Power.polynomialPower_boundaryClearance clearance exponent)
      rw [Dense.Gaussian.Power.polynomialPower, product,
        inductionHypothesis]
      rw [Nat.cast_succ]
      ring1

end Purelib.Polynomial.Winding.Box.Power

end
