module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Polynomial.Clearance.Box.Boundary.Basic

set_option genInjectivity false in
/-- A positive squared-norm lower bound on all four sides. -/
structure BoundaryClearance
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Geometry.Rational.Box) where
  /-- The common lower bound on boundary evaluation quadrance. -/ bound : Fraction.Rational
  /-- The boundary quadrance bound is positive. -/ positive : 0 < bound
  /-- Every displayed boundary point satisfies the retained quadrance bound. -/ lower : ∀ z : Gaussian.Basic.Canonical,
    Geometry.Rational.Box.Boundary.OnBoxBoundary box z →
    bound ≤ Gaussian.Basic.Canonical.normSq (p.eval z)

constructive_injectivity BoundaryClearance

/-- Boundary clearance makes every displayed boundary evaluation nonzero. -/
theorem BoundaryClearance.eval_ne_zero
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Geometry.Rational.Box}
    (clearance : BoundaryClearance p box) {z : Gaussian.Basic.Canonical}
    (boundary : Geometry.Rational.Box.Boundary.OnBoxBoundary box z) : p.eval z ≠ 0 := by
  intro zero
  have lower := clearance.lower z boundary
  rw [zero, Gaussian.Basic.Canonical.normSq_zero] at lower
  exact (not_lt_of_ge lower) clearance.positive
end Purelib.Polynomial.Clearance.Box.Boundary.Basic

end
