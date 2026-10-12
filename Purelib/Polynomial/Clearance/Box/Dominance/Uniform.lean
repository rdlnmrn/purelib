module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Clearance.Box.Dominance.Uniform
open Purelib.Data.Gaussian

/-! ## From a uniform error bound to finite Rouché data -/

/-- A strict uniform perturbation bound below a displayed boundary clearance
is exactly the finite norm-dominance record consumed by constructive Rouché
transfer. -/
def boundaryNormDominanceOfUniformBound
    (base perturbation : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance base box)
    (bound : Fraction.Rational)
    (strict : bound < clearance.bound)
    (uniform : ∀ z : Gaussian.Basic.Canonical, Box.Boundary.OnBoxBoundary box z →
      Gaussian.Basic.Canonical.normSq (perturbation.eval z) ≤ bound) :
    Clearance.Box.Dominance.Basic.BoundaryNormDominance base perturbation box where
  margin := clearance.bound - bound
  positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_pos_direct strict
  lower := by
    intro z boundary
    exact Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_le_sub_direct
      (clearance.lower z boundary) (uniform z boundary)

end Purelib.Polynomial.Clearance.Box.Dominance.Uniform

end
