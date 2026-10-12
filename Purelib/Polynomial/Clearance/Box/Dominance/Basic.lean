module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Norm.Basic
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
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace Purelib.Polynomial.Clearance.Box.Dominance.Basic

set_option genInjectivity false in
/-- One positive rational margin for strict squared-norm dominance on every
point of a finite box boundary. -/
structure BoundaryNormDominance
    (p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Geometry.Rational.Box)
      where
  /-- The retained lower bound on the difference of polynomial quadrances. -/ margin : Fraction.Rational
  /-- The dominance margin is positive. -/ positive : 0 < margin
  /-- The first polynomial's quadrance exceeds the second by at least the margin throughout the box boundary. -/ lower :
    ∀ z : Gaussian.Basic.Canonical,
    Geometry.Rational.Box.Boundary.OnBoxBoundary box z →
      margin ≤ Gaussian.Basic.Canonical.normSq (p.eval z) - Gaussian.Basic.Canonical.normSq (q.eval z)

constructive_injectivity BoundaryNormDominance

end Purelib.Polynomial.Clearance.Box.Dominance.Basic

end
