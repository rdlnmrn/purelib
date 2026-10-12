module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.Polynomial.Dense.Rational.Pair.Path.Basic.PolynomialEdge

/-- The edge obtained by evaluating `p` on `origin + t * direction`. -/
def ofLine (p :
  CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (start stop : Fraction.Rational) :
      Dense.Rational.Pair.Path.Basic.PolynomialEdge where
  realPart := Dense.Gaussian.Path.Components.pathReal p origin direction
  imagPart := Dense.Gaussian.Path.Components.pathImag p origin direction
  start := start
  stop := stop

/-- Normalizing the Gaussian polynomial leaves its retained rational line edge unchanged. -/
@[simp] theorem ofLine_normalize
    (p : CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (start stop : Fraction.Rational) :
    ofLine p.normalize origin direction start stop =
      ofLine p origin direction start stop := by
  unfold ofLine
  rw [Dense.Gaussian.Path.Components.pathReal_normalize, Dense.Gaussian.Path.Components.pathImag_normalize]

/-- The real polynomial of the retained line edge evaluates to the Gaussian line value's real coordinate. -/
@[simp] theorem ofLine_real_eval (p :
  CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (start stop t : Fraction.Rational) :
    (ofLine p origin direction start stop).realPart.eval t =
      (p.eval (Geometry.Rational.Affine.line origin direction t)).re := by
  exact Dense.Gaussian.Path.Components.eval_pathReal p origin direction t

/-- The imaginary polynomial of the retained line edge evaluates to the Gaussian line value's imaginary coordinate. -/
@[simp] theorem ofLine_imag_eval (p :
  CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (start stop t : Fraction.Rational) :
    (ofLine p origin direction start stop).imagPart.eval t =
      (p.eval (Geometry.Rational.Affine.line origin direction t)).im := by
  exact Dense.Gaussian.Path.Components.eval_pathImag p origin direction t
end Purelib.Polynomial.Dense.Rational.Pair.Path.Basic.PolynomialEdge

end
