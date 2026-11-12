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

open Purelib.Polynomial.Dense.Gaussian.Path

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
      PolynomialEdge :=
  let parts := Components.pathParts p origin direction
  { realPart := parts.1
    imagPart := parts.2
    start := start
    stop := stop }

/-- The original line edge retains the complete two-coordinate path record.

Both polynomials are read from the same retained affine substitution. The
record keeps its original parameter interval and ordered coordinates.
-/
theorem ofLine_eq (p : CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (start stop : Fraction.Rational) :
    ofLine p origin direction start stop =
      { realPart := Components.pathReal p origin direction
        imagPart := Components.pathImag p origin direction
        start := start
        stop := stop } := (rfl)

/-- Normalizing the Gaussian polynomial leaves its retained rational line edge unchanged. -/
@[simp] theorem ofLine_normalize
    (p : CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (start stop : Fraction.Rational) :
    ofLine p.normalize origin direction start stop =
      ofLine p origin direction start stop := by
  unfold ofLine Components.pathParts
  rw [Dense.Gaussian.Substitution.Affine.composeLine_normalize]

/-- The real polynomial of the retained line edge evaluates to the Gaussian line value's real coordinate. -/
@[simp] theorem ofLine_real_eval (p :
  CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (start stop t : Fraction.Rational) :
    (ofLine p origin direction start stop).realPart.eval t =
      (p.eval (Geometry.Rational.Affine.line origin direction t)).re := by
  exact Components.eval_pathReal p origin direction t

/-- The imaginary polynomial of the retained line edge evaluates to the Gaussian line value's imaginary coordinate. -/
@[simp] theorem ofLine_imag_eval (p :
  CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (start stop t : Fraction.Rational) :
    (ofLine p origin direction start stop).imagPart.eval t =
      (p.eval (Geometry.Rational.Affine.line origin direction t)).im := by
  exact Components.eval_pathImag p origin direction t
end Purelib.Polynomial.Dense.Rational.Pair.Path.Basic.PolynomialEdge

end
