module

import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Indexed rational eliminants for axis-parallel coordinate lines

The retained vertical and horizontal rational polynomials have nonzero and
bounded-degree certificates. Their pointwise nonzero evaluations produce
finite Bézout data for the same Gaussian source polynomial and coordinate line.
The certificate retains the original polynomial and supplied degree bound.
-/

open Purelib.Data.Rat
open Purelib.Polynomial

namespace Purelib.Polynomial.Elimination.Axis.Certificate

namespace AxisSafeCuts

@[expose] public section

set_option genInjectivity false in
/-- Retained vertical and horizontal eliminants with indexed finite Bézout certificates.

Each original rational eliminant is nonzero with degree at most the supplied
bound. Its nonzero evaluation at a displayed coordinate returns the retained
Bézout certificate for the corresponding source-polynomial axis line. -/
structure AxisEliminationCertificate
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (degreeBound : Nat) where
  /-- The retained rational eliminant for vertical coordinate lines. -/ vertical :
    Dense.Rational.Basic.CoordinatePolynomial
  /-- The retained rational eliminant for horizontal coordinate lines. -/ horizontal :
    Dense.Rational.Basic.CoordinatePolynomial
  /-- The vertical eliminant is nonzero. -/ vertical_nonzero : vertical.isZero = false
  /-- The horizontal eliminant is nonzero. -/ horizontal_nonzero : horizontal.isZero = false
  /-- The vertical eliminant degree fits the retained search bound. -/ vertical_degree : vertical.natDegree ≤
    degreeBound
  /-- The horizontal eliminant degree fits the retained search bound. -/ horizontal_degree : horizontal.natDegree ≤
    degreeBound
  /-- A nonzero vertical-eliminant value supplies an exact Bezout certificate for that line's two coordinate
    polynomials. -/ vertical_coprime : ∀ x : Fraction.Rational, vertical.eval x ≠ 0 →
    Dense.Rational.Bezout.Basic.CoprimeCertificate (Dense.Gaussian.Path.Axis.verticalPathReal p x)
      (Dense.Gaussian.Path.Axis.verticalPathImag p x)
  /-- A nonzero horizontal-eliminant value supplies an exact Bezout certificate for that line's two coordinate
    polynomials. -/ horizontal_coprime : ∀ y : Fraction.Rational, horizontal.eval y ≠ 0 →
    Dense.Rational.Bezout.Basic.CoprimeCertificate (Dense.Gaussian.Path.Axis.horizontalPathReal p y)
      (Dense.Gaussian.Path.Axis.horizontalPathImag p y)

constructive_injectivity AxisEliminationCertificate

end

end AxisSafeCuts

end Purelib.Polynomial.Elimination.Axis.Certificate
