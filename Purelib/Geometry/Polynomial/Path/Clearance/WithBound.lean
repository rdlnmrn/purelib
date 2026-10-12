module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Polynomial.Clearance

/-!
# Affine-path clearance with an exact retained bound

The carrier retains the original polynomial-pair certificate on its supplied
interval and an equality specifying that certificate's rational bound.
-/

namespace Purelib.Geometry.Polynomial.Path.Clearance.WithBound

set_option genInjectivity false in
/-- A polynomial-pair clearance certificate with a prescribed bound.

Retain the actual certificate for the two polynomials on the given interval and an equality identifying its bound with
the supplied rational. -/
public structure PathCertificateWithBound
    (real imaginary : Dense.Basic.DensePolynomial Fraction.Rational)
    (interval : Data.Rat.Interval.Bounds) (boundValue : Fraction.Rational) where
  /-- The retained clearance certificate for this polynomial pair and interval. -/ value : Pair.Basic.Certificate
    real imaginary interval
  /-- The certificate uses exactly the prescribed rational bound. -/ bound : value.bound = boundValue

constructive_injectivity PathCertificateWithBound

end Purelib.Geometry.Polynomial.Path.Clearance.WithBound
