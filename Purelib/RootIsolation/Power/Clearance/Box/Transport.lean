module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Intervals
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Path
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Power.Gaussian
public import Purelib.RootIsolation.Power.Clearance.Path.Transport
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Polynomial.Clearance.Box.Line.Basic (HorizontalLineClearance VerticalLineClearance)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Clearance.Box.Transport

open Purelib.Data.Gaussian

/-- Transport horizontal-line clearance for `Z^d - source` to `Z^d - target`.

The squared parameter displacement must be below the retained original clearance bound; the result keeps the same
ambient box and line coordinate. -/
def horizontalClearanceAfterMove
    {source target : Canonical} (degree : RootDegree)
    {ambient : Box} {y : Fraction.Rational}
    (clearance : HorizontalLineClearance
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree) ambient y)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < clearance.bound) :
    HorizontalLineClearance
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree) ambient y :=
  Clearance.Box.Line.Path.horizontalOfPathCertificate
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree) ambient y
      (Power.Clearance.Path.Transport.pathCertificateAfterMove degree clearance.toPathCertificate small)
end Purelib.RootIsolation.Power.Clearance.Box.Transport

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Clearance.Box.Transport

open Purelib.Data.Gaussian

/-- Exact transported horizontal-line clearance bound. -/
@[simp] theorem horizontalClearanceAfterMove_bound
    {source target : Canonical} (degree : RootDegree)
    {ambient : Box} {y : Fraction.Rational}
    (clearance : HorizontalLineClearance
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree) ambient y)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < clearance.bound) :
    (horizontalClearanceAfterMove degree clearance small).bound =
      (clearance.bound - Data.Gaussian.Norm.Basic.normSq (source - target)) ^ 2 /
        (4 * max 1
          (Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                (Gaussian.Cast.Imaginary.horizontalBase y)
                  Gaussian.Constants.horizontalDirection)
              (Box.Intervals.horizontalInterval ambient) +
            Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                (Gaussian.Cast.Imaginary.horizontalBase y)
                  Gaussian.Constants.horizontalDirection)
              (Box.Intervals.horizontalInterval ambient))) := by
  unfold horizontalClearanceAfterMove
  rw [Clearance.Box.Line.Path.horizontalOfPathCertificate_bound,
    Power.Clearance.Path.Transport.pathCertificateAfterMove_bound,
    HorizontalLineClearance.toPathCertificate_bound]
end Purelib.RootIsolation.Power.Clearance.Box.Transport

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Clearance.Box.Transport

open Purelib.Data.Gaussian

/-- Transport vertical-line clearance for `Z^d - source` to `Z^d - target`.

The squared parameter displacement must be below the retained original clearance bound; the result keeps the same
ambient box and line coordinate. -/
def verticalClearanceAfterMove
    {source target : Canonical} (degree : RootDegree)
    {ambient : Box} {x : Fraction.Rational}
    (clearance : VerticalLineClearance
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree) ambient x)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < clearance.bound) :
    VerticalLineClearance
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree) ambient x :=
  Clearance.Box.Line.Path.verticalOfPathCertificate
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree) ambient x
      (Power.Clearance.Path.Transport.pathCertificateAfterMove degree clearance.toPathCertificate small)
end Purelib.RootIsolation.Power.Clearance.Box.Transport

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Clearance.Box.Transport

open Purelib.Data.Gaussian

/-- Exact transported vertical-line clearance bound. -/
@[simp] theorem verticalClearanceAfterMove_bound
    {source target : Canonical} (degree : RootDegree)
    {ambient : Box} {x : Fraction.Rational}
    (clearance : VerticalLineClearance
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree) ambient x)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < clearance.bound) :
    (verticalClearanceAfterMove degree clearance small).bound =
      (clearance.bound - Data.Gaussian.Norm.Basic.normSq (source - target)) ^ 2 /
        (4 * max 1
          (Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
              (Box.Intervals.verticalInterval ambient) +
            Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
              (Box.Intervals.verticalInterval ambient))) := by
  unfold verticalClearanceAfterMove
  rw [Clearance.Box.Line.Path.verticalOfPathCertificate_bound,
    Power.Clearance.Path.Transport.pathCertificateAfterMove_bound,
    VerticalLineClearance.toPathCertificate_bound]
end Purelib.RootIsolation.Power.Clearance.Box.Transport

end
