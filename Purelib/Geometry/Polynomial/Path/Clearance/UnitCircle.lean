module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Gaussian.UnitCircle.Quarter
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Gaussian.UnitCircle

open Purelib.Polynomial.Clearance

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Path

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

namespace Purelib.Geometry.Polynomial.Path.Clearance.UnitCircle
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- A quarter rotation is a fixed nonzero constant path with exact norm-two clearance. -/
def unitCircuitRotationConstantCertificate
    (quarter : Quarter.UnitCircuitQuarter) (origin direction : Data.Gaussian.Basic.Canonical) :
    Pair.Basic.Certificate
      (Components.pathReal
        (Constants.gaussianConstant (Quarter.unitCircuitRotation quarter))
        origin direction)
      (Components.pathImag
        (Constants.gaussianConstant (Quarter.unitCircuitRotation quarter))
        origin direction)
      { lower := 0, upper := 1, valid := by decide } where
  bound := 2
  positive := by decide
  lower := by
    intro time _timeInside
    have lower : (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (Quarter.unitCircuitRotation
      quarter) :=
      (Quarter.unitCircuitRotation_normSq quarter).ge
    simpa only [Components.eval_pathReal,
      Components.eval_pathImag,
      Constants.gaussianConstant_eval, Data.Gaussian.Norm.Basic.normSq] using lower
end Purelib.Geometry.Polynomial.Path.Clearance.UnitCircle

end
