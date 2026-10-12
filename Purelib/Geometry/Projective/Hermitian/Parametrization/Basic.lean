module

import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Line.Gaussian
public import Purelib.Geometry.Projective.Line.Hermitian
public import Purelib.RationalFunctions.Curve.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Line.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Hermitian

open Purelib.RationalFunctions

section
@[expose] public section

/-!
# Rational parameterizations of CCL comparison boundaries

Coordinate lines and centered circles are transported through an invertible
finite homography by its explicit adjugate.  The resulting rational curve is
proved to lie on the corresponding Hermitian comparison boundary at every
non-pole parameter.  This is the provenance-preserving bridge needed before
the cleared gcd/Sturm classifier can inspect parser-formula boundaries.
-/

namespace Purelib.Geometry.Projective.Hermitian

set_option genInjectivity false in
/-- A rational parametrization of a Hermitian zero boundary with uniform positive weight.

The record retains the curve, a strictly positive lower bound for every homogeneous weight, projective validity at all
parameters, and the boundary equation wherever the affine denominator is nonzero. -/
structure Parametrization (form : Hermitian.HermitianForm)
  where
  /-- The rational curve parametrizing the Hermitian zero boundary. -/ curve : Curve.RationalCurve
  /-- A uniform rational lower bound for the homogeneous curve weight. -/ weightLower : Fraction.Rational
  /-- The retained homogeneous-weight lower bound is strictly positive. -/ weightLowerPositive : 0 < weightLower
  /-- The retained lower bound applies at every rational parameter. -/ weightLower_le : ∀ parameter, weightLower ≤
    Proj.weight
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩
  /-- The numerator and denominator never vanish simultaneously at a parameter. -/ projectiveValid : ∀ parameter,
    Proj.HasNonzeroCoordinate
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩
  /-- Every parameter with nonzero denominator evaluates to a zero of the Hermitian form. -/ onBoundary : ∀ parameter,
    curve.denominatorAt parameter ≠ 0 →
      form.eval (curve.point parameter) = 0

constructive_injectivity Parametrization

namespace Parametrization.mk

end Parametrization.mk

end Purelib.Geometry.Projective.Hermitian

end
