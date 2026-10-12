module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Rat.Fraction

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Aggregate horizontal quartic sample certificates

This module connects the exact rational samples emitted by the standalone
Python generator to the 64 canonical centered edges of the prepared
A-forward horizontal connector, then aggregates the local error bounds by
finite Cauchy--Schwarz.
-/

namespace Purelib.Polynomial.Geometry.ClearPath.Constant

/-- Every point of every retained path segment equals the supplied base.

The predicate follows the finite segment list; the empty path satisfies it without an endpoint condition. -/
public def PathPointConstant
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} (base : Gaussian.Basic.Canonical) :
    {start finish : Gaussian.Basic.Canonical} ->
      ClearPath polynomial ambient start finish -> Prop
  | _, _, .nil _ => True
  | _, _, .cons head tail =>
      (forall parameter, head.pointAt parameter = base) ∧
        Purelib.Polynomial.Geometry.ClearPath.Constant.PathPointConstant base tail

end Purelib.Polynomial.Geometry.ClearPath.Constant

end
