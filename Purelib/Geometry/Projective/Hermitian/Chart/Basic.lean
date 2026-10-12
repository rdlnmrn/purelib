module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Hermitian
public import Purelib.RationalFunctions.Curve.Projective.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Interval

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Hermitian

open Purelib.RationalFunctions.Curve

section
@[expose] public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.Geometry.Projective.Hermitian.Chart

set_option genInjectivity false in
/-- One parameterization paired with its finite proper parameter cell. -/
structure BoundedChart (form : Hermitian.HermitianForm) where
  /-- The certified rational parametrization of the given Hermitian boundary. -/ parameterization :
    Geometry.Projective.Hermitian.Parametrization form
  /-- The finite proper interval restricting the chart parameter. -/ cell : Proper.Cell

constructive_injectivity BoundedChart

namespace BoundedChart

/-- Homogeneous projective value of one bounded boundary chart. -/
def projective {form : Hermitian.HermitianForm} (chart :
  BoundedChart form)
    (parameter : Fraction.Rational) : Line.GaussianLine :=
  Projective.projective
    chart.parameterization.curve parameter

/-- Every displayed chart parameter is a genuine homogeneous projective point, including parameters at which its affine
denominator vanishes. -/
theorem projective_valid
    {form : Hermitian.HermitianForm} (chart : BoundedChart form)
    (parameter : Fraction.Rational) :
    Proj.HasNonzeroCoordinate
      (chart.projective parameter) :=
  chart.parameterization.projectiveValid parameter

/-- The parameterization's coefficient-computed positive projective-weight lower bound applies uniformly to every
displayed chart parameter. -/
theorem weightLower_le_projective
    {form : Hermitian.HermitianForm} (chart : BoundedChart form)
    (parameter : Fraction.Rational) :
    chart.parameterization.weightLower ≤
      Proj.weight (chart.projective parameter) :=
  chart.parameterization.weightLower_le parameter

/-- Every parameter of the boundary chart has strictly positive homogeneous weight. -/
theorem projective_weight_pos
    {form : Hermitian.HermitianForm} (chart : BoundedChart form)
    (parameter : Fraction.Rational) :
    0 < Proj.weight (chart.projective parameter) :=
  chart.parameterization.weightLowerPositive.trans_le
    (chart.weightLower_le_projective parameter)
end BoundedChart
end Purelib.Geometry.Projective.Hermitian.Chart

end
