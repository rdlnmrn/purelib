module
public import Purelib.Integration.Polynomial.Rational.Continuous
public import Purelib.Integration.Cell.Source.Continuous.Affine
public import Purelib.Polynomial.Dense.Rational.Substitution.Affine

/-!
# Finite rational polynomial integration on oriented endpoints

The original dense coefficient list is affinely substituted using its owned
finite Horner operation. Its resulting modulus drives the existing oriented
source integration process; the original polynomial and endpoints are retained.
-/

public section

namespace Purelib.Integration.Polynomial.Rational.Continuous.Affine

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Partition
open Purelib.Polynomial.Dense.Rational

/-- Substitute the retained rational endpoint map into the original finite polynomial. -/
@[expose] def substituted (polynomial : Basic.CoordinatePolynomial) (interval : Partition.Interval) :
    Basic.CoordinatePolynomial :=
  Substitution.Affine.subst polynomial interval.start interval.signedLength

/-- The substituted polynomial reads the original polynomial at the same affine rational point. -/
theorem substituted_eval (polynomial : Basic.CoordinatePolynomial) (interval : Partition.Interval)
    (point : Fraction.Rational) :
    (substituted polynomial interval).eval point =
      SourceFrontier.Continuous.Affine.pullback polynomial.eval interval point :=
  Substitution.Affine.subst_eval polynomial interval.start interval.signedLength point

/-- Compute a modulus for the original polynomial on the retained oriented endpoint interval.

The original finite affine substitution supplies the coefficient table, and
its exact pointwise readback transports the existing executable polynomial
modulus to the original source's affine parameter. -/
@[expose] def modulus (polynomial : Basic.CoordinatePolynomial) (interval : Partition.Interval) :
    Rational.Uniform.Modulus (SourceFrontier.Continuous.Affine.pullback polynomial.eval interval) :=
  (Bounds.Uniform.modulus (substituted polynomial interval)).transport
    (fun point _ _ => (substituted_eval polynomial interval point).symm)

/-- Construct finite oriented integration bounds from the original polynomial and rational endpoints. -/
@[expose] def boundProcess (polynomial : Basic.CoordinatePolynomial) (interval : Partition.Interval) : BoundProcess :=
  SourceFrontier.Continuous.Affine.boundProcess polynomial.eval interval (modulus polynomial interval)

end Purelib.Integration.Polynomial.Rational.Continuous.Affine

end
