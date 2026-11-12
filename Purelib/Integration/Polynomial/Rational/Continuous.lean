module
public import Purelib.Polynomial.Dense.Rational.Bounds.Uniform
public import Purelib.Integration.Cell.Source.Continuous.Comparison
public import Purelib.Integration.Cell.Source.Continuous.Producer

/-!
# Effective integration of finite rational polynomials

The original dense coefficient list supplies both its exact evaluator and an
effective variation modulus. Each positive request builds a finite rational
source frontier and a certified midpoint answer.
-/

public section

namespace Purelib.Integration.Polynomial.Rational.Continuous

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.SourceFrontier
open Purelib.Polynomial.Dense.Rational

/-- Build a finite integration enclosure directly from the original rational polynomial and request. -/
@[expose] def integrate (polynomial : Basic.CoordinatePolynomial) (request : AccuracyRequest) :
    SourceFrontier.Continuous.Result (Bounds.Uniform.modulus polynomial) :=
  SourceFrontier.Continuous.build (Bounds.Uniform.modulus polynomial) request

/-- Two finite requests for the same original polynomial give answers within their requested widths. -/
theorem answer_difference_lt (polynomial : Basic.CoordinatePolynomial) (left right : AccuracyRequest) :
    Fraction.abs ((integrate polynomial left).answer - (integrate polynomial right).answer) <
      left.tolerance + right.tolerance :=
  (integrate polynomial left).answer_difference_lt_of_same (integrate polynomial right) (fun _ _ _ => rfl)

/-- Construct persistent rational integration bounds directly from the original finite polynomial. -/
@[expose] def boundProcess (polynomial : Basic.CoordinatePolynomial) : BoundProcess :=
  (SourceFrontier.Continuous.producer (Bounds.Uniform.modulus polynomial)).boundProcess

/-- Construct the original cell-splitting integration process directly from the finite polynomial. -/
@[expose] def integrationProcess (polynomial : Basic.CoordinatePolynomial) :
    IntegrationProcess (SourcePoint polynomial.eval) :=
  (SourceFrontier.Continuous.producer (Bounds.Uniform.modulus polynomial)).integrationProcess

end Purelib.Integration.Polynomial.Rational.Continuous

end
