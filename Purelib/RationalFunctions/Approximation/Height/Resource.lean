module

import Purelib.Approximation.Rational.QuadraticTarget.Basic
public import Purelib.Approximation.Rational.QuadraticTarget.Resource
import Purelib.Data.Gaussian.Basic

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.Approximation.Height.Budget
import Purelib.RationalFunctions.Residual.Local.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.RationalFunctions.Approximation.Height.Resource

/-! ## Protected quotient targets -/

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Compute the square-threshold comparison budget for the protected quotient target.

The budget uses the context's exact residual coefficient and the supplied rational target through the shared
quadratic-target construction. -/
def protectedTargetComparisonBudget
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Rational.Box}
    (context : Residual.Local.Basic.LocalQuotientContext
      source opposite ambient)
    (target : Rat.Fraction.Rational) : Nat :=
  Rational.QuadraticTarget.Resource.targetComparisonBudget
    (Approximation.Height.Budget.targetCoefficient context) target
end Purelib.RationalFunctions.Approximation.Height.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.RationalFunctions.Approximation.Height.Resource

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- The protected quotient denominator satisfies the exact square-threshold bracket.

Its predecessor squared is at most the computed target ceiling, and its own square is strictly greater. Both quantities
use the same context coefficient and rational target. -/
theorem protectedTargetDenominator_bracket
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Rational.Box}
    (context : Residual.Local.Basic.LocalQuotientContext
      source opposite ambient)
    (target : Rat.Fraction.Rational) :
    let input := Rational.QuadraticTarget.Resource.targetCeiling
      (Approximation.Height.Budget.targetCoefficient context) target
    let output := Rational.QuadraticTarget.Basic.targetDenominator
      (Approximation.Height.Budget.targetCoefficient context) target
    (output - 1) * (output - 1) ≤ input ∧ input < output * output :=
  Rational.QuadraticTarget.Resource.targetDenominator_bracket _ _
end Purelib.RationalFunctions.Approximation.Height.Resource

end
