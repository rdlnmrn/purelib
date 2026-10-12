module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Extension
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Hermitian.Formula
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Geometry.Projective.Hermitian.Formula (BoundaryFormula)
open Purelib.Polynomial.Dense.Basic (RationalPolynomial)
open Purelib.Polynomial.Dense.Rational.Factorization (ConditionProfile)
open Purelib.Polynomial.Dense.Rational.Squarefree (Factor)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RationalFunctions

section
@[expose] public section

/-!
# CCL formulas cleared along rational boundary curves

Every Hermitian atom pulled back to a rational curve is compiled to one
explicit univariate rational polynomial.  Its value is the original atom
form multiplied by the positive quadrance of the curve denominator, so all
six parser sign tests are preserved at every displayed non-pole parameter.

This finite compiler lets the event layer feed all atoms of a candidate
one-bit formula into the existing equality/apart gcd profiler.  No affine
point, polynomial root, or limiting value is introduced by the translation.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile.Formula

/-! ## Finite formula refinement of an existing event profile -/

/-- Extend an already denominator/box-classified event profile by every
cleared atom polynomial of one candidate CCL formula.  Existing relations are
descended through the new gcd pieces, so the denominator and box certificates
are retained alongside the new formula relations. -/
def extendProfile
    {source : Factor}
    {existing : List RationalPolynomial}
    (curve : Curve.RationalCurve) (formula : BoundaryFormula)
    (profile : ConditionProfile
      source existing) :
    Dense.Rational.Factorization.ConditionProfileExtensions
      profile (Curve.Hermitian.Formula.conditionPolynomials curve formula) :=
  Dense.Rational.Factorization.extendProfileConditions profile
    (Curve.Hermitian.Formula.conditionPolynomials curve formula)

open Purelib.RootIsolation
/-- The formula extension is finite and nonempty. -/
theorem extendProfile_nonempty
    {source : Factor}
    {existing : List RationalPolynomial}
    (curve : Curve.RationalCurve) (formula : BoundaryFormula)
    (profile : ConditionProfile
      source existing) :
    (extendProfile curve formula profile).profiles ≠ [] :=
  (extendProfile curve formula profile).nonempty

/-- A separately supplied rational zero of the old profile factor is covered
by one extended formula profile, and conversely.  No zero is produced by this
statement. -/
theorem extendProfile_rootCoverage
    {source : Factor}
    {existing : List RationalPolynomial}
    (curve : Curve.RationalCurve) (formula : BoundaryFormula)
    (profile : ConditionProfile
      source existing)
    (parameter : Fraction.Rational) :
    profile.factor.polynomial.eval parameter = 0 ↔
      ∃ next ∈ (extendProfile curve formula profile).profiles,
        next.factor.polynomial.eval parameter = 0 :=
  (extendProfile curve formula profile).rootCoverage parameter

end Purelib.RootIsolation.Curve.Event.Profile.Formula

end
