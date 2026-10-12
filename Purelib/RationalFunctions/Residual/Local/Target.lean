module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RationalFunctions.Residual.Basic
import Purelib.RationalFunctions.Residual.Local.Basic
public import Purelib.RootIsolation.Residual.Chordal.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RationalFunctions.Residual.Local.Prepare
import Purelib.RationalFunctions.Residual.Local.Bounds

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

section
@[expose] public section

/-!
# Two-way residual and chordal bounds for rational functions

For a reduced coprime pair, a protectedState source track has a uniform positive
margin for the opposite polynomial.  This converts the polynomial
box-to-residual and residual-to-box theorems into corresponding theorems for
the quotient.  Swapping source and opposite gives the pole statements.
-/

namespace Purelib.RationalFunctions.Residual.Local.Basic
namespace LocalQuotientContext

variable {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Scale the polynomial residual target by the reciprocal of the opposite-polynomial majorant.

The target retains the exact squarefree certificate, winding-one state, displayed sample and epsilon request of the
polynomial residual construction. -/
def quotientResidualTarget
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    (squarefree : SquarefreeCertificate source)
    (state : WindingOneState source ambient)
    (sample : Canonical) (epsilon : Rational) : Rational :=
  Residual.Chordal.Basic.residualTarget squarefree state sample
      epsilon /
    context.oppositeMajorant

/-- The quotient residual target is positive for a strict interior sample and positive epsilon.

The polynomial target is positive under these conditions, and the context's opposite majorant is strictly positive. -/
theorem quotientResidualTarget_pos
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    (squarefree : SquarefreeCertificate source)
    (state : WindingOneState source ambient)
    (sample : Canonical) (strict : state.box.StrictContains sample)
    {epsilon : Rational} (epsilonPositive : 0 < epsilon) :
    0 < context.quotientResidualTarget squarefree state sample epsilon := by
  exact Rat.Fraction.Order.Field.div_pos_direct
    (Residual.Chordal.Basic.residualTarget_pos squarefree state sample
      strict epsilonPositive)
    context.oppositeMajorant_pos

end

open Purelib.Data in
open Purelib.RationalFunctions in
/-- A quotient residual below the divided target stays below the target after multiplying by the positive majorant. -/
theorem quotientResidualSq_mul_majorant_lt
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {target : Rational} {sample : Canonical}
    (small : Residual.Basic.quotientResidualSq source opposite sample <
      target / context.oppositeMajorant) :
    Residual.Basic.quotientResidualSq source opposite sample * context.oppositeMajorant <
      target :=
  (Rat.Fraction.Order.Field.lt_div_iff_pos
    context.oppositeMajorant_pos).mp small

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- A sufficiently small protected quotient residual implies the corresponding polynomial residual threshold.

The state refines the protected box and contains the sample. Its source quadrance is bounded by quotient quadrance times
the retained opposite majorant. -/
theorem
  sourceResidual_lt_of_quotientResidual_lt
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {state : WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    (squarefree : SquarefreeCertificate source)
    (sample : Canonical) (inside : state.box.Contains sample)
    {epsilon : Rational}
    (small : Residual.Basic.quotientResidualSq source opposite sample <
      context.quotientResidualTarget squarefree state sample epsilon) :
    Gaussian.Norm.Basic.normSq (source.eval sample) <
      Residual.Chordal.Basic.residualTarget squarefree state sample
        epsilon := by
  let target := Residual.Chordal.Basic.residualTarget squarefree state
    sample epsilon
  have upper := context.sourceResidual_le_quotientResidualSq_mul_majorant
    refinesProtected inside
  have scaled : Residual.Basic.quotientResidualSq source opposite sample *
      context.oppositeMajorant < target := by
    apply context.quotientResidualSq_mul_majorant_lt
    simpa only [target, quotientResidualTarget] using small
  calc
    Gaussian.Norm.Basic.normSq (source.eval sample) ≤
        Residual.Basic.quotientResidualSq source opposite sample * context.oppositeMajorant :=
      upper
    _ < target := scaled
end LocalQuotientContext

end Purelib.RationalFunctions.Residual.Local.Basic

end
