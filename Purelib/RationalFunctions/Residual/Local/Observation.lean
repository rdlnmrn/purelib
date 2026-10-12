module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RationalFunctions.Residual.Basic
import Purelib.RationalFunctions.Residual.Local.Basic
import Purelib.RootIsolation.Residual.Chordal.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RationalFunctions.Residual.Local.Prepare
public import Purelib.RationalFunctions.Residual.Local.Target

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

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Turn a small protected quotient residual into a polynomial residual observation.

The displayed sample lies strictly inside a refining source state, and its quotient residual is below the context's
positive-epsilon target. The result retains either an exact source zero or a nearby winding-one box with the polynomial
chordal bound. -/
def observeOfSmallQuotientResidual
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate source)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate source
      degreeBound)
    (state : State.WindingOne.Basic.WindingOneState source ambient)
    (refinesProtected : state.box.Refines context.protectedState.box)
    (sample : Gaussian.Basic.Canonical) (strict : state.box.StrictContains sample)
    {epsilon : Rat.Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (small : Residual.Basic.quotientResidualSq source opposite sample <
      context.quotientResidualTarget squarefree state sample epsilon) :
    Residual.Chordal.Basic.ResidualChordalObservation
      squarefree elimination state sample epsilon :=
  Residual.Chordal.Basic.observeOfResidual degreeAtLeastTwo
    squarefree elimination state sample strict epsilonPositive
      (context.sourceResidual_lt_of_quotientResidual_lt refinesProtected
        squarefree sample strict.contains small)
end LocalQuotientContext

end Purelib.RationalFunctions.Residual.Local.Basic

end
