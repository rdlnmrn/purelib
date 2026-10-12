module
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Band.Build
public import Purelib.RootIsolation.Newton.Search.Attempt
import Purelib.RootIsolation.Newton.Search.Center.Basic
import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Checked shortcuts for winding-one refinement

Newton iteration supplies candidates, not a convergence assumption.  A
candidate is accepted only after exact finite checks of strict containment,
the requested diagonal bound and winding four.  Eliminant-safe sides supply
the same ambient and boundary clearances as the total extractor.  A bounded
unsuccessful search delegates to the original total track.
-/

namespace Purelib.RootIsolation.Newton.Search.Extraction

attribute [local irreducible] Newton.Search.Center.Basic.checkCenter Grid.Box.roundedCenter
  Gaussian.Basic.value Dense.Gaussian.Derivative.Evaluation.derivativeEval
  Dense.Gaussian.Newton.Basic.newtonCenter
attribute [local irreducible] Newton.Search.Iteration.search

/-- Supply a globally line-cleared state from a raw winding box.  In
particular, a freshly Rouché-transported box need not undergo the old
extractor merely to become eligible for checked Newton proposals. -/
def extract {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient)
    {epsilon : Fraction.Rational} (positive : 0 < epsilon)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination := .canonical elimination) :
    Refinement current epsilon :=
  match Newton.Search.Attempt.attempt elimination current epsilon clearances with
  | some accepted => accepted
  | none =>
      let output := Newton.Band.Build.extract degreeAtLeastTwo squarefree
        elimination current positive
      { state :=
          { box := output.box
            refinesAmbient := output.refinesAmbient
            proper := output.proper
            clearance := output.clearance
            rawWindingFour := output.rawWindingFour
            ambientLeftClearance := output.ambientLeftClearance
            ambientRightClearance := output.ambientRightClearance
            ambientBottomClearance := output.ambientBottomClearance
            ambientTopClearance := output.ambientTopClearance }
        strict := output.strictCurrent
        accurate := output.diagonalSq_le }
end Purelib.RootIsolation.Newton.Search.Extraction

end
