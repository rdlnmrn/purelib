module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Geometry.Rational.Box.Sample.Five
public import Purelib.RootIsolation.Newton.Extraction.Initial.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Checked initial root extraction

The initial positive-winding region can contain several roots.  In particular,
its midpoint may be a critical point even when the polynomial is squarefree.
Try its midpoint and four off-centre seeds before using the total extractor.
These seeds are only proposals: the existing finite checker proves strict
containment, winding four, full-line clearance and the requested accuracy.

No Newton-convergence hypothesis or caller search budget is needed.  Failure
of the bounded shortcut retains the original unconditional finite fallback.
The selected root is whichever checked seed succeeds first; no equality with
the old extractor's ordering of independent roots is asserted.
-/

namespace Purelib.RootIsolation.Newton.Extraction.Initial.Build

/-- Total initial extraction with checked speculative acceleration.  All
obligations are carried by the returned finite data, including in the
fallback branch; speculation is not an additional trust boundary. -/
def extract {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient)
    {epsilon : Fraction.Rational} (positive : 0 < epsilon) :
    Refinement current epsilon :=
  match Newton.Extraction.Initial.Search.search elimination current epsilon (Box.Sample.Five.seeds current.box) with
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

end Purelib.RootIsolation.Newton.Extraction.Initial.Build

end
