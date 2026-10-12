module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Newton.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free shrinking winding-one tracks

The local Newton-square extractor is stable under iteration because every
returned square carries a new finite boundary-clearance certificate.  This
module packages those repeated finite calls as the numerical track interface
used by box isolation and any independently shrinking finite envelope.
-/

namespace Purelib.RootIsolation.Track.Newton.Build

/-- Concrete total track generated from one winding-one state. -/
def ofInitial
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (initial : State.WindingOne.Basic.WindingOneState p ambient) : Track.Basic.WindingOneTrack p ambient where
  initial := initial
  refine := Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination
  nested := Track.Newton.Refinement.refineState_refines degreeAtLeastTwo squarefree elimination
  strict := Track.Newton.Refinement.refineState_strict degreeAtLeastTwo squarefree elimination
  accurate := Track.Newton.Refinement.refineState_accurate degreeAtLeastTwo squarefree elimination

end Purelib.RootIsolation.Track.Newton.Build

end
