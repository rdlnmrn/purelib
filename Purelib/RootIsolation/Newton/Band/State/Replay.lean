module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.Newton.Band.Build
public import Purelib.RootIsolation.Newton.Band.State
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Newton.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Raw

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Complete the original Newton-band and winding-state constructors around
a restored exact local extraction. No different cut or track is selected. -/
namespace Purelib.RootIsolation.Newton.Band.State.Replay
variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.WindingOne.Basic.WindingOneState p ambient) (epsilon : Fraction.Rational) (positive : 0 < epsilon)

/-- A retained band equal to the original extraction produces exactly the original winding-one refinement state. -/
theorem state_eq (band : Newton.Band.Basic.Output squarefree
  current.raw epsilon)
    (same : band = Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current.raw positive) :
    Newton.Band.State.state squarefree current epsilon band = Track.Newton.Refinement.refineState degreeAtLeastTwo
      squarefree
      elimination current epsilon positive := by
  cases same
  rfl

end Purelib.RootIsolation.Newton.Band.State.Replay

end
