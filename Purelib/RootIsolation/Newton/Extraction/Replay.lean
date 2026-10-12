module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Extraction.Build
public import Purelib.RootIsolation.Newton.Extraction.Prepare
import Purelib.RootIsolation.Newton.Extraction.Source
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Newton.Extraction.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Restore the original Newton source selection from checked safe-subdivision
stages, then reuse that source in the unchanged local extraction construction.
The source ownership equation is exact, including its boundary bound. -/
namespace Purelib.RootIsolation.Newton.Extraction.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)

/-- Exact identity of every executable field of the local Newton output. -/
theorem fromSource_eq {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational} (positive : 0 < epsilon)
    (saved : Newton.Extraction.Source.SourceOutput squarefree current epsilon)
    (same : saved = Newton.Extraction.Source.selectSource squarefree elimination current positive) :
    Newton.Extraction.Prepare.fromSource degreeAtLeastTwo squarefree current positive saved =
      Newton.Extraction.Build.extract degreeAtLeastTwo squarefree elimination current positive := by
  cases same
  unfold Newton.Extraction.Prepare.fromSource Newton.Extraction.Build.extract
  rfl

end Purelib.RootIsolation.Newton.Extraction.Replay

end
