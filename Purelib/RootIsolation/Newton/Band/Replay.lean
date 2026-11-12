module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Band.Build
public import Purelib.RootIsolation.Newton.Band.Prepare
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Complete the original Newton-band and winding-state constructors around
a restored exact local extraction. No different cut or track is selected. -/
namespace Purelib.RootIsolation.Newton.Band.Replay

/-- Transporting only a retained elimination certificate's degree index preserves the complete original Newton band. -/
theorem extract_castDegree
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {left right : Nat}
    (same : left = right) (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p left)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational} (positive : 0 < epsilon) :
    Newton.Band.Build.extract degreeAtLeastTwo squarefree (elimination.castDegree same) current positive =
      Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current positive := by
  cases same
  rfl

/-- Exact original band readback from the same retained source's direct extraction geometry. -/
theorem fromSource_eq
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational} (positive : 0 < epsilon)
    (saved : Newton.Extraction.Source.SourceOutput squarefree current epsilon)
    (same : saved = Newton.Extraction.Source.selectSource squarefree elimination current positive) :
    Newton.Band.Prepare.fromGeometry degreeAtLeastTwo squarefree elimination current
      (Newton.Extraction.Geometry.fromSource degreeAtLeastTwo squarefree current positive saved) =
      Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current positive := by
  cases same
  rfl

/-- Reusing a retained core equal to the original Newton extraction produces exactly the original band output. -/
theorem fromCore_eq {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational} (positive : 0 < epsilon)
    (saved : Newton.Band.Prepare.Core degreeAtLeastTwo squarefree elimination current positive) :
    Newton.Band.Prepare.fromCore degreeAtLeastTwo squarefree elimination current positive saved =
      Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current positive := by
  rcases saved with ⟨core, same⟩
  cases same
  rfl

end Purelib.RootIsolation.Newton.Band.Replay

end
