module

public import Purelib.RootIsolation.Newton.Band.Prepare
import Purelib.RootIsolation.Newton.Extraction.Source
import Purelib.RootIsolation.Newton.Extraction.Geometry

public section

namespace Purelib.RootIsolation.Newton.Band.Build

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-- Run original source refinement and consume its retained radius and Newton point for the same canonical band.

The original safe-coordinate scans and eight full-line certificates remain
unchanged. Direct extraction geometry avoids constructing the unused Newton
square and its clearance before selecting the original band.
-/
@[expose] def extract
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) : Basic.Output squarefree current epsilon :=
  let source := Extraction.Source.selectSource squarefree elimination current epsilonPositive
  let geometry := Extraction.Geometry.fromSource degreeAtLeastTwo squarefree current epsilonPositive source
  Prepare.fromGeometry degreeAtLeastTwo squarefree elimination current geometry

end Purelib.RootIsolation.Newton.Band.Build
