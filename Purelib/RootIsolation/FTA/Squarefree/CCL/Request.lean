module
public import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Track.CCL.Sample.Residual
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.CCL.Sample.Basic
public import Purelib.RootIsolation.Track.CCL.Sample.Build
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.FTA.Squarefree (AdapterResult)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.FTA.Squarefree.AdapterResult
section Result

/-- Run a finite box/CCL request from any current state of one output track. -/
def requestAt
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree)
    (current : State.WindingOne.Basic.WindingOneState p
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Track.CCL.Sample.Basic.Request (result.trackAt index) current epsilon positive :=
  Track.CCL.Sample.Build.request (result.trackAt index) current epsilon positive

/-- First coupled request on a selected degree-indexed output track. -/
def initialRequestAt
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Track.CCL.Sample.Basic.Request (result.trackAt index) (result.trackAt index).initial
      epsilon positive :=
  result.requestAt index (result.trackAt index).initial epsilon positive

/-- Public degree-indexed residual bound, with degree positivity recovered
constructively from the displayed finite index. -/
theorem requestAt_sampleResidual
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree)
    (current : State.WindingOne.Basic.WindingOneState p
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (result.requestAt index current epsilon positive).sample.point) ≤
      Dense.Gaussian.Bounds.Box.residualConstant p
          (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) *
        (result.requestAt index current epsilon positive).next.box.diagonalSq :=
  (result.requestAt index current epsilon positive).sampleResidual
    (Nat.zero_lt_of_lt index.isLt)

end Result
end Purelib.RootIsolation.FTA.Squarefree.AdapterResult

end
