module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.FTA.Squarefree.Basic
public import Purelib.RootIsolation.FTA.Squarefree.CCL.Request
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.RootIsolation.Track.CCL.Sample.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.FTA.Squarefree

set_option genInjectivity false in
/-- Two first requests on distinct tracks, retaining the finite positive
box-separation certificate and the resulting distinct encoded samples. -/
structure CCL.Pair.PairRequest
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      FTA.Squarefree.AdapterResult p)
    (left right : Fin p.natDegree) (different : left ≠ right)
    (leftEpsilon rightEpsilon : Fraction.Rational)
    (leftPositive : 0 < leftEpsilon)
    (rightPositive : 0 < rightEpsilon) where
  /-- The actual first request on the original left degree-indexed track. -/ leftRequest :
    Track.CCL.Sample.Basic.Request (result.trackAt left)
    (result.trackAt left).initial leftEpsilon leftPositive
  /-- The actual first request on the original right degree-indexed track. -/ rightRequest :
    Track.CCL.Sample.Basic.Request (result.trackAt right)
    (result.trackAt right).initial rightEpsilon rightPositive
  /-- The two retained requested boxes are positively separated. -/ boxesSeparated : leftRequest.next.box.Separated
    rightRequest.next.box
  /-- The actual encoded sample points in the two retained boxes are distinct. -/ samplesDifferent :
    leftRequest.sample.point ≠ rightRequest.sample.point

constructive_injectivity CCL.Pair.PairRequest

/-- Independently refine and encode two distinct degree-indexed tracks. -/
@[expose] def AdapterResult.requestPairAt
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      FTA.Squarefree.AdapterResult p)
    (left right : Fin p.natDegree) (different : left ≠ right)
    (leftEpsilon rightEpsilon : Fraction.Rational)
    (leftPositive : 0 < leftEpsilon)
    (rightPositive : 0 < rightEpsilon) :
    CCL.Pair.PairRequest result left right different leftEpsilon rightEpsilon
      leftPositive rightPositive := by
  let leftRequest := result.initialRequestAt left leftEpsilon leftPositive
  let rightRequest := result.initialRequestAt right rightEpsilon rightPositive
  have boxesSeparated : leftRequest.next.box.Separated
      rightRequest.next.box :=
    Box.Separated.of_refines
      (result.trackAt_pairwiseSeparated left right different)
      leftRequest.nested rightRequest.nested
  exact
    { leftRequest := leftRequest
      rightRequest := rightRequest
      boxesSeparated := boxesSeparated
      samplesDifferent := boxesSeparated.points_ne
        leftRequest.sample.inside rightRequest.sample.inside }

end Purelib.RootIsolation.FTA.Squarefree

end
