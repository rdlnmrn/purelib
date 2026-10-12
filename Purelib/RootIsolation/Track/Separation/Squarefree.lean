module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Uniqueness
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Separation.Separated
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Squarefree specialization of track separation

The original squarefree Bezout certificate supplies the derivative
separation used by the same finite residual and common-box comparison.
-/

namespace Purelib.RootIsolation.Track.Separation.Squarefree

/-- Separated squarefree winding-one states cannot share a sufficiently small box.

The original squarefree Bezout certificate provides derivative separation on
the same ambient box. The retained states, tracks and common-box refinements
then satisfy the direct uniqueness comparison. -/
public theorem separated_tracks_not_supported_in_small_common_box
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (leftTrack rightTrack : Basic.WindingOneTrack p ambient)
    (leftState rightState : State.WindingOne.Basic.WindingOneState p ambient)
    (separated : leftState.box.Separated rightState.box)
    (common : Box)
    (leftCommon : leftState.box.Refines common)
    (rightCommon : rightState.box.Refines common)
    (small : common.diagonalSq <
      Dense.Gaussian.Derivative.Separation.Uniqueness.uniquenessDiagonalThreshold squarefree ambient) : False :=
  Track.Separation.Separated.separated_tracks_not_supported_in_small_common_box_of_separation
    degreePositive
    (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient)
    leftTrack rightTrack leftState rightState separated common leftCommon
    rightCommon small

end Purelib.RootIsolation.Track.Separation.Squarefree
