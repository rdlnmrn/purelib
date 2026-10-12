module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.CCL.Sample.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

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

namespace Purelib.RootIsolation.Track.CCL.Sample.Basic
namespace Request

/-- Every explicitly supplied point in the returned root box is within its
squared diagonal of the encoded rational sample. -/
theorem boxError
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive)
    {point : Gaussian.Basic.Canonical} (inside : result.next.box.Contains point) :
    Data.Gaussian.Norm.Basic.normSq
        (point - result.sample.point) ≤ result.next.box.diagonalSq :=
  Box.normSq_sub_le_diagonalSq
    inside result.sample.inside

/-- The numerical part of a coupled request meets the requested error. -/
theorem boxError_le_requested
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive)
    {point : Gaussian.Basic.Canonical} (inside : result.next.box.Contains point) :
    Data.Gaussian.Norm.Basic.normSq
        (point - result.sample.point) ≤ epsilon ^ 2 :=
  (result.boxError inside).trans result.accurate

/-- Any second finite realization of the same completed block list lies in
the explicit shrinking projective cylinder around this request. -/
theorem cylinderBound
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive)
    {other : Geometry.Projective.Line.GaussianLine}
    (otherRealizes : Data.CCL.Encoding.Cylinder.Projective.ProjectiveRealizes result.encoding.blocks other) :
    Geometry.Projective.Chordal.Basic.chordalSq result.encoding.point other ≤
      (1 / 2 : Fraction.Rational) ^ result.encoding.blocks.length :=
  Data.CCL.Encoding.Cylinder.Projective.ProjectiveRealizes.chordalSq_le_half_pow
    result.encoding.realizes otherRealizes

/-- Consecutive CCL requests move their displayed rational samples by at
most the squared diagonal of the earlier returned box. -/
theorem nextSampleMovement
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive)
    {nextEpsilon : Fraction.Rational} {nextPositive : 0 < nextEpsilon}
    (later : Track.CCL.Sample.Basic.Request track result.next nextEpsilon nextPositive) :
    Data.Gaussian.Norm.Basic.normSq
        (later.sample.point - result.sample.point) ≤
      result.next.box.diagonalSq :=
  Box.normSq_sub_le_diagonalSq
    (later.nested.contains later.sample.inside) result.sample.inside

/-- Consecutive returned samples therefore move by at most the earlier
request's squared accuracy target. -/
theorem nextSampleMovement_le_requested
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive)
    {nextEpsilon : Fraction.Rational} {nextPositive : 0 < nextEpsilon}
    (later : Track.CCL.Sample.Basic.Request track result.next nextEpsilon nextPositive) :
    Data.Gaussian.Norm.Basic.normSq
        (later.sample.point - result.sample.point) ≤ epsilon ^ 2 :=
  (result.nextSampleMovement later).trans result.accurate

end Request
end Purelib.RootIsolation.Track.CCL.Sample.Basic

end
