module
import Purelib.Data.CCL.Encoding.Encoder.Blocks
public import Purelib.Data.CCL.Encoding.Encoder.Cylinder
import Purelib.Data.CCL.Encoding.Encoder.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.CCL.Sample.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample

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

namespace Purelib.RootIsolation.Track.CCL.Sample.Build

/-- Execute a coupled request using only the supplied track's finite
refinement program and the choice-free canonical fraction representative. -/
def request
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Track.CCL.Sample.Basic.Request track current epsilon positive := by
  let next := track.refine current epsilon positive
  let sample := next.box.nonzeroSample next.proper
  let fraction := GaussianInt.Fraction.ofGaussian sample.point
  let numeratorNonzero :=
    GaussianInt.Fraction.ofGaussian_numerator_ne_zero sample.nonzero
  let encoding := Data.CCL.Encoding.Encoder.Blocks.encodeBlocks fraction
    numeratorNonzero
  let word := Data.CCL.Encoding.Encoder.Integral.encode fraction numeratorNonzero
  exact
    { next := next
      nested := track.nested current epsilon positive
      accurate := track.accurate current epsilon positive
      sample := sample
      fraction := fraction
      fractionValue := GaussianInt.Fraction.ofGaussian_value
        sample.point
      numeratorNonzero := numeratorNonzero
      encoding := encoding
      word := word
      word_eq := Data.CCL.Encoding.Encoder.Cylinder.encode_eq_rawWord fraction
        numeratorNonzero }

end Purelib.RootIsolation.Track.CCL.Sample.Build

end
