module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.List.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Certified finite box-refinement and CCL sample requests

The original polynomial track, current state and positive accuracy request index the retained next box, nonzero rational
sample, representing Gaussian-integer fraction, terminating encoding and exact cached raw word.
-/

public section

namespace Purelib.RootIsolation.Track.CCL.Sample.Basic

set_option genInjectivity false in
/-- One total finite box-refinement request together with the exact CCL code
of a displayed nonzero sample of the returned box.

The original polynomial track, current state and positive accuracy request index the retained next box, nonzero rational
sample, representing Gaussian-integer fraction, terminating encoding and exact cached raw word. -/
structure Request
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) where
  /-- The retained winding-one state returned by this finite refinement request. -/ next :
    State.WindingOne.Basic.WindingOneState p ambient
  /-- The returned box refines the original input box. -/ nested : next.box.Refines current.box
  /-- The returned box meets the original squared-diagonal accuracy request. -/ accurate : next.box.diagonalSq ≤ epsilon
    ^ 2
  /-- The exact nonzero rational sample retained inside the returned box. -/ sample : Box.NonzeroSample
    next.box
  /-- The retained Gaussian-integer fraction representing the same sample. -/ fraction : GaussianInt.Fraction
  /-- The retained fraction evaluates to the exact sampled point. -/ fractionValue : fraction.value = sample.point
  /-- The retained fraction's numerator is nonzero. -/ numeratorNonzero : fraction.numerator ≠ 0
  /-- The exact terminating block encoding of the retained fraction. -/ encoding :
    Data.CCL.Encoding.Encoder.Blocks.BlockEncoding fraction
  /-- The cached raw CCL word of the sampled point. -/ word : List.Basic.BinaryWord
  /-- The cached word equals the raw word of the retained block encoding. -/ word_eq : word =
    Data.CCL.Encoding.Block.Basic.rawWord encoding.blocks

constructive_injectivity Request

end Purelib.RootIsolation.Track.CCL.Sample.Basic

end
