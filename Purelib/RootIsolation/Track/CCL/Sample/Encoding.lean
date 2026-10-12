module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Transducer
import Purelib.Data.List.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.CCL.Sample.Basic
import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.Prefix.Cursor
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib

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

/-- Coherent incremental cursor through this request's exact finite sample
encoding. -/
def transducer
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive) :
    Data.CCL.Encoding.Transducer.EncodingTransducer result.fraction :=
  Data.CCL.Encoding.Transducer.EncodingTransducer.initial result.encoding

/-- The retained transducer's complete block word equals the original request's cached raw word. -/
theorem transducer_completeWord
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive) :
    Data.CCL.Encoding.Block.Basic.rawWord result.transducer.encoding.blocks = result.word :=
  result.word_eq.symm

/-- Every finite transducer advance extends the original emitted prefix. -/
theorem transducer_advance_extends
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive) (count : Nat) :
    ∃ extension : Data.List.Basic.BinaryWord,
      (result.transducer.advance count).state.emitted =
        result.transducer.state.emitted ++ extension :=
  result.transducer.advance_extends count

/-- Advancing by the exact pending length reaches the terminal state of this finite sample encoding. -/
theorem transducer_reaches_terminal
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive) :
    (result.transducer.advance
      result.transducer.state.pending.length).IsTerminal :=
  result.transducer.advance_remaining_terminal

/-- The CCL homogeneous realization reconstructs the displayed box sample. -/
theorem reconstructSample
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive) :
    result.encoding.point.Equivalent
      (Geometry.Projective.Line.Proj.affine result.sample.point) := by
  rw [← result.fractionValue]
  exact result.encoding.reconstruct
end Request
end Purelib.RootIsolation.Track.CCL.Sample.Basic

end
