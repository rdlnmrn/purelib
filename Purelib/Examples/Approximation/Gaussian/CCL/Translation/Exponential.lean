module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Translation.Request
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic
import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Realizer
public import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Examples.Approximation.Gaussian.Exponential.Progressive.WorkedExamples
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Representation.Sequence
import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Translation.Realizer
import Purelib.Approximation.Gaussian.Name.Basic

@[expose] public section

/-!
# Worked finite-translation examples

These four examples exercise different parts of the protocol: algebraic
bisection, a Liouville-style nonalgebraic digit process, sequential raw CCL
output for a finite exponential program, and a redundant signed-digit
translation of that same non-rational process.
-/

namespace Purelib.Examples.Approximation.Gaussian.CCL.Translation.Exponential

open Purelib.Approximation.Gaussian.Translation (Request)
open Purelib.Examples.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Translation

open Purelib.Approximation.Gaussian
open Purelib.Data.Rat
open Purelib.Examples.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Approximation.Gaussian.Name

/-! ## 2. Liouville factorial-position digits to a rational ball -/

/-! ## A shared finite exponential process for Examples 3 and 4 -/

/-! ## 3. Finite exponential approximation to a persistent CCL prefix -/

/-- The positive exponential cursor-translation tolerance one sixty-fourth. -/
def request :
    Request :=
  ⟨1 / 64,
    Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct
        (by decide : 0 < (64 : Nat)))⟩

/-- Translate the retained exponential approximation to a CCL cursor at stage zero.

Keeps the original output word, sampling index and certified translation cost for the fixed positive request. -/
def result :=
  CCL.Cursor.Realizer.approximationToCursorAt
    Progressive.WorkedExamples.approximation 0 request

/-- The exponential cursor translation retains its exact word and cost schedule.

The word length equals the bit count, the bit count is one beyond the sample index, and the cost bound is twice that
count plus two. -/
theorem cursor_schedule :
    let translated := CCL.Cursor.Realizer.approximationToCursorAt
      Progressive.WorkedExamples.approximation 0 request
    translated.output.word.length = translated.output.bitCount ∧
      translated.output.bitCount = translated.output.sampleIndex + 1 ∧
      translated.costBound =
        2 * (translated.output.sampleIndex + 1) + 2 :=
  CCL.Cursor.Realizer.approximationToCursorAt_schedule
    Progressive.WorkedExamples.approximation 0 request

/-- The translated exponential word is certified by the original exact cursor.

Retains the actual machine advance at the emitted bit count and the source approximation's named process and state. -/
theorem exact_raw_prefix :
    result.output.word.length = result.output.bitCount ∧
      Machine.Semantics.Basic.ExactCursor
        (Sequence.ApproximationData.toNamed Progressive.WorkedExamples.approximation).process
        (Sequence.ApproximationData.toNamed Progressive.WorkedExamples.approximation).state
        (Machine.Advance.advance
          (Sequence.ApproximationData.toNamed Progressive.WorkedExamples.approximation).machine
          result.output.bitCount) :=
  CCL.Cursor.Realizer.approximationToCursor_word_certificate
    Progressive.WorkedExamples.approximation 0 request

/-- Sampling the translated exponential name agrees with its original approximation.

Uses the retained operational equivalence in the certified approximation-to-cursor round trip. -/
def operationalRoundTrip :
    Equivalence.Equivalent
      (Sampling.approximation
        (Sequence.ApproximationData.toNamed Progressive.WorkedExamples.approximation))
      Progressive.WorkedExamples.approximation :=
  (Translation.CCL.Cursor.RoundTrip.certifiedApproximationCursorRoundTrip
    Progressive.WorkedExamples.approximation).operational

/-- The complete certified cursor round trip for the exponential approximation. -/
def certifiedRoundTrip :
    Translation.CCL.Cursor.RoundTrip.CertifiedApproximationCursorRoundTrip
      Progressive.WorkedExamples.approximation :=
  Translation.CCL.Cursor.RoundTrip.certifiedApproximationCursorRoundTrip
    Progressive.WorkedExamples.approximation

/-- The positive exponential cursor-translation tolerance one two-hundred-fifty-sixth. -/
def finerRequest :
  Request :=
  ⟨1 / 256,
    Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct
        (by decide : 0 < (256 : Nat)))⟩

/-- The two requested exponential cursor outputs are comparable by refinement.

For stage zero and stage two with their original tolerances, one retained output refines the other and extends its exact
emitted word. -/
theorem translated_prefixes_persistent :
    let coarse := CCL.Cursor.Realizer.approximationToCursorAt
      Progressive.WorkedExamples.approximation 0 request
    let fine := CCL.Cursor.Realizer.approximationToCursorAt
      Progressive.WorkedExamples.approximation 2 finerRequest
    ((Translation.CCL.Cursor.Basic.cursorRepresentation
          (Sequence.ApproximationData.toNamed Progressive.WorkedExamples.approximation)).Refines
        fine.output coarse.output ∧
      coarse.output.word.IsPrefix fine.output.word) ∨
    ((Translation.CCL.Cursor.Basic.cursorRepresentation
          (Sequence.ApproximationData.toNamed Progressive.WorkedExamples.approximation)).Refines
        coarse.output fine.output ∧
      fine.output.word.IsPrefix coarse.output.word) :=
  certifiedRoundTrip.outputs_persistent 0 2 request
    finerRequest

/-! ## 4. The same finite exponential process in redundant signed digits -/

end Purelib.Examples.Approximation.Gaussian.CCL.Translation.Exponential

end
