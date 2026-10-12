module
import Purelib.Approximation.Gaussian.Representation.Ball
import Purelib.Data.SignedDigit.Binary.Encoding
import Purelib.Approximation.Gaussian.Translation.Request
import Purelib.Approximation.Gaussian.SignedDigit.Representation
public import Purelib.Approximation.Gaussian.SignedDigit.Translation
public import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.SignedDigit.Binary.Basic
public import Purelib.Examples.Approximation.Gaussian.Exponential.Progressive.WorkedExamples
import Purelib.Approximation.Gaussian.Translation.Realizer
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Translation.Observation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Representation.Sequence
import Purelib.Approximation.Gaussian.SignedDigit.Cell

@[expose] public section

/-!
# Worked finite-translation examples

These four examples exercise different parts of the protocol: algebraic
bisection, a Liouville-style nonalgebraic digit process, sequential raw CCL
output for a finite exponential program, and a redundant signed-digit
translation of that same non-rational process.
-/

namespace Purelib.Examples.Approximation.Gaussian.SignedDigit.Translation.Exponential

open Purelib.Examples.Approximation.Gaussian.Exponential

open Purelib.Approximation.Gaussian
open Purelib.Data.Rat
open Purelib.Examples.Approximation.Gaussian
open Purelib.Data.SignedDigit

/-! ## 2. Liouville factorial-position digits to a rational ball -/

/-! ## A shared finite exponential process for Examples 3 and 4 -/

/-! ## 3. Finite exponential approximation to a persistent CCL prefix -/

/-! ## 4. The same finite exponential process in redundant signed digits -/

/-- The positive exponential signed-digit translation tolerance one thirty-second. -/
def request :
  Approximation.Gaussian.Translation.Request :=
  ⟨1 / 32,
    Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct
        (by decide : 0 < (32 : Nat)))⟩

/-- The translated exponential keeps its exact digit lengths and work bound.

Both real and imaginary digit lists have the requested retained depth, and the cost bound is four times that depth plus
four. -/
theorem signed_digit_data :
    let translated :=
      SignedDigit.Translation.fromApproximationAt
        Progressive.WorkedExamples.approximation 0 request
    let depth := SignedDigit.Translation.requestDepth
      Progressive.WorkedExamples.approximation request
    translated.output.depth = depth ∧
      translated.output.realDigits.length = depth ∧
      translated.output.imagDigits.length = depth ∧
      translated.costBound = 4 * depth + 4 :=
  SignedDigit.Translation.fromApproximationAt_data
    Progressive.WorkedExamples.approximation 0 request

/-- The ball read from the original translated digits meets the squared-error target. -/
theorem translated_ball_precision :
    let translated :=
      SignedDigit.Translation.fromApproximationAt
        Progressive.WorkedExamples.approximation 0 request
    let ball := SignedDigit.Representation.toBall.map translated.output
    Representation.Ball.ballRepresentation.precisionSq ball <
      request.targetSq :=
  SignedDigit.Translation.fromApproximationAt_toBall_precision
    Progressive.WorkedExamples.approximation 0 request

/-- Two distinct signed-digit prefixes have the same retained rational center.

The positive-negative and zero-positive words remain syntactically different despite their equal prefix values. -/
theorem redundancy_is_observable :
    Binary.Basic.prefixValue
        [.positive, .negative] =
      Binary.Basic.prefixValue [.zero, .positive] ∧
    [.positive, .negative] ≠
      ([.zero, .positive] :
        List Binary.Basic.Digit) :=
  ⟨Binary.Encoding.nonunique_prefix_center,
    Binary.Encoding.nonunique_prefix_syntax⟩

end Purelib.Examples.Approximation.Gaussian.SignedDigit.Translation.Exponential

end
