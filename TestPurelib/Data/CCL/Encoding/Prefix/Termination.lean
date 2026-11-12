module

import Purelib.Data.CCL.Encoding.Prefix.Completion
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Cancellation
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.List.BinaryPrefix.Decision
import Purelib.Data.List.Range.Basic
import Purelib.Geometry.Projective.Line.Gaussian

/-!
# Automatic termination from every retained original phase

The fixtures keep the original rational input and each actually exposed raw
prefix. They call the automatic constructor on those returned cursors and
check exact word agreement, the one detection unit and projective readback.
Zero is an executable affine cursor with continuing finite unary requests;
the nonzero-numerator terminal constructor excludes it. Native infinity is
the homogeneous terminal tail, outside the affine cursor/fraction input type.
-/

namespace TestPurelib.Data.CCL.Encoding.Prefix.Termination

open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Geometry.Projective

/-- Check zero's native finite unary behavior and the separate projective-infinity domain. -/
private def checkNativeDomains : IO Unit := do
  for count in [1, 5, 17] do
    let result := Prefix.Cursor.zero.request Prefix.Cursor.zero_valid count
    have paid : result.suffix.length = count :=
      Prefix.Cursor.zero.request_zero_paid Prefix.Cursor.zero_valid rfl count
    let _ := paid
    unless result.suffix.length == count && decide (result.next.point = 0) &&
        result.suffix.head? == some false && (result.suffix.drop 1).all id do
      throw (IO.userError "raw zero changed its finite initial-low unary convention")
    match result.next.nextBit result.valid with
    | .advanced _ => pure ()
    | .terminal _ => throw (IO.userError "raw zero was incorrectly given an affine terminal")
  let fraction := GaussianInt.Fraction.ofGaussian 0
  unless decide (fraction.numerator = 0) && decide (fraction.denominator ≠ 0) do
    throw (IO.userError "zero's original fraction domain was changed to manufacture a nonzero numerator")
  let infinity : Line.GaussianLine := Line.Proj.omega
  unless decide (infinity.p = 1) && decide (infinity.q = 0) &&
      decide (¬ infinity.Equivalent (Line.Proj.affine (0 : Basic.Canonical))) do
    throw (IO.userError "native projective infinity was identified with an affine zero input")

/-- Check automatic completion from every actual prefix of a displayed nonzero rational point. -/
private def check (point : Basic.Canonical) (inside : (Box.symmetric 4 (by decide)).Contains point)
    (nonzero : point ≠ 0) : IO Unit := do
  let fraction := GaussianInt.Fraction.ofGaussian point
  have numeratorNonzero := GaussianInt.Fraction.ofGaussian_numerator_ne_zero nonzero
  have fractionValue := GaussianInt.Fraction.ofGaussian_value point
  let full := Encoder.Integral.encodeResult fraction numeratorNonzero
  let enclosure := Prefix.Enclosure.ofBox (Box.symmetric 4 (by decide)) ⟨by decide, by decide⟩
  let original := Prefix.Cursor.ofEnclosure enclosure point inside
  have originalPoint := Prefix.Cursor.ofEnclosure_point enclosure point inside
  for count in List.range (full.word.length + 1) do
    let earlier := original.val.request original.property count
    let finished := earlier.next.finishEncoding earlier.valid fraction numeratorNonzero
      (fractionValue.trans (originalPoint.symm.trans earlier.pointEq.symm))
    unless decide (finished.completion.word = full.word) &&
        List.BinaryPrefix.Decision.isWordPrefix earlier.next.word finished.completion.word &&
        finished.request.suffix.length + 1 == finished.bound &&
        finished.bound == full.word.length - earlier.next.word.length do
      throw (IO.userError "automatic completion changed the original word or exact detection budget")
    unless decide (Line.Gaussian.Proj.affineReading
        (Line.Matrix.act finished.completion.state.matrix Line.Proj.omega) = point) &&
        decide ((Line.Matrix.act finished.completion.state.matrix Line.Proj.omega).q ≠ 0) do
      throw (IO.userError "automatic completion lost its original projective readback")
    match finished.request.next.nextBit finished.request.valid with
    | .advanced _ => throw (IO.userError "computed completion budget failed to reach the actual terminal")
    | .terminal _ => pure ()
    let beforeDetection := earlier.next.request earlier.valid (finished.bound - 1)
    unless decide (beforeDetection.next.word = finished.request.next.word) do
      throw (IO.userError "the budget preceding detection did not expose the exact affine terminal precursor")
    let extraDetection := earlier.next.request earlier.valid (finished.bound + 1)
    unless decide (extraDetection.next.word = finished.request.next.word) do
      throw (IO.userError "an additional detection request changed the canonical terminal precursor")
  for factor in ([⟨⟨2, 0⟩, by decide⟩, ⟨⟨1000000, 0⟩, by decide⟩] :
      List {value : GaussianInt // value ≠ 0}) do
    let scaled : GaussianInt.Fraction :=
      ⟨fraction.numerator * factor.val, fraction.denominator * factor.val,
        GaussianInt.mul_ne_zero fraction.denominatorNonzero factor.property⟩
    have scaledNonzero : scaled.numerator ≠ 0 := GaussianInt.mul_ne_zero numeratorNonzero factor.property
    have sameValue : scaled.value = fraction.value := by
      apply GaussianInt.Fraction.value_eq_of_mul_den
      change fraction.value * GaussianInt.toGaussian (fraction.denominator * factor.val) =
        GaussianInt.toGaussian (fraction.numerator * factor.val)
      rewrite [GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul,
        ← Basic.mul_assoc, fraction.value_mul_denominator]
      rfl
    let scaledFull := Encoder.Integral.encodeResult scaled scaledNonzero
    have sameWord := Encoder.Integral.encode_word_eq_of_value_eq fraction scaled numeratorNonzero
      scaledNonzero sameValue.symm
    unless decide (full.word = scaledFull.word) do
      throw (IO.userError "an unreduced equivalent integral presentation changed the canonical complete word")
    have checked : full.word = scaledFull.word := sameWord
    let _ := checked

/-- Check every actual partial phase and large unreduced presentations of the same original rational readings.

The multiplier one million makes denominator norms far larger than the
canonical words. Direct denominator descent must preserve those exact words
without walking the discarded norm budget or reducing the displayed input.
-/
public def run : IO Unit := do
  checkNativeDomains
  check (⟨13 / 5, 0⟩ : Basic.Canonical) ⟨by decide, by decide, by decide, by decide⟩ (by decide)
  check (⟨3 / 5, 4 / 5⟩ : Basic.Canonical) ⟨by decide, by decide, by decide, by decide⟩ (by decide)
  check (⟨1 / 16, 0⟩ : Basic.Canonical) ⟨by decide, by decide, by decide, by decide⟩ (by decide)
  IO.print "canonical termination: every actual partial phase, exact detection budgets \
    and fraction presentations agree\n"

end TestPurelib.Data.CCL.Encoding.Prefix.Termination
