module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Representation.Sequence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic
public import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Realizer
import Purelib.Approximation.Gaussian.Translation.Observation
import Purelib.Approximation.Gaussian.Translation.Realizer
import Purelib.Approximation.Gaussian.Translation.Request
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Representation

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Gaussian.Translation

open Purelib.Approximation.Gaussian.Translation.CCL

open Purelib.Approximation.Gaussian.Translation.CCL.Cursor

open Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Finite translations through a progressive CCL cursor

A finite CCL observation contains two synchronized interfaces to one named
program: a persistent raw prefix of an explicitly requested length and a
finite rational sample/error observation.  The prefix has exact projective
machine semantics; the sidecar supplies the rational precision gauge used for
cross-representation comparison.
-/

namespace Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip

/-- The name-level round trip is the repository's operational equivalence, not equality of the two finite sample
programs. -/
def approximationCursorRoundTrip
    (approximation : ApproximationData) :
    Gaussian.Equivalence.Equivalent
      (CursorObservation.approximation approximation.toNamed)
      approximation :=
  Equivalent.toNamed_sampling approximation

set_option genInjectivity false in
/-- The complete certified relationship between one random-access finite approximation and its productive CCL name. The
forward realizer, lossless cursor-forgetting map, operational round trip, per-request certificate, and cross-request
prefix persistence are packaged as one reusable object. -/
structure CertifiedApproximationCursorRoundTrip
    (approximation : ApproximationData) where
  /-- The certified finite translation from approximation observations to cursor observations. -/ forward :
    Approximation.Gaussian.Translation.Realizer (Sequence.approximationRepresentation approximation)
    (Cursor.Basic.cursorRepresentation approximation.toNamed)
  /-- The lossless observation map that forgets the raw-prefix counter. -/ backward : Observation.ObservationMap
    (Cursor.Basic.cursorRepresentation approximation.toNamed)
    (Sequence.approximationRepresentation
      (CursorObservation.approximation approximation.toNamed))
  /-- Finite sampled observations of the constructed name are operationally equivalent to the original approximation. -/
    operational : Gaussian.Equivalence.Equivalent
    (CursorObservation.approximation approximation.toNamed) approximation
  /-- Every original request retains the exact bit count, parser semantics, strict precision bound and measured cost. -/
    request_certified : ∀ (index : Nat) (request : Approximation.Gaussian.Translation.Request),
    let result := forward.translate index request
    result.output.word.length = result.output.bitCount ∧
      Semantics.Basic.ExactCursor
        approximation.toNamed.process approximation.toNamed.state
        (Advance.advance approximation.toNamed.machine
          result.output.bitCount) ∧
      (Cursor.Basic.cursorRepresentation approximation.toNamed).precisionSq result.output <
        request.targetSq ∧
      result.schedule.work ≤ result.costBound ∧
      result.costBound = 2 * (result.output.sampleIndex + 1) + 2
  /-- Any two request outputs are ordered by refinement and retain the corresponding raw-prefix extension. -/
    outputs_persistent : ∀ (leftIndex rightIndex : Nat)
      (leftRequest rightRequest : Approximation.Gaussian.Translation.Request),
    let left := forward.translate leftIndex leftRequest
    let right := forward.translate rightIndex rightRequest
    ((Cursor.Basic.cursorRepresentation approximation.toNamed).Refines
          right.output left.output ∧
        left.output.word.IsPrefix right.output.word) ∨
      ((Cursor.Basic.cursorRepresentation approximation.toNamed).Refines
          left.output right.output ∧
        right.output.word.IsPrefix left.output.word)

constructive_injectivity
  CertifiedApproximationCursorRoundTrip

/-- Canonical bundled round trip for every executable finite approximation. -/
def certifiedApproximationCursorRoundTrip
    (approximation : ApproximationData) :
    CertifiedApproximationCursorRoundTrip approximation where
  forward := Realizer.approximationToCursor approximation
  backward := Cursor.Basic.cursorToApproximation approximation.toNamed
  operational := approximationCursorRoundTrip approximation
  request_certified := Realizer.approximationToCursorAt_certified approximation
  outputs_persistent := Realizer.approximationToCursorAt_persistent approximation

end Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip

end
