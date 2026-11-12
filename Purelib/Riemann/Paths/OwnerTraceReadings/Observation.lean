module

public import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Comparison
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Actual coefficient observations across stationary owner joins

A literal retained OwnerJoin derives the signed agreement between its two
original root processes. Cached quadratic denotations transport their same
original expression through that agreement. The generic operational
comparison then pays both OLD observation radii and its actual tail target;
neither old reading is replaced by a newly selected witness.

A separate exact view reads a cached denotation at an already retained
OwnerTail.Reading. It preserves that reading and the original tail state,
and computes only the displayed coefficient-state radius. It acquires no
root reading, request or denotation.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTraceReadings

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Quadratic.Pair.Polynomial.Expression (Denotation)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)

namespace OwnerTail.Reading

variable {radicand : Coefficients} {expression : Expression radicand} {point : Canonical}
variable {owner : Owner (radicand.eval point)} {tail : OwnerTail owner}

/-- View the cached coefficient denotation at this exact old root reading and its original retained tail state.

The scalar coefficient pair, root witness and possible-state proof are
the original inputs. Only a possible-reading view and its exact visible
radius are cached; no producer or state refinement is run.
-/
@[expose] def denotationObservation
    (original : Denotation expression point (owner.certificate owner.parameterNonzero).value)
    (reading : OwnerTail.Reading tail) : Observation.Reading original.channel :=
  Observation.Reading.retain original.channel (original.readingState tail.state)
    (original.value.re + original.value.im * reading.value)
    (original.reading_possible tail.state reading.value reading.possible)

/-- The denotation view uses exactly the old retained root tail state under the original coefficient-state map. -/
theorem denotationObservation_state
    (original : Denotation expression point (owner.certificate owner.parameterNonzero).value)
    (reading : OwnerTail.Reading tail) :
    (denotationObservation original reading).state = original.readingState tail.state := rfl

/-- The denotation view retains the exact coefficient reading at the unchanged old root witness. -/
theorem denotationObservation_value
    (original : Denotation expression point (owner.certificate owner.parameterNonzero).value)
    (reading : OwnerTail.Reading tail) :
    (denotationObservation original reading).value = original.value.re + original.value.im * reading.value := rfl

/-- The denotation view pays the actual old root-state radius with the original cached coefficient factor. -/
theorem denotationObservation_radius
    (original : Denotation expression point (owner.certificate owner.parameterNonzero).value)
    (reading : OwnerTail.Reading tail) :
    (denotationObservation original reading).radius = 8 * Norm.Basic.normSq original.value.im *
      ((ownerName owner).process.ball tail.state).radiusSq :=
  original.reading_radius tail.state

end OwnerTail.Reading

namespace OwnerJoin

variable {radicand : Coefficients} {expression : Expression radicand} {point : Canonical}
variable {left right : Owner (radicand.eval point)}

/-- Compare two old possible coefficient readings using the literal retained join and one actual tail request.

The original generic Comparison retains both observation owners, old
states, values, radius caches, based views and selected tail samples. The
signed root relation is derived internally from the supplied join.
-/
def compareDenotations (join : OwnerJoin left right)
    (first : Denotation expression point (left.certificate left.parameterNonzero).value)
    (last : Denotation expression point (right.certificate right.parameterNonzero).value)
    (firstReading : Observation.Reading first.channel) (lastReading : Observation.Reading last.channel)
    (request : AccuracyRequest) : Observation.Comparison firstReading lastReading request.tolerance :=
  first.compare last join.equivalent firstReading lastReading request

/-- Compare the two unchanged readings selected by their original, possibly distinct coefficient requests. -/
def compareRequestedDenotations (join : OwnerJoin left right)
    (first : Denotation expression point (left.certificate left.parameterNonzero).value)
    (last : Denotation expression point (right.certificate right.parameterNonzero).value)
    {firstTarget lastTarget : Rational}
    (firstRequest : Observation.Request first.channel firstTarget)
    (lastRequest : Observation.Request last.channel lastTarget) (request : AccuracyRequest) :
    Observation.Comparison firstRequest.reading lastRequest.reading request.tolerance :=
  join.compareDenotations first last firstRequest.reading lastRequest.reading request

end OwnerJoin

end Purelib.Riemann.Paths.OwnerTraceReadings

end
