module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Bound.Process
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Weighted.Enclosure.Process
public import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Classified.Threshold
public import Purelib.Measure.Distribution.Enclosure.Threshold
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Classified.Soundness
import Purelib.Measure.Classified.Split
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Threshold events from finite rational enclosures

Pointwise rational enclosures can decide some threshold comparisons and leave
the rest explicitly unresolved.  The resulting lower and upper probability
sums contain the exact threshold probability of every rational observable
admitted by the displayed enclosures.  Refining the enclosures narrows the
probability bound.
-/

namespace Purelib.Measure
namespace PointwiseEnclosureProcess

open Purelib
open Purelib.Data.Rat
/-- Retain the enclosure process as a threshold classification process with the supplied unresolved-probability accuracy
certificate.

The exact states, requests and initial state are unchanged; every state's original ranges admit the same retained
observable. -/
def toThresholdClassificationProcess {α : Type}
    {distribution : Distribution α}
    (process : Measure.PointwiseEnclosureProcess distribution)
    (threshold : Fraction.Rational) (value : α → Fraction.Rational)
    (admitted : ∀ state atom, atom ∈ distribution.atoms →
      (process.ranges state atom.item).Contains (value atom.item))
    (unresolvedAccurate : ∀ state epsilon positive,
      distribution.probability
        (unresolvedStatusEvent fun item =>
          thresholdStatus
            (process.ranges (process.request state epsilon positive) item)
            threshold) < epsilon) :
    Measure.ClassificationProcess distribution (atLeastEvent threshold value) where
  State := process.State
  status state item := thresholdStatus (process.ranges state item) threshold
  initial := process.initial
  request := process.request
  sound state := distribution.thresholdClassification_sound
    (process.ranges state) threshold value (admitted state)
  request_refines state epsilon positive atom member :=
    thresholdStatus_refines
      (process.request_refines state epsilon positive atom member)
  accurate := unresolvedAccurate
  refinesInitial state atom member :=
    thresholdStatus_refines (process.refinesInitial state atom member)

/-- Read the original enclosure states as threshold probability bounds when every request resolves all retained atom
ranges.

The original requests are reused directly, and their complete threshold-resolution certificate gives zero-width
resulting event bounds. -/
def toThresholdBoundProcess {α : Type}
    {distribution : Distribution α}
    (process : Measure.PointwiseEnclosureProcess distribution)
    (threshold : Fraction.Rational)
    (requestResolved : ∀ state epsilon positive atom,
      atom ∈ distribution.atoms →
        ThresholdResolved
          (process.ranges (process.request state epsilon positive) atom.item)
          threshold) : Approximation.BoundProcess where
  State := process.State
  bound state := eventBound
    (distribution.thresholdFrontier (process.ranges state) threshold)
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    distribution.thresholdFrontier_eventBound_refines
      (process.ranges (process.request state epsilon positive))
      (process.ranges state) threshold
      (process.request_refines state epsilon positive)
  accurate state epsilon positive := by
    rw [distribution.thresholdFrontier_width_eq_zero_of_resolved]
    · exact positive
    · exact requestResolved state epsilon positive
  refinesInitial state :=
    distribution.thresholdFrontier_eventBound_refines
      (process.ranges state) (process.ranges process.initial) threshold
      (process.refinesInitial state)

/-- The exact threshold-process bound contains the original event probability of any observable admitted by that state's
retained ranges. -/
theorem probability_mem_thresholdBound {α : Type}
    {distribution : Distribution α}
    (process : Measure.PointwiseEnclosureProcess distribution)
    (threshold : Fraction.Rational)
    (requestResolved : ∀ state epsilon positive atom,
      atom ∈ distribution.atoms →
        ThresholdResolved
          (process.ranges (process.request state epsilon positive) atom.item)
          threshold)
    (state : process.State) (value : α → Fraction.Rational)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (process.ranges state atom.item).Contains (value atom.item)) :
    ((process.toThresholdBoundProcess threshold requestResolved).bound state).Contains
      (distribution.probability (atLeastEvent threshold value)) :=
  distribution.probability_mem_thresholdFrontier
    (process.ranges state) threshold value inside

end PointwiseEnclosureProcess

end Purelib.Measure

end
