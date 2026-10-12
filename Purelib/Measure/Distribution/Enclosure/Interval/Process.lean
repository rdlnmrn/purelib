module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Weighted.Enclosure.Process
import Purelib.Measure.Classified.Process
import Purelib.Measure.Classified.Interval
public import Purelib.Measure.Classified.FixedLawProcess
public import Purelib.Measure.Distribution.Enclosure.Interval
import Purelib.Measure.Content.Density.Aligned
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Classified.Soundness
import Purelib.Measure.Classified.Split
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic

section
@[expose] public section

/-!
# Finite probability of rational-interval membership

A rational enclosure for each displayed atom can certify that its value is
inside a target rational interval, outside it, or still unresolved.  The
resulting finite lower/upper sums enclose the exact probability for every
explicit rational observable admitted by those enclosures.  Narrower source
enclosures can only narrow the probability enclosure.
-/

namespace Purelib.Measure
namespace PointwiseEnclosureProcess

open Purelib in
open Purelib.Data.Rat in
/-- Read the exact enclosure process as an interval-membership classification process with the supplied
unresolved-probability guarantee.

The original states, requests and initial state are retained; soundness refers to the same observable and every original
atom's range at every state. -/
def toWithinBoundClassificationProcess {α : Type}
    {distribution : Distribution α}
    (process : PointwiseEnclosureProcess distribution)
    (target : Data.Rat.Interval) (value : α → Fraction.Rational)
    (admitted : ∀ state atom, atom ∈ distribution.atoms →
      (process.ranges state atom.item).Contains (value atom.item))
    (unresolvedAccurate : ∀ state epsilon positive,
      distribution.probability
        (withinBoundUnresolvedEvent
          (process.ranges (process.request state epsilon positive)) target) <
        epsilon) :
    ClassificationProcess distribution (withinBoundEvent target value) where
  State := process.State
  status state item := withinBoundStatus (process.ranges state item) target
  initial := process.initial
  request := process.request
  sound state := distribution.withinBoundClassification_sound
    (process.ranges state) target value (admitted state)
  request_refines state epsilon positive atom member :=
    withinBoundStatus_refines
      (process.request_refines state epsilon positive atom member)
  accurate := unresolvedAccurate
  refinesInitial state atom member :=
    withinBoundStatus_refines (process.refinesInitial state atom member)

end PointwiseEnclosureProcess

end Purelib.Measure

end
