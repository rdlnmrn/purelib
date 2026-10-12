module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Basic
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

namespace Purelib.Measure

/-! ## Lifting pointwise finite requests through expectation -/

open Purelib in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain requested rational interval enclosures over the exact occurrences of one finite distribution.

Each state supplies payload intervals. Positive requests refine the old intervals and bound their widths on the same
retained atoms; every state's intervals also refine the original initial intervals. -/
structure PointwiseEnclosureProcess {α : Type}
    (distribution : Distribution α) where
  /-- The executable state carrier for these retained pointwise enclosures. -/ State : Type
  /-- The exact rational interval retained for each state and payload. -/ ranges : State → α → Data.Rat.Interval
  /-- The original enclosure state for this fixed distribution. -/ initial : State
  /-- Produce a state for the supplied positive rational width request. -/ request : (state : State) → (epsilon :
    Fraction.Rational) → 0 < epsilon → State
  /-- Every requested interval refines the same payload's old interval on the retained distribution atoms. -/
    request_refines : ∀ state epsilon positive atom,
    atom ∈ distribution.atoms →
      Interval.Refines
        (ranges (request state epsilon positive) atom.item)
        (ranges state atom.item)
  /-- Every requested interval has width at most the positive request on the retained atoms. -/ accurate : ∀ state
    epsilon positive atom,
    atom ∈ distribution.atoms →
      (ranges (request state epsilon positive) atom.item).width ≤ epsilon
  /-- Every state's intervals refine the same original initial intervals on the retained atoms. -/ refinesInitial : ∀
    state atom, atom ∈ distribution.atoms →
    Interval.Refines (ranges state atom.item) (ranges initial atom.item)

constructive_injectivity PointwiseEnclosureProcess

end Purelib.Measure

end
