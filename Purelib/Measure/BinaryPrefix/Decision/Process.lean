module
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Decision.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Classified.Process
import Purelib.Measure.Refinement
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
public import Purelib.Measure.BinaryPrefix.Decision.Classification
import Purelib.Measure.BinaryPrefix.Decision.Valuation
import Purelib.Data.List.Prefix.Cursor
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction

section
public section

/-!
# A finite Boolean algebra of raw-prefix decisions

`RawEvent` is a finite binary decision tree.  Its valuation is computed by
finite recursion, assigning half of the current symbolic weight to each raw
bit branch.  It is deliberately not a set of completed bit streams and does
not assert that the CCL decoder preserves this symbolic valuation.
-/

namespace Purelib.Data.List.BinaryPrefix
namespace RawEvent

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
/-- The raw event's exact terminal frontier gives the singleton interval at its computed weight. -/
theorem terminalFrontier_eventBound (event : List.BinaryPrefix.RawEvent)
  :
    Measure.eventBound event.terminalFrontier =
      Interval.exact event.weight := by
  apply Interval.ext
  · exact event.terminalFrontier_lower
  · exact event.terminalFrontier_upper

open Purelib in
open Purelib.Data in
open Purelib.Measure in
/-- Construct a constant event process retaining the raw decision event's exact terminal frontier.

Its unit state and identity requests retain the same fully classified frontier, with zero unresolved weight at every
positive tolerance. -/
@[expose] def toEventProcess (event : List.BinaryPrefix.RawEvent) :
    Measure.EventProcess List.BinaryPrefix.CCLMeasureWord where
  State := Unit
  frontier _ := event.terminalFrontier
  initial := ()
  request state epsilon positive := state
  request_refines state epsilon positive :=
    FrontierRefines.refl _
  accurate state epsilon positive := by
    unfold Measure.Resolves
    rw [event.terminalFrontier_unresolved]
    exact positive
  refinesInitial state := FrontierRefines.refl _

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
/-- The constructed event process's initial bound is the singleton interval at the original raw event's weight. -/
theorem toEventProcess_bound (event : List.BinaryPrefix.RawEvent) :
    Measure.eventBound
        (event.toEventProcess.frontier event.toEventProcess.initial) =
      Interval.exact event.weight :=
  event.terminalFrontier_eventBound

end RawEvent

end Purelib.Data.List.BinaryPrefix

end
