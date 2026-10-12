module
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Measure.BinaryPrefix.Classified

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Classified.Split

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.BinaryPrefix.Classification.WorkedExamples

open Purelib
open Purelib.Measure
open Purelib.Examples

/-- The empty raw prefix split into one inside child and one outside child. -/
def resolvedRawRoot : List (Classified
  Data.List.BinaryPrefix.CCLMeasureWord) :=
  BinaryPrefix.rawBinaryChildren [] .inside .outside

/-- The resolved first-bit event enclosure refines the unresolved root enclosure. -/
example : Purelib.Data.Rat.Interval.Refines (eventBound
  resolvedRawRoot)
    (eventBound [Purelib.Measure.BinaryPrefix.rawClassified [] .unresolved]) :=
  BinaryPrefix.rawUnresolvedSplit_eventBound_refines
    [] .inside .outside

/-- The displayed resolved event has exact probability one half. -/
example : (eventBound resolvedRawRoot).lower = 1 / 2 ∧
    (eventBound resolvedRawRoot).upper = 1 / 2 := by
  decide

end Purelib.Examples.Measure.BinaryPrefix.Classification.WorkedExamples

end
