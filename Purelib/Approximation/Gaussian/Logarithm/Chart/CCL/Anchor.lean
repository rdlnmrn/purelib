module
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchor.Unit
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchor

open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Exact finite seeds for anchored logarithm transport

The retryable logarithm layer needs at least one completely explicit source
anchor.  The exact rational input `1` uses the existing unit complex-log chart,
the exact-zero correction, and the proved operational identity `exp 0 = 1`.
This is local finite branch data, not a global logarithm convention.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.CCL.Anchor

/-- The exact seed is immediately an ordinary productive logarithm output. -/
theorem exactOneAnchor_productive (count : Nat) :
    (Named.machine (AnchoredChart.output Unit.exactOneAnchor).name).emitted.IsPrefix
        (Advance.advance
          (Named.machine (AnchoredChart.output Unit.exactOneAnchor).name) count).emitted ∧
      (Advance.advance
        (Named.machine (AnchoredChart.output Unit.exactOneAnchor).name) count).emitted.length = count :=
  Named.productive (AnchoredChart.output Unit.exactOneAnchor).name count

end Purelib.Approximation.Gaussian.Logarithm.Chart.CCL.Anchor

end
