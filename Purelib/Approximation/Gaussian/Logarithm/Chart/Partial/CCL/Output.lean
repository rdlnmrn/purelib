module
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Retryable finite preflight for one anchored logarithm branch

The source anchor fixes the logarithm branch.  Automatic work refines one
target coherent name until an executable rational chart-safety certificate is
visible.  Generic finite refinement cannot construct semantic overlap between
two unrelated `Possible` predicates, so success of the safety test returns a
typed `blocked` requirement for an overlap witness at the exact prepared target
state.  Supplying that witness resumes directly into the existing
`SafeOverlapExtension.transport` operation.

No output name is exposed before readiness.  Failure of a safety test performs
one certified refinement and never proves that the input is zero or outside a
logarithm domain.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.CCL.Output

/-- Readiness returns an ordinary productive anchored-logarithm name. -/
theorem ready_productive
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {state : LogarithmState.State targetInput}
    {output : Anchored.AnchoredChart (LogarithmState.preparedTarget state)}
    (_ready : Approximation.Gaussian.Logarithm.Chart.Partial.Ready sourceInput targetInput source state output)
    (count : Nat) :
    (Named.machine ((AnchoredChart.output output).name)).emitted.IsPrefix
        (Advance.advance
          (Named.machine ((AnchoredChart.output output).name)) count).emitted ∧
      (Advance.advance
        (Named.machine ((AnchoredChart.output output).name)) count).emitted.length = count :=
  (Named.productive ((AnchoredChart.output output).name)) count

end Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.CCL.Output

end
