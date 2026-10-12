module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
meta import Mathlib.Tactic.Linter.Lint

section

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

set_option genInjectivity false in
/-- A ready branch is exactly the transport through one displayed safe overlap extension. -/
structure Ready
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput)
    (output : Anchored.AnchoredChart (LogarithmState.preparedTarget state)) : Type where
  /-- The safe overlap extension indexed by the original source anchor and exact prepared target state. -/ extension :
    Transport.SafeOverlapExtension sourceInput (LogarithmState.preparedTarget state) source
  /-- The returned branch is exactly the transport through the retained extension. -/ output_eq : output =
    extension.transport source

constructive_injectivity Ready

end Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

end

end
