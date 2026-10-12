module
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Safety
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Overlap
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

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

/-- Typed evidence requests at one exact retained target state. The overlap constructor retains the already discovered
automatic safety proof. A complete extension can be supplied directly when family-specific geometry has already
constructed it. -/
inductive Requirement
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput) : Type
  /-- Request a semantic overlap witness while retaining the already checked safety certificate. -/ | overlap
      (certificate : Safety.Certificate source.chart.factor
        (targetInput.name.process.ball state.source) state.nextIndex)
  /-- Request a complete safe overlap extension at the exact retained target state. -/ | completeExtension

namespace Requirement

/-- Anchored-logarithm preflight has no automatic exclusion verdict. Failure of the finite safety test can justify
refinement, but it cannot construct a proof that no logarithm branch exists. -/
inductive Exclusion
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput) : Type

/-- Evidence is indexed by the exact source anchor, target, state, and requirement which requested it. -/
def Evidence
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {state : LogarithmState.State targetInput} :
    Requirement sourceInput targetInput source state → Type
  | .overlap _ => Overlap.OverlapWitness sourceInput (LogarithmState.preparedTarget state)
  | .completeExtension =>
      Transport.SafeOverlapExtension sourceInput (LogarithmState.preparedTarget state) source

end Requirement

end Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

end

section
@[expose] public section

/-!
# A finite dependency scheduler for `log(1 + z) / z`

This is the first composition client for retryable partial operations.  It
coordinates one fixed anchored-logarithm branch with denominator-only
apartness preparation.  A scheduler tick performs at most one child action,
and a blocked result retains the exact child state and typed requirement.

The client deliberately stays at the coherent-name level.  It neither fills
the removable value at zero nor claims a global logarithm branch.
-/

section Purelib.CCL.Progressive.PartialLogQuotient
section Log
end Log

end Purelib.CCL.Progressive.PartialLogQuotient

end
