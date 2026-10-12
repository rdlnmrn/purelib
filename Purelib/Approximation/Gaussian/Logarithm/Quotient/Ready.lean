module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Division.Partial.Ready
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Client
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Name.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Logarithm.Quotient

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

section
public section

/-!
# A finite dependency scheduler for `log(1 + z) / z`

This is the first composition client for retryable partial operations.  It
coordinates one fixed anchored-logarithm branch with denominator-only
apartness preparation.  A scheduler tick performs at most one child action,
and a blocked result retains the exact child state and typed requirement.

The client deliberately stays at the coherent-name level.  It neither fills
the removable value at zero nor claims a global logarithm branch.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient

namespace Ready

/-- The ordinary quotient produced after both children are ready. -/
@[expose] def readyName (client : Client)
    (logState : LogarithmState.State client.argument)
    (logOutput : Anchored.AnchoredChart (LogarithmState.preparedTarget logState))
    (denominatorState : Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based client.denominator.name.process
        denominatorState.source)) : Coherent.CoherentNamed :=
  Purelib.Approximation.Gaussian.Division.Partial.Ready.readyName (AnchoredChart.output logOutput) client.denominator
    denominatorState
    evidence

end Ready

set_option genInjectivity false in
/-- Ready expression package. It retains both child certificates, which is what makes schedule-independence provable
without recomputing either child. -/
structure Ready (client : Client) (output :
  Coherent.CoherentNamed) : Type 2 where
  /-- The exact retained state of the logarithm child. -/ logState : LogarithmState.State client.argument
  /-- The cached anchored chart indexed by the retained logarithm state. -/ logOutput : Anchored.AnchoredChart
    (LogarithmState.preparedTarget logState)
  /-- The cached logarithm chart has the original source anchor's readiness certificate. -/ logValid :
    Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
    client.sourceInput client.argument client.source
    logState logOutput
  /-- The exact retained state of the original denominator child. -/ denominatorState :
    Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator
  /-- The denominator process based at the retained state has certified candidate apartness. -/ denominatorEvidence :
    Possible.PossibleApart
    (Gaussian.Process.Based.based client.denominator.name.process
      denominatorState.source)
  /-- The returned output is exactly the quotient constructed from the two retained ready children. -/ output_eq :
    output = Ready.readyName client logState logOutput
    denominatorState denominatorEvidence

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity Ready

end Purelib.Approximation.Gaussian.Logarithm.Quotient

end
