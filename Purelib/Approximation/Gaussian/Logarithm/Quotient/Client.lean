module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Basic
meta import Mathlib.Tactic.Linter.Lint

section

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

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

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient

set_option genInjectivity false in
/-- Static data for the expression `log(1 + z) / z`. The source anchor fixes the intended local logarithm branch; its
eventual overlap with `1 + z` is supplied as typed evidence. -/
structure Client where
  /-- The original coherent denominator channel used in the quotient and its logarithm argument. -/ denominator :
    Coherent.CoherentNamed
  /-- The coherent source input retaining the selected logarithm branch. -/ sourceInput : Coherent.CoherentNamed
  /-- The anchored logarithm chart indexed by that exact source input. -/ source : Anchored.AnchoredChart sourceInput

constructive_injectivity Client

namespace Client

/-- The total child expression `1 + z`. -/
def argument (client : Client) : Coherent.CoherentNamed :=
  CoherentNamed.add
    (Coherence.exact 1) client.denominator

end Client
end Purelib.Approximation.Gaussian.Logarithm.Quotient

end

end
