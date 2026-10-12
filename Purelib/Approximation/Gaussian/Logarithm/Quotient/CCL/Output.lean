module
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Client
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Ready
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation.Gaussian.Logarithm.Quotient

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Data.CCL.Transducer.Machine

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

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient.CCL.Output

/-- A ready expression is an ordinary productive coherent name. -/
theorem ready_productive {client :
    Approximation.Gaussian.Logarithm.Quotient.Client}
  {output : Coherent.CoherentNamed}
    (_ready : Approximation.Gaussian.Logarithm.Quotient.Ready client output) (count : Nat) :
    (Named.machine output.name).emitted.IsPrefix
        (Advance.advance (Named.machine output.name) count).emitted ∧
      (Advance.advance
        (Named.machine output.name) count).emitted.length = count :=
  (Named.productive output.name) count
end Purelib.Approximation.Gaussian.Logarithm.Quotient.CCL.Output

end
