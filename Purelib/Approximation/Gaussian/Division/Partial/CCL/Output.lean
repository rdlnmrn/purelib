module
public import Purelib.Approximation.Gaussian.Division.Partial.Ready
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Retryable finite preflight for constructive division

An ordinary progressive division is total only after its denominator carries
uniform whole-ball apartness.  This module searches for that certificate one
explicit finite refinement at a time.  It keeps the existing total `Process`
and productive transducer unchanged: a caller receives an ordinary
`CoherentNamed` only in the `ready` case.

Failure of the current rational separation test is represented solely by a
certified progress step.  It is neither evidence that the denominator is zero
nor evidence that zero lies in the current ball.  Manual resumption accepts an
apartness witness indexed by the exact retained denominator state.
-/

namespace Purelib.Approximation.Gaussian.Division.Partial.CCL.Output

/-- A ready quotient is an ordinary productive name: every finite bit request returns exactly the requested number of
raw bits and preserves its prefix. -/
theorem ready_productive {numerator denominator :
  Coherent.CoherentNamed}
    {state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator} {output : Coherent.CoherentNamed}
    (_ready : Approximation.Gaussian.Division.Partial.Ready numerator denominator state output) (count : Nat) :
    (output.name.machine).emitted.IsPrefix
        (Advance.advance output.name.machine count).emitted ∧
      (Advance.advance output.name.machine count).emitted.length =
        count :=
  output.name.productive count

end Purelib.Approximation.Gaussian.Division.Partial.CCL.Output

end
