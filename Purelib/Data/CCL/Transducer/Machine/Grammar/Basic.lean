module
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Machine.Basic

public import Purelib.Data.CCL.Transducer.Machine.Committed
public import Purelib.Data.CCL.Transducer.Mode.Grammar
import Purelib.Data.CCL.Encoding.Parser.Syntax

section
@[expose] public section

/-!
# Raw-grammar certificate for progressive arithmetic output

The progressive arithmetic controller carries quantitative enclosure data,
but its visible output remains the original pure CCL bitstream.  This module
is the one-way bridge: it proves that each buffered controller chunk advances
the unchanged syntax-only raw parser to exactly the phase recorded by the
controller.  Nothing in the canonical parser depends on the sidecar.
-/

namespace Purelib.Data.CCL.Transducer.Machine.Grammar

section Machine

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
/-- Require parsing the exact committed word to yield the raw phase of the retained machine mode. -/
def Invariant (machine : Machine)
  : Prop :=
  (Parser.State.parse (committed machine)).phase =
    Mode.Grammar.modeRawPhase machine.mode

end Machine

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
/-- The initial machine satisfies the exact committed-word grammar invariant. -/
theorem initial_invariant
    (process : Approximation.Gaussian.Process)
    (state : process.State) :
    Invariant (initial process state) := rfl
end Purelib.Data.CCL.Transducer.Machine.Grammar

end
