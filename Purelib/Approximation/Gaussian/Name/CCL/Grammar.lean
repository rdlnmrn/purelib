module
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Advance

public import Purelib.Data.CCL.Transducer.Machine.Grammar.Basic
import Purelib.Data.CCL.Transducer.Machine.Grammar.Step

open Purelib.Approximation

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.CCL.Transducer.Machine.Grammar

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

namespace Purelib.Approximation.Gaussian.Name.CCL.Grammar.Named

namespace Machine
end Machine

/-- Advancing the original arithmetic name by any finite bit request preserves the controller's raw-parser grammar
invariant. -/
theorem machine_advance_invariant (name :
  Gaussian.Name.Basic.Named) (count : Nat) :
    Data.CCL.Transducer.Machine.Grammar.Invariant (Advance.advance name.machine count) :=
  Data.CCL.Transducer.Machine.Grammar.initial_advance_invariant name.process name.state count

end Purelib.Approximation.Gaussian.Name.CCL.Grammar.Named

end
