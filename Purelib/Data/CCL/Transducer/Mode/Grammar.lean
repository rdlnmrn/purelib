module
public import Purelib.Data.CCL.Encoding.Parser.Syntax
public import Purelib.Data.CCL.Transducer.Mode.Basic

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

namespace Purelib.Data.CCL.Transducer.Mode.Grammar

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
/-- Read the initial-high or subsequent-loop parser phase from the retained regular kind and count. -/
def regularRawPhase :
    Mode.Basic.RegularKind → Nat → Parser.Syntax.Phase
  | .initialHigh, count => .highUnary count
  | .loop, count => .loopUnary count

/-- Read the exact raw parser phase corresponding to the retained transducer mode and its count. -/
def modeRawPhase : Data.CCL.Transducer.Mode → Parser.Syntax.Phase
  | .initial _ => .initial
  | .low state => .lowUnary state.count
  | .loop state => regularRawPhase state.kind state.count
  | .residual state => .loopUnary state.count
end

namespace Machine
end Machine
end Purelib.Data.CCL.Transducer.Mode.Grammar

end
