module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Data.CCL.Transducer.Mode.Basic
public import Purelib.Data.List.Basic
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Data.CCL.Transducer

open Purelib.Data.CCL.Transducer in
open Purelib.Data.List in
set_option genInjectivity false in
/-- Retain a transducer mode with its emitted prefix and exact pending bit queue.

The mode keeps its original process owner and dependent certificates. The two words distinguish bits already returned
from the retained chunk still awaiting consumption. -/
structure Machine where
  /-- The exact current transducer mode and its retained process-state certificates. -/ mode : Mode
  /-- The ordered prefix of bits already returned by this machine. -/ emitted : Basic.BinaryWord
  /-- The exact retained bit queue waiting to be returned. -/ pending : Basic.BinaryWord

constructive_injectivity Machine

namespace Machine

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
/-- Start the exact initial process state with empty emitted and pending bit words. -/
def initial (process : Approximation.Gaussian.Process) (state :
  process.State) : Machine :=
  { mode := .initial
      { process := process
        state := state }
    emitted := []
    pending := [] }

end Machine
end Purelib.Data.CCL.Transducer

end
