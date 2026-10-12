module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Transducer.Replay.Mode
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor

section
@[expose] public section

/-!
# Finite numerical controller and adaptive replay

All executable state below is finite chart syntax, rational bounds, natural
source indices and bit lists.  In particular, neither a `Process` nor a
source evaluator occurs in a returned state.  Each productive chunk records
its model reads, including the second read after a residual inverse chart
change.  Buffered bits do not perform a model query.

This is the numerical interpreter.  Its connection to the certified
transducer is established separately; successful replay of an invented log
does not certify global coherence of its replies.
-/

namespace Purelib.Data.CCL.Transducer.Replay

open Purelib.Data.CCL.Transducer in
set_option genInjectivity false in
/-- Retain an executable replay mode with its emitted prefix and exact pending bit queue. -/
@[ext] structure Machine where
  /-- The exact current replay mode and retained recipe cursor. -/ mode : Mode
  /-- The ordered prefix of bits already returned by replay. -/ emitted : List Bool
  /-- The exact replay bit queue waiting to be returned. -/ pending : List Bool
deriving DecidableEq

constructive_injectivity Machine

namespace Machine

open Purelib.Data.CCL.Transducer in
/-- Start replay at the supplied source cursor index with empty emitted and pending words. -/
def initial (index : Nat) : Machine
  := ⟨.initial ⟨.source, index⟩, [], []⟩

end Machine
end Purelib.Data.CCL.Transducer.Replay

end
