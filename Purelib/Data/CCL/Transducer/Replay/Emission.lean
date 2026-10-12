module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Transducer.Replay.Mode
import Purelib.Data.Gaussian.Basic

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
/-- Retain an executable replay bit chunk and its exact next replay mode.

The next mode keeps its recipe cursor and phase data. This replay record stores the emitted word directly; certified
emission properties are established separately. -/
@[ext] structure Emission where
  /-- The exact bit chunk emitted by this replay step. -/ bits : List Bool
  /-- The retained next replay mode after the chunk. -/ next : Mode
deriving DecidableEq

constructive_injectivity Emission

end Purelib.Data.CCL.Transducer.Replay

end
