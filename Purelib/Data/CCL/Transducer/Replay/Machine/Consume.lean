module
import Purelib.Data.CCL.Transducer.Replay.Emission
public import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
public import Purelib.Data.CCL.Transducer.Replay.Failure

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

namespace Purelib.Data.CCL.Transducer.Replay.Machine.Consume

open Purelib.Data.CCL.Transducer
/-- Consume the first bit of the exact replay emission and retain its next mode and remaining queue.

Append that bit to the supplied emitted prefix. An empty chunk returns a failure containing that same prefix and
emission with its exact emptiness proof. -/
def consume (emitted : List Bool) (emission :
  Data.CCL.Transducer.Replay.Emission) : Except Data.CCL.Transducer.Replay.Failure Data.CCL.Transducer.Replay.Machine :=
  match bits : emission.bits with
  | [] => .error (.emptyEmission emitted emission bits)
  | bit :: rest => .ok ⟨emission.next, emitted ++ [bit], rest⟩

/-- Failed replay consumption retains the exact empty emission, supplied prefix and proof that its chunk is empty. -/
theorem consume_error {emitted : List Bool} {emission :
  Data.CCL.Transducer.Replay.Emission} {error : Data.CCL.Transducer.Replay.Failure}
    (failure : consume emitted emission = .error error) :
    ∃ empty : emission.bits = [], error = .emptyEmission emitted emission empty := by
  unfold consume at failure
  split at failure
  · rename_i empty
    cases failure
    exact ⟨empty, rfl⟩
  · cases failure
end Purelib.Data.CCL.Transducer.Replay.Machine.Consume

end
