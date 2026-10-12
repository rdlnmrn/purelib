module
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
public import Purelib.Data.CCL.Transducer.Machine.Step
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.List.Basic
import Purelib.Data.List.Append

-- Retain the established Machine.committed projection name.

/-!
# Committed transducer words

The committed word is the emitted prefix followed by its retained pending queue.
Consuming a nonempty emission retains exactly that word and its selected next mode.
-/

public section

namespace Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.CCL.Transducer
open Purelib.Data.List

/-- Read the committed word as the emitted prefix followed by its retained pending queue.

Both lists keep their original Boolean order. The projection concatenates them without executing another emission or
changing the retained mode. -/
@[expose] def committed (machine : Machine) : List Bool :=
  machine.emitted ++ machine.pending

namespace Committed

/-- Consuming a certified emission commits the emitted prefix followed by its entire stored chunk.

The nonempty certificate excludes the empty case. The selected head is appended to the prefix and the same remaining
bits form the retained queue. -/
theorem consumeEmission_committed (emitted : List Bool)
    (emission : Emission) :
    committed (Machine.Step.consumeEmission emitted emission).2 =
      emitted ++ emission.bits := by
  cases emission with
  | mk bits nonempty next =>
      cases bits with
      | nil => exact (nonempty rfl).elim
      | cons bit rest =>
          change (emitted ++ [bit]) ++ rest = emitted ++ (bit :: rest)
          exact Append.append_assoc emitted [bit] rest

/-- Consuming a certified emission retains exactly its stored next mode. -/
theorem consumeEmission_mode (emitted : List Bool) (emission : Emission) :
    (Machine.Step.consumeEmission emitted emission).2.mode = emission.next := by
  cases emission with
  | mk bits nonempty next =>
      cases bits with
      | nil => exact (nonempty rfl).elim
      | cons bit rest => rfl

end Committed
end Purelib.Data.CCL.Transducer.Machine
