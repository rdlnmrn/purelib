module
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Step
import Purelib.Data.CCL.Transducer.Mode.Basic

public import Purelib.Data.CCL.Transducer.Emission.Grammar.Basic
import Purelib.Data.CCL.Transducer.Emission.Grammar.Step
import Purelib.Data.CCL.Transducer.Machine.Committed
public import Purelib.Data.CCL.Transducer.Machine.Grammar.Basic
import Purelib.Data.CCL.Transducer.Mode.Grammar
import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.List.Basic
import Purelib.Data.List.Append

-- Retain the established Machine.initial_advance_invariant theorem name.

/-!
# Preservation of committed-word grammar

The syntax phase of the committed Boolean word agrees with the retained mode.
Each bit transition and finite advance preserves that exact grammar invariant.
-/

public section

namespace Purelib.Data.CCL.Transducer.Machine.Grammar

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
open Purelib.Data.List

namespace Step

/-- Consuming an emission with its certified phase transition preserves committed-word grammar.

The same emitted prefix is extended by the emission's retained Boolean chunk. Parser concatenation and the exact stored
next mode identify its final phase. -/
theorem consumeEmission_invariant (mode : Mode) (emitted : List Bool)
    (emission : Emission)
    (before : (Parser.State.parse emitted).phase =
      Mode.Grammar.modeRawPhase mode)
    (follows : Emission.Grammar.Basic.EmissionFollows mode emission) :
    Invariant (Machine.Step.consumeEmission emitted emission).2 := by
  unfold Invariant
  rw [Machine.Committed.consumeEmission_committed,
    Parser.State.parse_append_phase, before,
    Machine.Committed.consumeEmission_mode]
  exact follows

/-- Returning one machine bit preserves its exact committed-word grammar invariant.

A queued bit only changes the division between emitted and pending words. With an empty queue, the certified emission's
phase transition supplies the invariant for the newly committed chunk. -/
theorem nextBit_invariant (machine : Machine)
    (invariant : Invariant machine) :
    Invariant (Machine.Step.nextBit machine).2 := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | nil =>
          apply consumeEmission_invariant mode emitted (Emission.Step.step mode)
          · change (Parser.State.parse (emitted ++ [])).phase =
                Mode.Grammar.modeRawPhase mode at invariant
            rw [Append.append_nil] at invariant
            exact invariant
          · exact Emission.Grammar.Step.step_follows mode
      | cons bit rest =>
          change (Parser.State.parse ((emitted ++ [bit]) ++ rest)).phase =
            Mode.Grammar.modeRawPhase mode
          rw [Append.append_assoc]
          exact invariant

/-- Every finite advance preserves the retained machine's committed-word grammar invariant.

Induction follows the specified number of bit transitions. Each successor carries the invariant of the same returned
machine into the remaining advance. -/
theorem advance_invariant (machine : Machine)
    (invariant : Invariant machine) : ∀ count : Nat,
    Invariant (Machine.Advance.advance machine count)
  | 0 => invariant
  | count + 1 =>
      advance_invariant (Machine.Step.nextBit machine).2
        (nextBit_invariant machine invariant) count

end Step
/-- Every finite advance from an initial process state satisfies committed-word grammar.

The original dependent process state selects the initial machine. Its empty committed word establishes the invariant
carried by all subsequent finite bit transitions. -/
theorem initial_advance_invariant
    (process : Approximation.Gaussian.Process)
    (state : process.State) (count : Nat) :
    Invariant
      (Machine.Advance.advance (initial process state) count) :=
  Step.advance_invariant _ (initial_invariant process state) count
end Purelib.Data.CCL.Transducer.Machine.Grammar
