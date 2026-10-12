module
import Purelib.Data.CCL.Transducer.Machine.Basic
public import Purelib.Data.CCL.Transducer.Machine.Step
import Purelib.Data.List.Append
import Purelib.Data.Nat.Addition

/-!
# Finite advances of the retained CCL bit machine

Each successor consumes the original next-bit result, retaining its exact
mode, emitted prefix and pending queue. The quantitative and prefix laws
refer to that same machine sequence and requested finite count.
-/

namespace Purelib.Data.CCL.Transducer.Machine.Advance

open Purelib.Data.List

open Purelib.Data.CCL.Transducer
/-- Advance the exact machine by the requested finite number of returned bits.

Each successor uses the retained nextBit result as the next machine, preserving its mode, emitted prefix and pending
queue. A zero request returns the original machine unchanged. -/
@[expose] public def advance : Machine → Nat → Machine
  | machine, 0 => machine
  | machine, count + 1 => Purelib.Data.CCL.Transducer.Machine.Advance.advance (Machine.Step.nextBit machine).2 count

/-- Advancing by the requested count increases the retained emitted length by exactly that count.

Each retained next-bit step adds one emitted entry. Recursion on the
supplied finite count adds those exact steps to the original prefix length. -/
public theorem advance_length (machine : Machine) : ∀ count : Nat,
    (Machine.Advance.advance machine count).emitted.length = machine.emitted.length + count
  | 0 => (Nat.add_zero machine.emitted.length).symm
  | count + 1 => by
      rw [Machine.Advance.advance, Purelib.Data.CCL.Transducer.Machine.Advance.advance_length (Machine.Step.nextBit
        machine).2 count,
        Machine.Step.nextBit_length]
      exact Nat.succ_add machine.emitted.length count

/-- Advancing the machine preserves its original emitted word as a prefix.

A zero request retains the original word. A successor prefixes the
returned bit to the recursive suffix witness, keeping its order and
certifying the same advanced emitted word directly. -/
public theorem advance_extends (machine : Machine) : ∀ count : Nat,
    machine.emitted.IsPrefix (Machine.Advance.advance machine count).emitted
  | 0 => ⟨[], Append.append_nil machine.emitted⟩
  | count + 1 => by
      obtain ⟨suffix, suffixEqual⟩ :=
        Purelib.Data.CCL.Transducer.Machine.Advance.advance_extends
          (Machine.Step.nextBit machine).2 count
      refine ⟨[(Machine.Step.nextBit machine).1] ++ suffix, ?_⟩
      change machine.emitted ++ ([(Machine.Step.nextBit machine).1] ++ suffix) =
        (Machine.Advance.advance (Machine.Step.nextBit machine).2 count).emitted
      rw [← Append.append_assoc, ← Machine.Step.nextBit_emitted]
      exact suffixEqual

/-- A finite advance extends the retained emitted prefix by exactly the requested number of bits.

The original count controls both the retained-prefix witness and the
exact increase in emitted length; no alternative machine sequence is
used for the two claims. -/
public theorem productive (machine : Machine) (count : Nat) :
    machine.emitted.IsPrefix (Machine.Advance.advance machine count).emitted ∧
      (Machine.Advance.advance machine count).emitted.length =
        machine.emitted.length + count :=
  ⟨Machine.Advance.advance_extends machine count, Machine.Advance.advance_length machine count⟩

/-- Two successive finite advances equal one advance by the sum of their counts.

The first request advances the original machine before the second request
uses that exact retained result. Induction compares this same sequence
with the single request for the sum of both finite counts. -/
public theorem advance_add (machine : Machine) (first second : Nat) :
    Machine.Advance.advance
        (Machine.Advance.advance machine first) second =
      Machine.Advance.advance machine (first + second) := by
  induction first generalizing machine with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first inductionHypothesis =>
      rw [Nat.succ_add, Machine.Advance.advance, Machine.Advance.advance]
      exact inductionHypothesis (Machine.Step.nextBit machine).2

end Purelib.Data.CCL.Transducer.Machine.Advance
